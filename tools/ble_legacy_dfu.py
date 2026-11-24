#!/usr/bin/env python3
"""Nordic Legacy DFU (SDK 11) over Bluetooth LE from Linux.

A test client for this bootloader's BLE OTA path: it sends an application DFU
zip the way a phone would, and can break a transfer on purpose to check that
the bootloader recovers.

    scan                       list radios and bootloaders in range
    info   --zip FILE          check a DFU zip without touching a radio
    pair   ADDRESS             bond with the application (passkey entry)
    enter  ADDRESS             ask the application to reboot into BLE OTA DFU
    flash  --zip FILE          send the zip to a radio already in BLE OTA DFU
    update ADDRESS --zip FILE  enter + flash

Needs BlueZ and the `bleak` package:

    nix-shell -p python3 python3Packages.bleak --run \\
        "python3 tools/ble_legacy_dfu.py scan"

The bootloader is single-bank: it erases the installed application when it
accepts START, before any data arrives. `flash` and `update` therefore refuse
to run without --confirm-erase. Keep a USB cable and the firmware .uf2 at hand.

Protocol, as implemented by lib/sdk11 in this repo (ble_dfu.c,
dfu_transport_ble.c). Control Point writes are with response, Packet writes
are without, and replies are Control Point notifications `10 <op> <status>`:

    01 04                  START, image type 4 = application
    <sd><bl><app> u32le    image sizes, on the Packet characteristic
                           -> 10 01 01 once the application area is erased
    02 00, <.dat>, 02 01   init packet -> 10 02 01
    08 <n u16le>           ask for a receipt every n packets (PRN)
    03                     RECEIVE, then the .bin on the Packet characteristic
                           -> 11 <bytes u32le> every n packets
                           -> 10 03 01 after the last byte is in flash
    04                     VALIDATE -> 10 04 01
    05                     ACTIVATE AND RESET, the radio reboots
    06                     RESET, used here only to abort
"""

import argparse
import asyncio
import json
import struct
import sys
import time
import zipfile
from dataclasses import dataclass

from bleak import BleakClient, BleakScanner
from bleak.exc import BleakError

_BASE = "0000{:04x}-1212-efde-1523-785feabcd123"
DFU_SERVICE = _BASE.format(0x1530)
DFU_CONTROL = _BASE.format(0x1531)
DFU_PACKET = _BASE.format(0x1532)
DFU_REVISION = _BASE.format(0x1534)
DIS_FW_REVISION = "00002a26-0000-1000-8000-00805f9b34fb"

OP_START, OP_INIT, OP_RECEIVE, OP_VALIDATE, OP_ACTIVATE, OP_RESET, OP_PRN = 1, 2, 3, 4, 5, 6, 8
OP_RESPONSE, OP_RECEIPT = 0x10, 0x11
IMAGE_APPLICATION = 0x04

# The application's buttonless service reports revision 1, the bootloader 8.
REVISION_APPLICATION = 0x0001

STATUS = {
    1: "SUCCESS",
    2: "INVALID_STATE",
    3: "NOT_SUPPORTED",
    4: "DATA_SIZE_EXCEEDS_LIMIT",
    5: "CRC_ERROR",
    6: "OPERATION_FAILED",
}

# START is answered only after the application area is erased, which the
# SoftDevice interleaves with the radio. The Meshtastic Android client allows 90 s.
T_START, T_INIT, T_RECEIPT, T_RECEIVE, T_VALIDATE = 90, 30, 30, 60, 60
SUBSCRIBE_SETTLE = 0.5

_t0 = time.monotonic()


def log(msg):
    print(f"[{time.monotonic() - _t0:7.2f}] {msg}", flush=True)


class DfuError(Exception):
    pass


class Aborted(Exception):
    """A deliberate --abort-after stop."""


# --------------------------------------------------------------------------
# DFU zip
# --------------------------------------------------------------------------

def crc16(data, crc=0xFFFF):
    """CRC-16/CCITT-FALSE, as nrfutil writes into the init packet."""
    for b in data:
        crc = ((crc >> 8) & 0xFF) | ((crc << 8) & 0xFFFF)
        crc ^= b
        crc ^= (crc & 0xFF) >> 4
        crc ^= (crc << 12) & 0xFFFF
        crc ^= ((crc & 0xFF) << 5) & 0xFFFF
    return crc


@dataclass
class Package:
    init: bytes
    image: bytes
    summary: str


def load_package(path):
    with zipfile.ZipFile(path) as z:
        manifest = json.loads(z.read("manifest.json"))["manifest"]
        others = [k for k in manifest if k in ("bootloader", "softdevice", "softdevice_bootloader")]
        if others or "application" not in manifest:
            # Sending a bootloader or SoftDevice over the air is the one update
            # that can leave a radio needing a debug probe. Not from this tool.
            raise DfuError(f"{path}: only application-only packages are accepted (found {sorted(manifest)})")
        app = manifest["application"]
        init = z.read(app["dat_file"])
        image = z.read(app["bin_file"])

    if len(image) % 4:
        raise DfuError(f"image is {len(image)} bytes, not a multiple of 4")
    if not 14 <= len(init) <= 256:
        raise DfuError(f"init packet is {len(init)} bytes, not a Legacy DFU init packet")

    device_type, device_rev, app_version, sd_count = struct.unpack_from("<HHIH", init)
    sd_req = struct.unpack_from(f"<{sd_count}H", init, 10)
    (init_crc,) = struct.unpack_from("<H", init, 10 + 2 * sd_count)
    image_crc = crc16(image)
    if len(init) == 12 + 2 * sd_count and init_crc != image_crc:
        raise DfuError(f"image CRC16 {image_crc:#06x} does not match the init packet's {init_crc:#06x}")

    summary = (
        f"image {len(image)} B, CRC16 {image_crc:#06x}; init {len(init)} B: "
        f"device type {device_type:#06x}, rev {device_rev:#06x}, app version {app_version:#010x}, "
        f"SoftDevice req {[hex(s) for s in sd_req]}"
    )
    return Package(init=init, image=image, summary=summary)


# --------------------------------------------------------------------------
# Finding radios
# --------------------------------------------------------------------------

def address_plus_one(address):
    """The bootloader advertises at the application's address with the least
    significant byte incremented, no carry (dfu_transport_ble.c)."""
    octets = address.split(":")
    octets[-1] = f"{(int(octets[-1], 16) + 1) & 0xFF:02X}"
    return ":".join(octets)


def _name(device, adv):
    return adv.local_name or device.name or ""


async def find_bootloader(app_address, dfu_name, timeout):
    """The bootloader: at the application's address + 1 with the DFU service or
    the DFU name, or at the application's own address under the DFU name.

    At the application's own address the service list proves nothing, because
    BlueZ adds the services it has already resolved for a paired device, and
    the application has a DFU service too."""
    same = app_address.upper() if app_address else None
    plus_one = address_plus_one(same) if same else None

    def match(device, adv):
        address = device.address.upper()
        named = _name(device, adv) == dfu_name
        if address == plus_one:
            return named or DFU_SERVICE in [u.lower() for u in adv.service_uuids]
        if address == same:
            return named
        # No address to go by: the name alone has to do.
        return same is None and named

    return await BleakScanner.find_device_by_filter(match, timeout=timeout)


async def find_address(address, timeout):
    return await BleakScanner.find_device_by_address(address, timeout=timeout)


async def read_revision(client):
    try:
        raw = await client.read_gatt_char(DFU_REVISION)
        return struct.unpack("<H", bytes(raw[:2]))[0]
    except (BleakError, struct.error):
        return None


# --------------------------------------------------------------------------
# Session with the bootloader
# --------------------------------------------------------------------------

class LegacyDfu:
    def __init__(self, client):
        self.client = client
        self.notifications = asyncio.Queue()

    async def subscribe(self):
        # The Control Point rejects writes until its CCCD is set.
        await self.client.start_notify(DFU_CONTROL, lambda _c, data: self.notifications.put_nowait(bytes(data)))
        await asyncio.sleep(SUBSCRIBE_SETTLE)

    async def control(self, *data):
        await self.client.write_gatt_char(DFU_CONTROL, bytes(data), response=True)

    async def packet(self, data):
        await self.client.write_gatt_char(DFU_PACKET, data, response=False)

    async def _next(self, timeout, what):
        if not self.client.is_connected:
            raise DfuError(f"link lost while waiting for {what}")
        try:
            return await asyncio.wait_for(self.notifications.get(), timeout)
        except asyncio.TimeoutError:
            raise DfuError(f"no reply to {what} within {timeout} s") from None

    async def response(self, op, timeout, what):
        """Wait for `10 <op> <status>`, skipping receipts still in flight."""
        while True:
            n = await self._next(timeout, what)
            if len(n) >= 3 and n[0] == OP_RESPONSE and n[1] == op:
                if n[2] != 1:
                    raise DfuError(f"{what} refused: {STATUS.get(n[2], hex(n[2]))}")
                return
            if n and n[0] == OP_RESPONSE:
                raise DfuError(f"unexpected response {n.hex()} while waiting for {what}")

    async def receipt(self, expected):
        while True:
            n = await self._next(T_RECEIPT, "packet receipt")
            if len(n) >= 5 and n[0] == OP_RECEIPT:
                (received,) = struct.unpack_from("<I", n, 1)
                if received != expected:
                    raise DfuError(f"bootloader has {received} bytes, {expected} were sent")
                return
            if len(n) >= 3 and n[0] == OP_RESPONSE and n[2] != 1:
                raise DfuError(f"transfer refused: {STATUS.get(n[2], hex(n[2]))} ({n.hex()})")

    async def transfer(self, pkg, prn, packet_size, abort_after, abort_mode):
        image = pkg.image

        log("START: the bootloader now erases the installed application")
        await self.control(OP_START, IMAGE_APPLICATION)
        await self.packet(struct.pack("<III", 0, 0, len(image)))
        await self.response(OP_START, T_START, "START")
        log("START accepted")

        await self.control(OP_INIT, 0)
        for i in range(0, len(pkg.init), 20):
            await self.packet(pkg.init[i:i + 20])
        await self.control(OP_INIT, 1)
        await self.response(OP_INIT, T_INIT, "INIT")
        log("init packet accepted")

        if prn:
            await self.control(OP_PRN, *struct.pack("<H", prn))
        await self.control(OP_RECEIVE)

        sent = 0
        packets = 0
        started = time.monotonic()
        next_report = 0.05
        while sent < len(image):
            chunk = image[sent:sent + packet_size]
            await self.packet(chunk)
            sent += len(chunk)
            packets += 1

            if abort_after is not None and sent >= abort_after:
                log(f"--abort-after: stopping at {sent} of {len(image)} bytes ({abort_mode})")
                if abort_mode == "reset":
                    try:
                        await asyncio.wait_for(self.control(OP_RESET), 2)
                    except (BleakError, asyncio.TimeoutError):
                        pass
                raise Aborted()

            if prn and packets % prn == 0 and sent < len(image):
                await self.receipt(sent)

            if sent / len(image) >= next_report:
                rate = sent / max(time.monotonic() - started, 1e-3)
                log(f"  {100 * sent // len(image):3d}%  {sent}/{len(image)} B  {rate / 1000:.1f} kB/s")
                next_report += 0.05

        await self.response(OP_RECEIVE, T_RECEIVE, "end of image")
        log(f"image received by the bootloader in {time.monotonic() - started:.0f} s")

        await self.control(OP_VALIDATE)
        await self.response(OP_VALIDATE, T_VALIDATE, "VALIDATE")
        log("image validated")

        try:
            await asyncio.wait_for(self.control(OP_ACTIVATE), 5)
        except (BleakError, asyncio.TimeoutError):
            pass  # the radio resets before the write is acknowledged
        log("ACTIVATE sent, the radio reboots into the new application")


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------

async def cmd_scan(args):
    log(f"scanning for {args.timeout} s")
    found = await BleakScanner.discover(timeout=args.timeout, return_adv=True)
    rows = []
    for device, adv in found.values():
        name = _name(device, adv)
        dfu = DFU_SERVICE in [u.lower() for u in adv.service_uuids]
        if dfu or name.endswith("_DFU") or name.lower().startswith(("meshcore", "meshtastic")):
            # For a paired device BlueZ reports resolved services here too, so
            # this does not tell an application from a bootloader.
            rows.append((adv.rssi, device.address, name, "has DFU service" if dfu else ""))
    for rssi, address, name, note in sorted(rows, reverse=True):
        print(f"  {address}  {rssi:4d} dBm  {name:24s} {note}")
    if not rows:
        print("  nothing that looks like a radio or a bootloader")


async def cmd_info(args):
    pkg = load_package(args.zip)
    print(pkg.summary)


async def cmd_pair(args):
    """Bond with the application. MeshCore protects its DFU service with an
    authenticated bond, and BlueZ asks an agent for the passkey, so this
    registers one on its own bus connection for the length of the call."""
    from dbus_fast import BusType
    from dbus_fast.aio import MessageBus
    from dbus_fast.service import ServiceInterface, method

    passkey = args.passkey

    class Agent(ServiceInterface):
        def __init__(self):
            super().__init__("org.bluez.Agent1")

        @method()
        def Release(self):
            pass

        @method()
        def RequestPasskey(self, device: "o") -> "u":
            log("BlueZ asked for the passkey")
            return int(passkey)

        @method()
        def RequestPinCode(self, device: "o") -> "s":
            return passkey

        @method()
        def DisplayPasskey(self, device: "o", passkey: "u", entered: "q"):
            pass

        @method()
        def RequestConfirmation(self, device: "o", passkey: "u"):
            pass

        @method()
        def RequestAuthorization(self, device: "o"):
            pass

        @method()
        def AuthorizeService(self, device: "o", uuid: "s"):
            pass

        @method()
        def Cancel(self):
            pass

    device = await find_address(args.address, args.timeout)
    if device is None:
        raise DfuError(f"{args.address} is not advertising")
    path = device.details["path"]

    agent_path = "/org/roammesh/dfu_agent"
    bus = await MessageBus(bus_type=BusType.SYSTEM).connect()
    bus.export(agent_path, Agent())
    root = bus.get_proxy_object("org.bluez", "/org/bluez", await bus.introspect("org.bluez", "/org/bluez"))
    manager = root.get_interface("org.bluez.AgentManager1")
    await manager.call_register_agent(agent_path, "KeyboardOnly")
    try:
        obj = bus.get_proxy_object("org.bluez", path, await bus.introspect("org.bluez", path))
        dev = obj.get_interface("org.bluez.Device1")
        if await dev.get_paired():
            log(f"{args.address} is already paired")
        else:
            log(f"pairing with {args.address}")
            await dev.call_pair()
            log("paired")
        await dev.set_trusted(True)
        await dev.call_disconnect()
    finally:
        await manager.call_unregister_agent(agent_path)
        bus.disconnect()


async def enter_dfu(address, timeout):
    """Ask the application to reboot into BLE OTA DFU. Returns False if the
    application was not found (the radio may already be in the bootloader)."""
    device = await find_address(address, timeout)
    if device is None:
        log(f"{address} is not advertising as an application")
        return False

    log(f"connecting to the application at {address}")
    async with BleakClient(device, timeout=20) as client:
        revision = await read_revision(client)
        if revision is not None and revision != REVISION_APPLICATION:
            raise DfuError(f"{address} reports DFU revision {revision:#06x}: that is a bootloader, not an application")
        dfu = LegacyDfu(client)
        try:
            await dfu.subscribe()
        except BleakError as e:
            raise DfuError(f"cannot enable DFU notifications ({e}). Is this machine paired with the radio? Run `pair`.") from e
        log("asking the application to reboot into the bootloader")
        try:
            await asyncio.wait_for(dfu.control(OP_START, IMAGE_APPLICATION), 5)
        except (BleakError, asyncio.TimeoutError, EOFError):
            pass  # it reboots before the write is acknowledged
    return True


async def flash(app_address, pkg, args):
    log(f"looking for the bootloader ({args.dfu_name}" + (f", {app_address} or +1)" if app_address else ")"))
    device = await find_bootloader(app_address, args.dfu_name, args.timeout)
    if device is None:
        raise DfuError("no bootloader found in BLE OTA DFU mode")
    log(f"bootloader at {device.address} ({device.name})")

    async with BleakClient(device, timeout=20) as client:
        revision = await read_revision(client)
        if revision == REVISION_APPLICATION:
            raise DfuError("that device is an application, not a bootloader; use `enter` or `update`")
        try:
            version = bytes(await client.read_gatt_char(DIS_FW_REVISION)).decode(errors="replace")
        except BleakError:
            version = "unknown"
        log(f"bootloader version: {version} (DFU revision {revision})")

        packet_size = args.packet_size
        if packet_size > 20:
            # BlueZ only reports the negotiated MTU once asked.
            acquire = getattr(client._backend, "_acquire_mtu", None)
            if acquire:
                await acquire()
            if packet_size > client.mtu_size - 3:
                raise DfuError(f"--packet-size {packet_size} exceeds the link's {client.mtu_size - 3} bytes")

        dfu = LegacyDfu(client)
        await dfu.subscribe()
        try:
            await dfu.transfer(pkg, args.prn, packet_size, args.abort_after, args.abort_mode)
        except Aborted:
            return False
    return True


async def wait_for_application(address, timeout):
    log(f"waiting for the application to come back at {address}")
    device = await find_address(address, timeout)
    if device is None:
        log("the application did not reappear in time")
        return False
    log(f"application is advertising again as {device.name}")
    return True


async def cmd_enter(args):
    await enter_dfu(args.address, args.timeout)


async def cmd_flash(args):
    pkg = load_package(args.zip)
    log(pkg.summary)
    done = await flash(args.address, pkg, args)
    if done and args.address:
        await wait_for_application(args.address, 60)


async def cmd_update(args):
    pkg = load_package(args.zip)
    log(pkg.summary)
    if await enter_dfu(args.address, args.timeout):
        await asyncio.sleep(3)  # reboot into the bootloader
    done = await flash(args.address, pkg, args)
    if done:
        await wait_for_application(args.address, 60)


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = p.add_subparsers(dest="command", required=True)

    def transfer_options(s):
        s.add_argument("--zip", required=True, help="application DFU zip (adafruit-nrfutil genpkg)")
        s.add_argument("--confirm-erase", action="store_true",
                       help="required: the installed application is erased as the transfer starts")
        s.add_argument("--dfu-name", default="MTX1_DFU", help="the bootloader's advertising name")
        s.add_argument("--prn", type=int, default=10, help="packets per receipt notification, 0 = none")
        s.add_argument("--packet-size", type=int, default=20,
                       help="bytes per packet: a multiple of 4, at most MTU - 3 and 244")
        s.add_argument("--abort-after", type=int, metavar="BYTES",
                       help="fault injection: stop once this many bytes are sent")
        s.add_argument("--abort-mode", choices=("disconnect", "reset"), default="disconnect",
                       help="how --abort-after stops: drop the link, or send RESET first")
        s.add_argument("--timeout", type=float, default=30, help="scan timeout, seconds")

    s = sub.add_parser("scan", help="list radios and bootloaders in range")
    s.add_argument("--timeout", type=float, default=8)
    s.set_defaults(run=cmd_scan)

    s = sub.add_parser("info", help="check a DFU zip")
    s.add_argument("--zip", required=True)
    s.set_defaults(run=cmd_info)

    s = sub.add_parser("pair", help="bond with the application")
    s.add_argument("address")
    s.add_argument("--passkey", default="123456")
    s.add_argument("--timeout", type=float, default=20)
    s.set_defaults(run=cmd_pair)

    s = sub.add_parser("enter", help="ask the application to reboot into BLE OTA DFU")
    s.add_argument("address")
    s.add_argument("--timeout", type=float, default=20)
    s.set_defaults(run=cmd_enter)

    s = sub.add_parser("flash", help="send a zip to a radio already in BLE OTA DFU")
    s.add_argument("--address", help="the application's address, to find the bootloader at it or +1")
    transfer_options(s)
    s.set_defaults(run=cmd_flash)

    s = sub.add_parser("update", help="enter + flash")
    s.add_argument("address", help="the application's address")
    transfer_options(s)
    s.set_defaults(run=cmd_update)

    args = p.parse_args()
    if args.command in ("flash", "update"):
        if not args.confirm_erase:
            p.error("this erases the installed application as soon as the transfer starts; pass --confirm-erase")
        if args.packet_size % 4 or not 4 <= args.packet_size <= 244:
            p.error("--packet-size must be a multiple of 4 between 4 and 244")

    try:
        asyncio.run(args.run(args))
    except (DfuError, BleakError) as e:
        log(f"FAILED: {e}")
        sys.exit(1)
    except KeyboardInterrupt:
        log("interrupted")
        sys.exit(130)


if __name__ == "__main__":
    main()
