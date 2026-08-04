# GL-AR750S native edition

This package is built specifically for the GL.iNet GL-AR750S running OpenWrt 19.07 on
`ath79/nand` (`mips_24kc`, big-endian, soft-float, musl). It does not use Python,
Scapy, libpcap, or tcpdump at runtime. Wi-Fi frames are received directly from a
Linux `AF_PACKET` socket and decoded from Radiotap/802.11 in Rust.

## Radio layout

- `radio0` / `phy0` / `wlan0`: keep the 5 GHz AP available for administration.
- `radio1` / `phy1`: temporarily stop the 2.4 GHz AP and create `ridmon` in monitor
  mode on channel 6.

The program does not modify UCI. Stopping the service does not recreate the 2.4 GHz
AP, but `wifi up radio1` or a router reboot restores it from the existing wireless
configuration.

## Install the CI package

Extract the `light-rid-gl-ar750s-*.tar.gz` artifact at `/`, then run:

```sh
chmod 0755 /usr/bin/light-rid-station /etc/init.d/light-rid
/etc/init.d/light-rid enable
/etc/init.d/light-rid start
logread -e light-rid
```

The dashboard and health API listen on port 8000 by default. Capture status is
available in `/api/health`, `/api/diagnostics/summary`, and
`/api/hardware/status`.

To keep the 2.4 GHz AP and capture only its current channel, launch the binary with
`--keep-radio-ap`. To use a monitor interface prepared externally, also add
`--skip-monitor-setup`.
