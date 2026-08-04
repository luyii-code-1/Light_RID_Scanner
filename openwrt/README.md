# GL-AR750S deployment

This branch targets the GL-AR750S (`ath79`, big-endian `mips_24kc`) only.
The station UI, RID parser, storage, and APIs remain Python. The
`light-rid-capture` helper replaces Scapy packet capture with a Linux
`AF_PACKET` implementation written in Rust.

The router needs OpenWrt's `python3`, `python3-light`, and `python3-sqlite3`
packages. Install the CI tarball at `/`, then start it manually from SSH:

```sh
tar -xzf light-rid-gl-ar750s-*.tar.gz -C /
light-rid-run
```

`light-rid-run` stays in the foreground. Press Ctrl+C or close the SSH session
to stop it. It dedicates the 2.4 GHz radio (`radio1`/`phy1`) to monitor mode as
`ridmon` on channel 6 and restores `radio1` when it exits. The 5 GHz access
point remains available. No init script or boot-time service is installed.
