# GL-AR750S deployment

This branch targets the GL-AR750S (`ath79`, big-endian `mips_24kc`) only.
The station UI, RID parser, storage, and APIs remain Python. The
`light-rid-capture` helper replaces Scapy packet capture with a Linux
`AF_PACKET` implementation written in Rust.

The router needs OpenWrt's `python3`, `python3-light`, and `python3-sqlite3`
packages. Install or upgrade from the CI tarball, run the production preflight,
then start it manually from SSH:

```sh
tar -xzf light-rid-gl-ar750s-*.tar.gz -C /
light-rid-install
light-rid-run check
light-rid-run
```

On first install, record the one-time `admin_password` printed by
`light-rid-install`. Each router receives a unique random credential; only
scrypt hashes are stored in `config.json`. Normal upgrades preserve the
existing account and do not print or reset credentials.

Upgrades preserve `/etc/light-rid/config.json`, the SQLite history, the OUI
database, and `/etc/light-rid/rid_model.json`. A deliberate reset creates a
timestamped configuration backup before installing the production defaults:

```sh
light-rid-install --factory-reset
```

Factory reset generates and prints a new one-time administrator password.

For later offline upgrades, copy both CI files to the router, stop the manual
scanner session, and use the guarded upgrader instead of extracting over a
running process:

```sh
light-rid-run stop
light-rid-upgrade light-rid-gl-ar750s-*.tar.gz
light-rid-run
```

The upgrader requires the adjacent `.tar.gz.sha256` file and validates the
checksum, archive paths, required executables, and package manifest.

`light-rid-run` stays in the foreground. Press Ctrl+C or close the SSH session
to stop it. It dedicates the 2.4 GHz radio (`radio1`/`phy1`) to monitor mode as
`ridmon` on channel 6 and restores `radio1` when it exits. The 5 GHz access
point remains available. No init script or boot-time service is installed.
Only one scanner instance can run at a time. `light-rid-run status` reports the
device ID, installed build, free RAM/storage, process IDs, monitor channel,
5GHz management AP, and web listener. Every package
contains a SHA-256 manifest checked by `light-rid-install` and
`light-rid-run check`. The mutable model database is protected by the outer
package checksum during installation and then lives in `/etc/light-rid`; it is
intentionally excluded from post-install code integrity checks for compatibility
with older configurations that updated the bundled seed in place.

Stop the current manual session before upgrading. If an SSH connection was
interrupted and left an old process behind, recover without rebooting:

```sh
light-rid-run stop
light-rid-run check
light-rid-run
```
