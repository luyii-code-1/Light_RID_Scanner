# GL-AR750S deployment

This branch targets the GL-AR750S (`ath79`, big-endian `mips_24kc`) only.
The station UI, RID parser, storage, and APIs remain Python. The
`light-rid-capture` helper replaces Scapy packet capture with a Linux
`AF_PACKET` implementation written in Rust.

The router needs OpenWrt's `python3`, `python3-light`, and `python3-sqlite3`
packages. After SSH connects to the router, the normal online install or
upgrade is one command. It downloads the public GL-AR750S package from the
repository's generated Raw download branch (with GitHub Release fallback),
verifies its SHA-256 checksum, preserves existing settings, enables procd, and
waits for the service to start:

```sh
curl -fsSL https://cdn.jsdelivr.net/gh/luyii-code-1/Light_RID_Scanner@GL-AR750S-edition/openwrt/install-gl-ar750s.sh | sh
```

The bootstrap uses jsDelivr first, then falls back to GitHub Raw and GitHub
Release. Every downloaded package is checked against its SHA-256 file before
extraction. If jsDelivr itself is unavailable, the bootstrap can also be read
directly from GitHub Raw:

```sh
curl -fsSL https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/GL-AR750S-edition/openwrt/install-gl-ar750s.sh | sh
```

`wget -qO- URL | sh` is also supported. For production-line provisioning,
environment variables can be supplied to `sh` without placing credentials in
the public repository:

```sh
curl -fsSL https://cdn.jsdelivr.net/gh/luyii-code-1/Light_RID_Scanner@GL-AR750S-edition/openwrt/install-gl-ar750s.sh | \
  LIGHT_RID_FACTORY_SSID='Light-RID' LIGHT_RID_FACTORY_WIFI_PASSWORD='replace-me' sh
```

For an offline production workstation, download the CI tarball, adjacent
checksum, and `deploy-gl-ar750s.ps1`, then run one command from Windows:

```powershell
.\deploy-gl-ar750s.ps1 -Package .\light-rid-gl-ar750s-34b0294.tar.gz `
  -RouterHost 192.168.8.1 -HostKey "SHA256:device-host-key"
```

The script uploads, verifies, installs, enables, starts, and checks the service.
It can also take `-FactorySsid` and `-FactoryWifiPassword` for production-line
provisioning. Use SSH keys/Pageant or pass `-Password`; never commit production
credentials. Without `-HostKey`, PuTTY asks the operator to verify and cache the
device key on first connection.

The equivalent router-side installation is:

```sh
tar -xzf light-rid-gl-ar750s-*.tar.gz -C /
light-rid-install
light-rid-run check
```

The first install stores a read-only baseline of OpenWrt's `network`,
`wireless`, `dhcp`, `firewall`, and `uhttpd` configurations under
`/etc/light-rid/openwrt-original`. The router page can restore this exact
pre-install state. Upgrades never replace that baseline.

For a production-line install with one shared 5 GHz SSID/password, provision
the values interactively so the secret never enters the public repository or
CI artifact:

```sh
light-rid-install --factory-provision
```

For non-interactive provisioning, pass `LIGHT_RID_FACTORY_SSID` and
`LIGHT_RID_FACTORY_WIFI_PASSWORD` in the installer process environment and
unset them immediately afterwards.

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

For later offline upgrades, copy both CI files to the router and use the
guarded upgrader. It stops and restarts the procd service automatically:

```sh
light-rid-upgrade light-rid-gl-ar750s-*.tar.gz
```

The upgrader requires the adjacent `.tar.gz.sha256` file and validates the
checksum, archive paths, required executables, and package manifest.

Installation enables `/etc/init.d/light-rid`. OpenWrt procd starts it at boot,
captures logs, and respawns it after failures. The launcher permanently marks
all radio1 AP definitions disabled in UCI, removes any vendor-created phy1
interfaces, and dedicates the 2.4 GHz radio (`radio1`/`phy1`) to monitor mode as
`ridmon` on channel 6. A runtime watchdog restarts the supervised scanner if a
vendor process changes the monitor interface, channel, or radio ownership. The
5 GHz AP and wired WAN remain available for ordinary router service.
The dedicated `/router` page controls OpenWrt through UCI/ubus and provides a
separate LuCI link. Network changes use a 90-second confirmation window and an
independent rollback process. The 2.4 GHz radio is never exposed as a router
setting because it is reserved for RID capture.
Only one scanner instance can run at a time. `light-rid-run status` reports the
device ID, installed build, free RAM/storage, process IDs, monitor channel,
5GHz management AP, and web listener. Every package
contains a SHA-256 manifest checked by `light-rid-install` and
`light-rid-run check`. The mutable model database is protected by the outer
package checksum during installation and then lives in `/etc/light-rid`; it is
intentionally excluded from post-install code integrity checks for compatibility
with older configurations that updated the bundled seed in place.

Service management and recovery commands are:

```sh
light-rid-run check
/etc/init.d/light-rid restart
light-rid-run status
```
