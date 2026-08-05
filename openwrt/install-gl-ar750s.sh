#!/bin/sh

# Public bootstrap installer for the dedicated GL-AR750S edition.
# Usage:
#   curl -fsSL https://cdn.jsdelivr.net/gh/luyii-code-1/Light_RID_Scanner@GL-AR750S-edition/openwrt/install-gl-ar750s.sh | sh

set -eu

REPOSITORY="luyii-code-1/Light_RID_Scanner"
RELEASE_TAG="${LIGHT_RID_RELEASE_TAG:-gl-ar750s-latest}"
ASSET="light-rid-gl-ar750s.tar.gz"
MIRROR_DOWNLOAD_BASE="https://cdn.jsdelivr.net/gh/$REPOSITORY@gl-ar750s-download"
RAW_DOWNLOAD_BASE="https://raw.githubusercontent.com/$REPOSITORY/gl-ar750s-download"
RELEASE_DOWNLOAD_BASE="https://github.com/$REPOSITORY/releases/download/$RELEASE_TAG"
WORK_DIR="/tmp/light-rid-bootstrap.$$"

fail() {
    echo "light-rid-bootstrap: $*" >&2
    exit 1
}

cleanup() {
    rm -rf "$WORK_DIR"
}

fetch() {
    source_url="$1"
    destination="$2"
    if command -v curl >/dev/null 2>&1; then
        curl -fsSL --retry 3 --connect-timeout 15 -o "$destination" "$source_url"
    elif command -v wget >/dev/null 2>&1; then
        wget -O "$destination" "$source_url"
    else
        fail "curl or wget is required"
    fi
}

download_verified_package() {
    package_base="$1"
    checksum_base="${2:-$package_base}"
    rm -f "$WORK_DIR/$ASSET" "$WORK_DIR/$ASSET.sha256"
    fetch "$package_base/$ASSET" "$WORK_DIR/$ASSET" || return 1
    fetch "$checksum_base/$ASSET.sha256" "$WORK_DIR/$ASSET.sha256" || return 1
    (cd "$WORK_DIR" && sha256sum -c "$ASSET.sha256") || return 1
}

trap cleanup EXIT HUP INT TERM

board="$(cat /tmp/sysinfo/board_name 2>/dev/null || true)"
[ "$board" = "glinet,gl-ar750s-nor-nand" ] || \
    fail "unsupported board '${board:-unknown}'; this installer is only for GL-AR750S NOR/NAND"
grep -q "DISTRIB_ARCH='mips_24kc'" /etc/openwrt_release 2>/dev/null || \
    fail "OpenWrt mips_24kc userspace is required"
command -v sha256sum >/dev/null 2>&1 || fail "sha256sum is required"
command -v tar >/dev/null 2>&1 || fail "tar is required"

if ! command -v python3 >/dev/null 2>&1 || \
   ! python3 -c 'import json, sqlite3, urllib.request' >/dev/null 2>&1; then
    command -v opkg >/dev/null 2>&1 || fail "python3 is incomplete and opkg is unavailable"
    echo "light-rid-bootstrap: installing the OpenWrt Python runtime"
    opkg update || fail "opkg update failed; check WAN and package feeds"
    opkg install python3 || fail "cannot install the OpenWrt python3 package"
fi

factory_ssid="${LIGHT_RID_FACTORY_SSID:-}"
factory_password="${LIGHT_RID_FACTORY_WIFI_PASSWORD:-}"
if { [ -n "$factory_ssid" ] && [ -z "$factory_password" ]; } || \
   { [ -z "$factory_ssid" ] && [ -n "$factory_password" ]; }; then
    fail "LIGHT_RID_FACTORY_SSID and LIGHT_RID_FACTORY_WIFI_PASSWORD must be supplied together"
fi

mkdir -m 0700 "$WORK_DIR" || fail "cannot create temporary directory"
echo "light-rid-bootstrap: downloading $RELEASE_TAG for GL-AR750S"
if [ -n "${LIGHT_RID_DOWNLOAD_BASE:-}" ]; then
    download_verified_package "$LIGHT_RID_DOWNLOAD_BASE" || \
        fail "package download or checksum verification failed"
elif ! download_verified_package "$MIRROR_DOWNLOAD_BASE" "$RAW_DOWNLOAD_BASE"; then
    echo "light-rid-bootstrap: mirror download failed; trying GitHub Raw" >&2
    if ! download_verified_package "$RAW_DOWNLOAD_BASE"; then
        echo "light-rid-bootstrap: Raw download failed; trying GitHub Release" >&2
        download_verified_package "$RELEASE_DOWNLOAD_BASE" || \
            fail "all package download sources failed"
    fi
fi

if command -v light-rid-upgrade >/dev/null 2>&1; then
    light-rid-upgrade "$WORK_DIR/$ASSET" || fail "upgrade failed"
else
    tar -xzf "$WORK_DIR/$ASSET" -C / || fail "package extraction failed"
    light-rid-install || fail "installation failed"
fi

if [ -n "$factory_ssid" ]; then
    LIGHT_RID_FACTORY_SSID="$factory_ssid" \
    LIGHT_RID_FACTORY_WIFI_PASSWORD="$factory_password" \
        light-rid-install --factory-provision || fail "factory WiFi provisioning failed"
fi

unset factory_password LIGHT_RID_FACTORY_WIFI_PASSWORD
light-rid-run check || fail "post-install preflight failed"

ready=0
attempt=0
while [ "$attempt" -lt 24 ]; do
    if light-rid-run status | grep -q '^station=running' && \
       light-rid-run status | grep -q '^monitor=ridmon' && \
       light-rid-run status | grep -q '^web=listen' && \
       light-rid-run status | grep -q '^autostart=enabled'; then
        ready=1
        break
    fi
    attempt=$((attempt + 1))
    sleep 5
done
[ "$ready" -eq 1 ] || fail "service did not become ready within 120 seconds"

light-rid-run status
echo "light-rid-bootstrap: installation complete; open http://$(uci -q get network.lan.ipaddr):4600/"
