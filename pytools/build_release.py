#!/usr/bin/env python3
"""Build and Raspberry Pi sync helper for Light RID Scanner editions."""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import struct
import subprocess
import sys
from datetime import datetime
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
BUILD_INFO_PATH = ROOT / "rid_build_info.json"

EDITION_ENTRYPOINTS = {
    "station": ROOT / "station_edition" / "run.py",
}

EDITION_NAMES = {
    "station": "light_rid_station",
}

TARGET_ALIASES = {
    "x86_64": "x86_64",
    "amd64": "x86_64",
    "x64": "x86_64",

    "x32": "x32",
    "x86": "x32",
    "i386": "x32",
    "i686": "x32",

    "arm64": "arm64",
    "aarch64": "arm64",

    "armv7": "armv7",
    "armv7l": "armv7",
    "armhf": "armv7",
    "arm": "armv7",
}


def run(cmd: list[str], *, env: dict[str, str] | None = None) -> None:
    print("+", " ".join(cmd))
    subprocess.run(cmd, cwd=str(ROOT), env=env, check=True)


def data_arg(src: str, dst: str) -> str:
    sep = ";" if os.name == "nt" else ":"
    return f"{src}{sep}{dst}"


def current_machine() -> str:
    if hasattr(os, "uname"):
        return os.uname().machine.lower()
    return platform.machine().lower()


def default_target() -> str:
    return TARGET_ALIASES.get(current_machine(), "x86_64")


def validate_target_runtime(target: str) -> None:
    """
    PyInstaller normally builds for the current Python runtime architecture.

    For Docker/QEMU jobs, `uname -m` can be misleading depending on binfmt/qemu,
    so for 32-bit targets we mainly validate Python pointer size instead of
    strictly checking machine names.
    """
    bitness = struct.calcsize("P") * 8
    machine = current_machine()

    if target == "x32":
        if bitness != 32:
            raise SystemExit(
                "target x32 requires a 32-bit Python runtime. "
                "Use the CI linux-x32 Docker job with --platform linux/386."
            )

    if target == "armv7":
        if bitness != 32:
            raise SystemExit(
                "target armv7 requires a 32-bit ARMv7/armhf Python runtime. "
                "Use the CI linux-armv7 Docker job with --platform linux/arm/v7, "
                "or build directly on Raspberry Pi OS/Debian armhf."
            )

    if target == "arm64":
        if machine not in {"aarch64", "arm64"}:
            raise SystemExit(
                "target arm64 requires an ARM64/aarch64 runtime. "
                "Use ubuntu-24.04-arm or an ARM64 machine."
            )

def exact_git_tag() -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "describe", "--tags", "--exact-match", "HEAD"],
            text=True,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        value = (proc.stdout or "").strip()
        if proc.returncode == 0 and value:
            return value
    except Exception:
        pass
    return ""


def git_short_head() -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "rev-parse", "--short=7", "HEAD"],
            text=True,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        value = (proc.stdout or "").strip()
        if proc.returncode == 0 and value:
            return value
    except Exception:
        pass
    return "local"


def git_dirty() -> bool:
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "status", "--porcelain"],
            text=True,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        return bool((proc.stdout or "").strip())
    except Exception:
        return False


def read_build_info() -> dict:
    if not BUILD_INFO_PATH.exists():
        return {}
    try:
        data = json.loads(BUILD_INFO_PATH.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def resolve_release_tag(cli_tag: str | None = None) -> str:
    explicit = str(cli_tag or "").strip()
    if explicit:
        return explicit
    for key in ("RELEASE_TAG", "GITHUB_EVENT_RELEASE_TAG_NAME"):
        env_tag = str(os.environ.get(key) or "").strip()
        if env_tag:
            return env_tag
    ref_type = str(os.environ.get("GITHUB_REF_TYPE") or "").strip().lower()
    ref_name = str(os.environ.get("GITHUB_REF_NAME") or "").strip()
    if ref_type == "tag" and ref_name:
        return ref_name
    ref = str(os.environ.get("GITHUB_REF") or "").strip()
    if ref.startswith("refs/tags/"):
        return ref.split("/", 2)[-1].strip()
    return exact_git_tag()

def resolve_build_commit(cli_commit: str | None = None) -> str:
    explicit = str(cli_commit or "").strip()
    if explicit:
        return explicit
    for key in ("BUILD_COMMIT", "GITHUB_SHA"):
        env_commit = str(os.environ.get(key) or "").strip()
        if env_commit:
            return env_commit
    return git_short_head()

def prepare_build_info(*, release_tag: str = "", build_commit: str = "") -> None:
    prev = read_build_info()
    commit = resolve_build_commit(build_commit)
    tag = exact_git_tag()
    release_tag_value = str(release_tag or "").strip()
    try:
        prev_build = int(prev.get("build") or 0)
    except Exception:
        prev_build = 0
    prev_release_tag = str(prev.get("release_tag") or "").strip()
    same_commit = str(prev.get("commit") or "").strip() == commit
    same_release_tag = prev_release_tag == release_tag_value
    build = prev_build + 1 if (same_commit and same_release_tag) else 1
    payload = {
        "commit": commit,
        "tag": tag,
        "release_tag": release_tag_value,
        "build": build,
        "generated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "dirty": git_dirty(),
    }
    BUILD_INFO_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(
        f"build version: commit:{commit}#{build} "
        f"source_tag:{tag or '-'} release_tag:{release_tag_value or '-'}"
    )


def build_binary(
    edition: str,
    target: str,
    *,
    clean: bool = True,
    release_tag: str = "",
    build_commit: str = "",
) -> Path:
    validate_target_runtime(target)

    entry = EDITION_ENTRYPOINTS[edition]
    if not entry.exists():
        raise SystemExit(f"missing entrypoint: {entry}")

    dist_dir = ROOT / "release" / edition / target
    work_dir = ROOT / "build" / "pyinstaller" / edition / target

    name = f"{EDITION_NAMES[edition]}-{target}"
    if os.name == "nt":
        name += ".exe"

    if clean:
        shutil.rmtree(dist_dir, ignore_errors=True)
        shutil.rmtree(work_dir, ignore_errors=True)

    dist_dir.mkdir(parents=True, exist_ok=True)
    prepare_build_info(release_tag=release_tag, build_commit=build_commit)

    env = dict(os.environ)
    env["LIGHT_RID_EDITION"] = edition
    env["LIGHT_RID_TARGET"] = target
    if release_tag:
        env["RELEASE_TAG"] = release_tag

    cmd = [
        sys.executable,
        "-m",
        "PyInstaller",
        "--onefile",
        "--clean",
        "--collect-submodules",
        "scapy",
        "--hidden-import",
        "sqlite3",
        "--hidden-import",
        "_sqlite3",
        "--add-data",
        data_arg("station_edition/light_rid", "station_edition/light_rid"),
        "--add-data",
        data_arg(
            "station_edition/light_rid/resources/rid-models.json",
            "station_edition/light_rid/resources",
        ),
        "--add-data",
        data_arg("rid_build_info.json", "."),
        "--distpath",
        str(dist_dir),
        "--workpath",
        str(work_dir),
        "--name",
        name,
        str(entry),
    ]

    run(cmd, env=env)

    artifact = dist_dir / name
    if not artifact.exists():
        raise SystemExit(f"build finished but artifact is missing: {artifact}")

    return artifact


def sync_pi(artifact: Path, *, config: str, restart: bool) -> None:
    args = [
        sys.executable,
        str(ROOT / "tools" / "pi_tools.py"),
        "binary-sync",
        "--config",
        config,
    ]

    if not restart:
        args.append("--no-restart")

    env = dict(os.environ)
    env["LIGHT_RID_PREBUILT_BINARY"] = str(artifact)

    run(args, env=env)


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Build Light RID Scanner edition binaries")
    p.add_argument(
        "--edition",
        choices=sorted(EDITION_ENTRYPOINTS),
        required=True,
    )
    p.add_argument(
        "--target",
        choices=sorted(set(TARGET_ALIASES.values())),
        default=default_target(),
    )
    p.add_argument("--no-clean", action="store_true")
    p.add_argument(
        "--sync-pi",
        action="store_true",
        help="sync the built binary to Raspberry Pi through tools/pi_tools.py",
    )
    p.add_argument("--pi-config", default=str(ROOT / "tools" / "pi.local.json"))
    p.add_argument("--no-restart", action="store_true")
    p.add_argument("--release-tag", default="", help="release tag to embed into rid_build_info.json")
    p.add_argument("--build-commit", default="", help="commit id to embed into rid_build_info.json")
    return p.parse_args()


def main() -> int:
    args = parse_args()
    target = TARGET_ALIASES.get(args.target, args.target)
    release_tag = resolve_release_tag(args.release_tag)
    build_commit = resolve_build_commit(args.build_commit)

    artifact = build_binary(
        args.edition,
        target,
        clean=not args.no_clean,
        release_tag=release_tag,
        build_commit=build_commit,
    )
    print(f"artifact: {artifact}")

    if args.sync_pi:
        sync_pi(artifact, config=args.pi_config, restart=not args.no_restart)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
