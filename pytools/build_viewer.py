#!/usr/bin/env python3
"""Build helper for the standalone Light RID node-center viewer."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import struct
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ENTRYPOINT = ROOT / "viewer" / "server.py"
TARGET_ALIASES = {
    "x86_64": "x86_64",
    "amd64": "x86_64",
    "x32": "x32",
    "x86": "x32",
    "i386": "x32",
    "i686": "x32",
    "arm64": "arm64",
    "aarch64": "arm64",
    "windows-x86_64": "windows-x86_64",
    "win-x86_64": "windows-x86_64",
    "windows-x32": "windows-x32",
    "windows-x86": "windows-x32",
    "win-x32": "windows-x32",
    "win-x86": "windows-x32",
}


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd))
    subprocess.run(cmd, cwd=str(ROOT), check=True)


def data_arg(src: str, dst: str) -> str:
    sep = ";" if os.name == "nt" else ":"
    src_path = Path(src)
    if not src_path.is_absolute():
        src_path = ROOT / src_path
    return f"{src_path.resolve()}{sep}{dst}"


def validate_target_runtime(target: str) -> None:
    bitness = struct.calcsize("P") * 8
    if target == "x32" and bitness != 32:
        raise SystemExit(
            "target x32 requires a 32-bit Python runtime; use the CI linux-x32 Docker job or a 32-bit Python"
        )
    if target == "windows-x32" and (os.name != "nt" or bitness != 32):
        raise SystemExit("target windows-x32 requires a 32-bit Python runtime on Windows")


def build_binary(target: str, *, clean: bool = True) -> Path:
    validate_target_runtime(target)
    if not ENTRYPOINT.exists():
        raise SystemExit(f"missing entrypoint: {ENTRYPOINT}")
    dist_dir = ROOT / "release" / "viewer" / target
    work_dir = ROOT / "build" / "pyinstaller" / "viewer" / target
    name = f"light_rid_viewer-{target}"
    if os.name == "nt" and not name.endswith(".exe"):
        name += ".exe"
    if clean:
        shutil.rmtree(dist_dir, ignore_errors=True)
        shutil.rmtree(work_dir, ignore_errors=True)
    dist_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        sys.executable,
        "-m",
        "PyInstaller",
        "--onefile",
        "--clean",
        "--add-data",
        data_arg("station_edition/light_rid/assets", "station_edition/light_rid/assets"),
        "--add-data",
        data_arg("station_edition/light_rid/web_server.py", "station_edition/light_rid"),
        "--add-data",
        data_arg("EULA.md", "."),
        "--distpath",
        str(dist_dir),
        "--specpath",
        str(work_dir),
        "--workpath",
        str(work_dir),
        "--name",
        name,
        str(ENTRYPOINT),
    ]
    run(cmd)
    artifact = dist_dir / name
    if not artifact.exists():
        raise SystemExit(f"build finished but artifact is missing: {artifact}")
    return artifact


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build the Light RID node-center viewer binary")
    parser.add_argument("--target", choices=sorted(set(TARGET_ALIASES.values())), default="x86_64")
    parser.add_argument("--no-clean", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = TARGET_ALIASES.get(args.target, args.target)
    artifact = build_binary(target, clean=not args.no_clean)
    print(f"artifact: {artifact}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
