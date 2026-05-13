#!/usr/bin/env python3
"""Build helper for the standalone Light RID node-center viewer."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ENTRYPOINT = ROOT / "viewer" / "server.py"
TARGET_ALIASES = {
    "x86_64": "x86_64",
    "amd64": "x86_64",
    "arm64": "arm64",
    "aarch64": "arm64",
    "windows-x86_64": "windows-x86_64",
    "win-x86_64": "windows-x86_64",
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


def build_binary(target: str, *, clean: bool = True) -> Path:
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
