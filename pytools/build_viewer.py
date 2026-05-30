#!/usr/bin/env python3
"""Build helper for the standalone Light RID node-center viewer."""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import struct
import sys
from datetime import datetime
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ENTRYPOINT = ROOT / "viewer" / "server.py"
BUILD_INFO_PATH = ROOT / "rid_build_info.json"
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


def current_machine() -> str:
    if hasattr(os, "uname"):
        return os.uname().machine.lower()
    return platform.machine().lower()


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


def build_binary(target: str, *, clean: bool = True, release_tag: str = "", build_commit: str = "") -> Path:
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
    prepare_build_info(release_tag=release_tag, build_commit=build_commit)
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
        data_arg("rid_build_info.json", "."),
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
    parser.add_argument("--release-tag", default="", help="release tag to embed into rid_build_info.json")
    parser.add_argument("--build-commit", default="", help="commit id to embed into rid_build_info.json")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    target = TARGET_ALIASES.get(args.target, args.target)
    release_tag = resolve_release_tag(args.release_tag)
    build_commit = resolve_build_commit(args.build_commit)
    artifact = build_binary(target, clean=not args.no_clean, release_tag=release_tag, build_commit=build_commit)
    print(f"artifact: {artifact}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
