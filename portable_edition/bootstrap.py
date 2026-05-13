"""Portable edition bootstrap.

The portable edition intentionally reuses the scanner and web runtime while
forcing a no-auth, no-token, no-monitoring profile at startup.
"""

from __future__ import annotations

import os
from pathlib import Path

from station_edition.light_rid.app import main as station_main
from station_edition.light_rid.runtime import create_runtime_context


def main() -> None:
    os.environ["LIGHT_RID_EDITION"] = "portable"
    package_dir = Path(__file__).resolve().parent.parent / "station_edition" / "light_rid"
    ctx = create_runtime_context(
        package_dir=package_dir,
        entrypoint=Path(__file__).resolve(),
        module_name="portable_edition._assembled",
        package_name="portable_edition",
    )
    station_main(ctx)


if __name__ == "__main__":
    main()
