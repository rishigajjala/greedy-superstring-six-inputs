#!/usr/bin/env python3
"""Verify every SHA-256 entry in MANIFEST.sha256 using the standard library."""

from __future__ import annotations

import hashlib
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "MANIFEST.sha256"


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> int:
    failures: list[str] = []
    checked = 0
    for number, raw in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        expected, separator, relative = line.partition("  ")
        if not separator or len(expected) != 64:
            failures.append(f"line {number}: malformed entry")
            continue
        path = ROOT / relative
        if not path.is_file():
            failures.append(f"{relative}: missing")
            continue
        actual = digest(path)
        checked += 1
        if actual != expected:
            failures.append(f"{relative}: expected {expected}, got {actual}")
    if failures:
        print("manifest verification FAILED", file=sys.stderr)
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"manifest verification OK: {checked} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
