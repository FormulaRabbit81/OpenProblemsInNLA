#!/usr/bin/env python3
"""Check packaged file hashes without modifying the package (standard library only)."""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest = root / "MANIFEST.sha256"
    try:
        entries = manifest.read_text(encoding="utf-8").splitlines()
        checked = 0
        for line in entries:
            digest, relative = line.split("  ", 1)
            if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
                raise ValueError("Invalid SHA-256 value in manifest")
            path = (root / relative).resolve()
            if not path.is_relative_to(root) or path == manifest:
                raise ValueError(f"Unsafe or self-referential manifest path: {relative}")
            if not path.is_file():
                raise ValueError(f"Missing file: {relative}")
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != digest:
                raise ValueError(f"Hash mismatch: {relative}")
            checked += 1
        if not checked:
            raise ValueError("Empty manifest")
        print(f"PASS: all {checked} packaged file hashes match.")
        return 0
    except (OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
