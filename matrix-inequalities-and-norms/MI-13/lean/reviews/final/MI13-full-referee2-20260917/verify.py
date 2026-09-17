#!/usr/bin/env python3
"""Read-only MI-13 referee-packet integrity checks; no Lean or Comparator run."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sources", action="store_true",
        help="also check final53 external source/runtime bindings in the local workspace",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "MANIFEST.json").read_text())
    payloads = manifest["payloads"]
    for relative, expected in payloads.items():
        path = root / relative
        assert not path.is_symlink(), f"symlink is not a retained payload: {relative}"
        assert path.resolve().is_relative_to(root), f"path escapes packet: {relative}"
        assert path.is_file(), f"missing payload: {relative}"
        assert digest(path) == expected, f"payload hash mismatch: {relative}"
    observed = {
        str(path.relative_to(root)) for path in root.rglob("*")
        if path.is_file() and path != root / "MANIFEST.json"
    }
    assert observed == set(payloads), (
        "packet inventory mismatch", sorted(observed - set(payloads)),
        sorted(set(payloads) - observed),
    )

    verdict = json.loads((root / "REVIEW.json").read_text())
    static = json.loads((root / "STATIC-FINAL53.json").read_text())
    runtime = json.loads((root / "RUNTIME-FINAL53.json").read_text())
    sources = json.loads((root / "SOURCE-FINAL53-BINDINGS.json").read_text())
    bindings = json.loads((root / "FINAL-BINDINGS.json").read_text())
    assert verdict["nonauthor"] and not verdict["authored_statement_or_proof_code"]
    assert verdict["source_inputs"] == len(static["files"]) == 22
    assert verdict["frozen_contracts"] == len(static["contracts"]) == 36
    assert len(runtime["measured_axioms"]) == 36
    assert static["successful"] and runtime["all_passed"]
    assert static["check_count"] == verdict["static_checks_passed"] == 421
    assert runtime["check_count"] == verdict["retained_runtime_checks_passed"] == 2539
    assert verdict["root_receipt_sha256"] == runtime["root_receipt_sha256"]
    assert not verdict["fresh_compilation_by_referee"]
    assert not verdict["Comparator_executed"]
    assert not verdict["published_commit_checked"]
    assert verdict["GitHub_run_id"] is None and verdict["count_change"] == 0
    assert set(runtime["excluded_unrelated_modules"]) == {
        "NLA.IE02.Definitions", "NLA.IE02.Coefficients",
    }
    for observed_axioms in runtime["measured_axioms"].values():
        assert set(observed_axioms) == {"propext", "Classical.choice", "Quot.sound"}
    for item in sources["bindings"]:
        assert digest(root / item["snapshot"]) == item["sha256"]
    assert bindings["binding_count"] == len(bindings["bindings"])
    external_count = 0
    if args.sources:
        for source, expected in bindings["bindings"].items():
            path = Path(source)
            assert path.is_absolute() and path.is_file(), f"missing external input: {source}"
            assert digest(path) == expected, f"external hash mismatch: {source}"
            external_count += 1
    print(json.dumps({
        "packet_integrity": "passed",
        "payloads": len(payloads),
        "external_bindings_checked": external_count,
        "fresh_Lean_execution": False,
        "Comparator_execution": False,
        "published_commit_checked": False,
        "count_change": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
