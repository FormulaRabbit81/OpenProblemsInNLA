#!/usr/bin/env python3
"""Offline consistency checks for preserved PR257 external Lean CI evidence.

This authenticates the downloaded records against one another. It does not run
Lean/NanoDa or establish the mathematical fidelity of the theorem statement.
Optionally verify every byte in an independent checkout with --source-tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

HERE = Path(__file__).resolve().parent
COMMIT = "762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0"
WORKFLOW = "a013555a88a0fc9ec910a09ea833dc9cc338db35"
REPO = "DiarHaidary/Spectral-norms-of-independent-entries-with-regular-moment-growth"
ENTRY = "PALOMAR-2026-09-14-000006"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(name):
    return json.loads((HERE / name).read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-tree", type=Path)
    args = parser.parse_args()
    run, jobs, arts = read("run.json"), read("jobs.json"), read("artifacts.json")
    require(run["id"] == 34852526384 and run["head_sha"] == WORKFLOW,
            "Wrong workflow run/revision")
    require(run["event"] == "workflow_dispatch" and run["run_attempt"] == 1,
            "Wrong dispatch/attempt")
    require(run["status"] == "completed" and run["conclusion"] == "success",
            "Workflow did not succeed")
    require(run["repository"]["full_name"] == "PalomarRegistry/PalomarSubmission",
            "Wrong verification repository")
    required_steps = {
        "Parse and fetch immutable source", "Build pinned Comparator",
        "Build pinned NanoDa kernel", "Build toolchain-matched lean4export",
        "Run Comparator and challenge provenance audit",
        "Fail the run when verification did not pass",
    }
    require(len(jobs["jobs"]) == 1, "Unexpected job count")
    job = jobs["jobs"][0]
    require(job["conclusion"] == "success", "Failed verification job")
    passed = {s["name"] for s in job["steps"] if s["conclusion"] == "success"}
    require(required_steps <= passed, "A required mechanical step did not pass")
    require(len(arts["artifacts"]) == 1, "Unexpected artifact count")
    artifact = arts["artifacts"][0]
    require(artifact["id"] == 10352481140 and not artifact["expired"],
            "Unexpected or already-expired artifact at retrieval")
    require(artifact["digest"] == "sha256:" + digest(HERE / "report.zip"),
            "GitHub artifact digest mismatch")
    require(artifact["workflow_run"]["id"] == run["id"] and
            artifact["workflow_run"]["head_sha"] == WORKFLOW,
            "Artifact belongs to a different run")
    with zipfile.ZipFile(HERE / "report.zip") as z:
        require(z.namelist() == ["mechanical-report.json"], "Unexpected ZIP content")
        require(z.read("mechanical-report.json") == (HERE / "mechanical-report.json").read_bytes(),
                "Extracted report differs from original GitHub ZIP")
    report, entry = read("mechanical-report.json"), read("entry.json")
    require(report["source"]["commit"] == COMMIT and report["source"]["repository"] == REPO,
            "CI checked a different source")
    require(report["status"] == "pass" and report["stage"] == "complete" and
            report["phase"] == "verification" and not report["errors"],
            "Report is not a complete verification pass")
    cmp = report["comparator"]
    require(cmp["theorem_names"] == ["MI32.main_upper"] and cmp["definition_names"] == [],
            "Wrong compared target or replaceable definitions")
    require(set(cmp["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            "Nonstandard axiom allowlist")
    require(cmp["challenge_module"] == "Challenge" and cmp["solution_module"] == "Solution",
            "Wrong Challenge/Solution")
    pins = {
        "comparator_commit": "575674928e239f5bc452aab72d1dd7b0f1326494",
        "nanoda_commit": "68d5ca9db226849b41a6fff59d796ff19d0a8840",
        "lean4export_commit": "15f6055e299ad5b89345e533cc2192f4cc00f659",
        "landrun_commit": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
    }
    for key, pin in pins.items():
        require(report[key] == pin and entry["verification"][key] == pin,
                "Verifier pin mismatch: " + key)
    with zipfile.ZipFile(HERE / "run-logs.zip") as z:
        log = z.read("0_verify.txt").decode()
    for pin in pins.values():
        require(pin in log, "Actual GitHub run log lacks pin " + pin)
    tail = report["comparator_log_tail"]
    for line in ["MI32.main_upper", "Running nanoda kernel on solution",
                 "nanoda kernel accepts the solution", "Lean default kernel accepts the solution",
                 "Your solution is okay!"]:
        require(line in tail, "Missing replay evidence: " + line)
    require(entry["id"] == ENTRY and entry["version"] == 1 and entry["status"] == "registered",
            "Wrong registry entry/version/status")
    require(entry["source"]["commit"] == COMMIT and entry["source"]["repository"] == REPO,
            "Registry source does not match CI source")
    require(entry["verification"]["workflow_commit"] == WORKFLOW and
            entry["verification"]["run_id"] == run["id"] and
            entry["verification"]["workflow_run_attempt"] == 1,
            "Registry verification pointer mismatch")
    require(entry["trust"]["level"] == "high" and
            report["challenge"]["trust_level"] == "high" and
            report["challenge"]["untrusted_sources"] == [],
            "Challenge provenance not high/allowlisted")
    require((HERE / "registry-mechanical-report.json").read_bytes() ==
            (HERE / "mechanical-report.json").read_bytes(), "Registry/GitHub reports differ")
    require(entry["verification"]["mechanical_report_sha256"] == digest(HERE / "mechanical-report.json"),
            "Registry mechanical report hash mismatch")
    require(entry["preservation"]["receipt_sha256"] == digest(HERE / "source-archive.json"),
            "Preservation receipt hash mismatch")
    require(entry["review"]["report"]["sha256"] == digest(HERE / "editorial-review.json"),
            "Editorial report hash mismatch")
    require(entry["review"]["outcome"] == "neutral", "Unexpected editorial conclusion")
    for key in ["challenge", "solution", "comparator", "lakefile", "lake_manifest", "formalization", "license"]:
        item = report[key]
        require(digest(HERE / "source" / item["path"]) == item["sha256"],
                "Source hash mismatch: " + key)
    require(report["lean_toolchain"] == "leanprover/lean4:v4.33.0" and
            (HERE / "source/lean-toolchain").read_text().strip() == report["lean_toolchain"],
            "Lean toolchain mismatch")
    packages = read("source/lake-manifest.json")["packages"]
    recorded = {p["name"]: p["revision"] for p in report["project_dependencies"]}
    require(len(packages) == 9 and len(recorded) == 9 and
            {p["name"]: p["rev"] for p in packages} == recorded,
            "Dependency revision mismatch")
    require(recorded["mathlib"] == "db584cd6d46c92f209a44c0f1c829460d327499d",
            "Wrong mathlib revision")
    receipt = read("source-archive.json")
    require(receipt["id"] == ENTRY and receipt["version"] == 1 and
            receipt["repositories"] == entry["preservation"]["repositories"],
            "Archive receipt and registry differ")
    origin, archived, ref = read("source-commit.json"), read("archive-commit.json"), read("archive-ref.json")
    require(origin["sha"] == archived["sha"] == COMMIT and
            origin["tree"]["sha"] == archived["tree"]["sha"] == "8db1a2a4ad74de0675213099aefbf3fe4a5544ca",
            "Origin/archive commit/tree mismatch")
    require(ref["object"]["type"] == "commit" and ref["object"]["sha"] == COMMIT and
            ref["ref"] == "refs/tags/palomar/" + ENTRY + "-v1/" + COMMIT,
            "Preservation tag mismatch")
    files = read("source-file-hashes.json")
    require(len(files) == 196 and files == read("archive-file-hashes.json"),
            "Recorded original/archive file hashes differ")
    if args.source_tree:
        for name, expected in files.items():
            require(digest(args.source_tree / name) == expected, "Checkout mismatch: " + name)
    print("PASS: GitHub run/artifact, exact target and pins, standard-axiom policy,")
    print("both explicit kernel accepts, registry byte/hash identity, 9 dependencies,")
    print("preservation tag/commit/tree and 196 matching archived source file hashes.")
    if args.source_tree:
        print("PASS: all 196 file payloads in supplied independent source tree.")
    print("Scope: evidence consistency and authenticated external replay; no local kernel rerun.")


if __name__ == "__main__":
    main()
