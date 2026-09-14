#!/usr/bin/env python3
"""Independent read-only PR261 preservation and provenance cross-check.

Uses only Python's standard library and Git object reads. Does not import or
execute submitted code, repository tools, or another reviewer's checker.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

BASE = "27540c8022a33fef171625b7e48a95e33562d535"
SOURCE = "9bf50028bc30e6cdf78e19089befcb9b9bd6c292"
RECORD = "references/holden-ac-2026-09-14/"
SUBMITTED = RECORD + "submitted/"
NOTICE = "## Reviewed research submission — 14 September 2026"
TEX_NOTICE = "\\subsection{Reviewed research submission --- 14 September\n2026}"
FIELDS = ("Difficulty", "Importance", "Rating rationale", "Topic", "Status")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    def git(*parts):
        return subprocess.check_output(["git", "-C", str(args.repo), *parts])

    def blob(ref, path):
        return git("show", ref + ":" + path)

    def tree(ref):
        answer = {}
        for entry in git("ls-tree", "-r", "-z", ref).split(b"\0"):
            if not entry:
                continue
            metadata, path = entry.split(b"\t", 1)
            mode, kind, oid = metadata.decode().split()
            answer[path.decode()] = {"mode": mode, "type": kind, "oid": oid}
        return answer

    require(git("rev-parse", BASE).decode().strip() == BASE, "Base ref mismatch")
    require(git("rev-parse", SOURCE).decode().strip() == SOURCE, "Source ref mismatch")
    old_tree, new_tree = tree(BASE), tree(SOURCE)
    removed = sorted(old_tree.keys() - new_tree.keys())
    added = sorted(new_tree.keys() - old_tree.keys())
    modified = sorted(p for p in old_tree.keys() & new_tree.keys()
                      if old_tree[p] != new_tree[p])
    require(not removed, "Existing tracked files removed")
    require(all(p.startswith(RECORD) for p in added), "Addition outside submission record")
    expected_modified = {"RESOLVED.md"}
    for number in range(1, 7):
        for name in ("README.md", "problem.tex", "problem.pdf"):
            expected_modified.add(f"arithmetic-and-complexity/AC-{number:02}/{name}")
    require(set(modified) == expected_modified, "Modified-file scope differs from expected 19")
    require(all(old_tree[p]["mode"] == new_tree[p]["mode"] and
                old_tree[p]["type"] == new_tree[p]["type"] for p in old_tree),
            "Existing file mode or type changed")

    registry_bytes = blob(BASE, "problem_ids.json")
    require(registry_bytes == blob(SOURCE, "problem_ids.json"), "Registry bytes changed")
    registry = json.loads(registry_bytes)
    require(len(registry) == 217 and len(set(registry.values())) == 217,
            "Expected 217 unique registered canonical paths")
    expected_changed_ids = {f"AC-{n:02}" for n in range(1, 7)}
    unchanged_ids, changed_records, canonical_digest_records = [], [], []
    before_counts = {field: Counter() for field in ("Status", "Difficulty", "Importance")}
    after_counts = {field: Counter() for field in before_counts}
    prior_markdown_link_count = 0

    for identity, path in sorted(registry.items()):
        require(path in old_tree and path in new_tree, f"Missing canonical page {identity}")
        old_bytes, new_bytes = blob(BASE, path), blob(SOURCE, path)
        old, new = old_bytes.decode(), new_bytes.decode()
        old_title = re.search(r"^# (.+)$", old, re.MULTILINE)
        new_title = re.search(r"^# (.+)$", new, re.MULTILINE)
        require(old_title and new_title and old_title.group(1) == new_title.group(1),
                f"Title changed: {identity}")
        require(old_title.group(1).startswith(identity + " "), f"Title identity mismatch: {identity}")
        field_values = {}
        for field in FIELDS:
            expression = r"^\*\*" + re.escape(field) + r":\*\* (.+?)\s*$"
            before = re.search(expression, old, re.MULTILINE)
            after = re.search(expression, new, re.MULTILINE)
            if field in {"Topic", "Rating rationale"} and before is None and after is None:
                field_values[field] = None
                continue
            require(before and after, f"Missing {field}: {identity}")
            require(before.group(1) == after.group(1), f"Changed {field}: {identity}")
            field_values[field] = before.group(1)
            if field in before_counts:
                before_counts[field][before.group(1)] += 1
                after_counts[field][after.group(1)] += 1

        if identity in expected_changed_ids:
            require(new.count(NOTICE) == 1 and NOTICE not in old,
                    f"Research-notice multiplicity mismatch: {identity}")
            prefix, notice = new.split(NOTICE)
            date_old = "**Last checked:** 2026-09-10"
            date_new = "**Last checked:** 2026-09-14"
            require(old.count(date_old) == 1 and prefix.count(date_new) == 1,
                    f"Unexpected last-checked field: {identity}")
            normalized_prefix = prefix.replace(date_new, date_old, 1).rstrip("\n")
            require(normalized_prefix == old.rstrip("\n"),
                    f"Prior canonical text changed: {identity}")
            require(field_values["Status"] == "Open", f"AC status is not Open: {identity}")
            require("Open" in notice, f"Appended notice omits Open status: {identity}")
            tex_path = str(PurePosixPath(path).with_name("problem.tex"))
            old_tex, new_tex = blob(BASE, tex_path).decode(), blob(SOURCE, tex_path).decode()
            require(new_tex.count(TEX_NOTICE) == 1 and TEX_NOTICE not in old_tex,
                    f"TeX notice mismatch: {identity}")
            tex_prefix, tex_notice = new_tex.split(TEX_NOTICE)
            require(tex_notice.endswith("\\end{document}\n"), f"TeX ending mismatch: {identity}")
            require(old_tex.count("Literature check: 2026-09-10") == 1 and
                    tex_prefix.count("Literature check: 2026-09-14") == 1,
                    f"TeX date mismatch: {identity}")
            normalized_tex = tex_prefix.replace("Literature check: 2026-09-14",
                                                "Literature check: 2026-09-10", 1)
            normalized_tex += "\\end{document}\n"
            require(re.sub(r"\s+", "", old_tex) == re.sub(r"\s+", "", normalized_tex),
                    f"Prior non-whitespace TeX content changed: {identity}")
            changed_records.append({"id": identity, "path": path,
                                    "title": old_title.group(1), "fields": field_values,
                                    "before_sha256": sha(old_bytes), "after_sha256": sha(new_bytes),
                                    "prior_text_preserved_after_date_and_append_removal": True,
                                    "prior_tex_nonwhitespace_content_preserved": True})
        else:
            require(old_bytes == new_bytes, f"Unexpected canonical change: {identity}")
            unchanged_ids.append(identity)

        old_links = Counter(re.findall(r"\]\(([^\n)]+)\)", old))
        new_links = Counter(re.findall(r"\]\(([^\n)]+)\)", new))
        require(not old_links - new_links, f"Prior Markdown link lost: {identity}")
        prior_markdown_link_count += sum(old_links.values())
        canonical_digest_records.append({"id": identity, "path": path,
                                         "base_sha256": sha(old_bytes), "source_sha256": sha(new_bytes)})

    require(len(unchanged_ids) == 211 and len(changed_records) == 6, "Canonical count mismatch")
    require(before_counts == after_counts, "Status or rating distribution changed")

    indexes = sorted({"README.md", "CATALOG.md", "problem_ids.json"} |
                     {p.split("/")[0] + "/README.md" for p in registry.values()})
    for path in indexes:
        require(path in old_tree and old_tree[path] == new_tree[path], f"Index changed: {path}")
    before_resolved, after_resolved = blob(BASE, "RESOLVED.md"), blob(SOURCE, "RESOLVED.md")
    resolved_text = after_resolved.decode()
    resolved_header = "## Reviewed AC-01–AC-06 research — 14 September 2026\n"
    require(resolved_text.count(resolved_header) == 1, "RESOLVED notice count mismatch")
    begin = resolved_text.index(resolved_header)
    end = resolved_text.index("## Resolved catalog entries", begin)
    insertion = resolved_text[begin:end]
    require((resolved_text[:begin] + resolved_text[end:]).encode() == before_resolved,
            "Prior RESOLVED text altered")
    require(insertion.startswith(resolved_header + "\n**All six remain Open.**"),
            "RESOLVED insertion status mismatch")

    provenance_bytes = blob(SOURCE, RECORD + "provenance.json")
    provenance = json.loads(provenance_bytes)
    require(len(provenance) == 6, "Expected six original archive records")
    all_members, member_records, archive_records = set(), [], []
    source_basenames = {PurePosixPath(p).name for p in new_tree}
    for archive, record in sorted(provenance.items()):
        require(set(record) == {"sha256", "files"}, f"Unexpected provenance schema: {archive}")
        require(re.fullmatch(r"[0-9a-f]{64}", record["sha256"]), "Bad archive digest format")
        archive_records.append({"archive": archive, "declared_archive_sha256": record["sha256"],
                                "member_count": len(record["files"]),
                                "original_archive_present_in_source_tree": archive in source_basenames,
                                "original_archive_digest_independently_verified": False})
        for relative_path, expected_hash in sorted(record["files"].items()):
            relative = PurePosixPath(relative_path)
            require(not relative.is_absolute() and ".." not in relative.parts,
                    f"Unsafe provenance member path: {relative_path}")
            path = SUBMITTED + relative_path
            require(path not in all_members, f"Duplicate provenance member path: {path}")
            all_members.add(path)
            require(path in new_tree and new_tree[path]["type"] == "blob" and
                    new_tree[path]["mode"] in {"100644", "100755"}, f"Missing/nonregular member: {path}")
            require(re.fullmatch(r"[0-9a-f]{64}", expected_hash), f"Malformed digest: {path}")
            content = blob(SOURCE, path)
            actual_hash = sha(content)
            require(actual_hash == expected_hash, f"Provenance digest mismatch: {path}")
            member_records.append({"archive": archive, "member": relative_path,
                                   "bytes": len(content), "sha256": actual_hash,
                                   "matches_provenance": True})
    submitted_tree_paths = {p for p in new_tree if p.startswith(SUBMITTED)}
    require(len(all_members) == 227, "Expected 227 distinct member records")
    require(submitted_tree_paths == all_members, "Submitted files and provenance path sets differ")
    require(not any(r["original_archive_present_in_source_tree"] for r in archive_records),
            "Original archive unexpectedly present; assess digest separately")

    report = {
        "verdict": "PASS within stated preservation and member-hash scope",
        "base_commit": BASE, "source_commit": SOURCE,
        "base_tree": git("rev-parse", BASE + "^{tree}").decode().strip(),
        "source_tree": git("rev-parse", SOURCE + "^{tree}").decode().strip(),
        "method": "Independent standard-library checker reading immutable Git objects; no imported audit or repository code",
        "tracked_files": {"base_count": len(old_tree), "source_count": len(new_tree),
                          "added_count": len(added), "modified_count": len(modified),
                          "removed": removed, "modified_paths": modified,
                          "all_additions_under": RECORD, "existing_modes_and_types_preserved": True},
        "canonical_pages": {"count": len(registry), "registry_sha256": sha(registry_bytes),
                            "byte_identical_count": len(unchanged_ids),
                            "changed_only_by_research_append_and_check_date": changed_records,
                            "all_ids_paths_titles_fields_prior_text_targets_and_citations_retained": True,
                            "prior_markdown_link_occurrences_retained": prior_markdown_link_count,
                            "distribution_before_and_after": {k: dict(sorted(v.items())) for k, v in before_counts.items()},
                            "digest_ledger_sha256": sha(json.dumps(canonical_digest_records, sort_keys=True).encode())},
        "unchanged_indexes": {p: new_tree[p]["oid"] for p in indexes},
        "resolved": {"original_bytes_retained_around_single_research_insertion": True,
                     "inserted_lines": len(insertion.splitlines()), "insertion_sha256": sha(insertion.encode())},
        "provenance": {"manifest_sha256": sha(provenance_bytes), "archive_count": len(provenance),
                       "all_227_committed_member_sha256_values_match": True,
                       "member_path_set_equals_all_submitted_files": True,
                       "member_count": len(all_members), "archives": archive_records,
                       "members": member_records},
        "limitations": [
            "The six original top-level ZIP byte streams are unavailable in this source tree. Their declared SHA-256 values are recorded, not independently authenticated. Extraction completeness cannot be checked against their central directories.",
            "Member-hash equality establishes consistency with the committed provenance manifest, not independent author identity, original archive authenticity, or mathematical validity.",
            "Five nested ZIP files are checked as intact member bytes. Their contents are not re-extracted in this bounded cross-check.",
            "No proof, checker replay, PDF visual inspection, repository test, literature search, or new open-status assessment is repeated here. Separate mathematical and PDF audits cover those scopes.",
            "Changed TeX files retain all prior non-whitespace content after removal of the appended notice and check-date update; AC-02 and AC-04 also contain harmless line wrapping changes inspected in their diffs. Binary PDF content is not compared semantically here."
        ]
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"verdict": report["verdict"], "base": BASE, "source": SOURCE,
                      "canonical_pages": 217, "byte_identical_canonical_pages": 211,
                      "open_ac_pages_retained": 6, "deleted_files": 0,
                      "added_files": len(added), "modified_existing_files": len(modified),
                      "verified_submission_members": 227,
                      "distribution": report["canonical_pages"]["distribution_before_and_after"],
                      "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
