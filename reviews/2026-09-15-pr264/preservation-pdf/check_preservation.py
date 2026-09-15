#!/usr/bin/env python3
"""Read-only independent preservation audit of immutable PR264 source objects."""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "6d840cd6bdf811e166ba0a07501407fb121ff0ce"
SOURCE = "32b028cf16e210f8f628ab1cc7c8f5b389df0632"
CANONICAL = "matrix-functions-and-stability/MF-24/README.md"


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    def git(*parts):
        return subprocess.check_output(["git", "-C", args.repo, *parts])

    def data(ref, path):
        return git("show", ref + ":" + path)

    def tree(ref):
        result = {}
        for line in git("ls-tree", "-r", "-z", ref).split(b"\0"):
            if line:
                fields, path = line.split(b"\t", 1)
                result[path.decode()] = fields.decode().split()
        return result

    before, after = tree(BASE), tree(SOURCE)
    removed = sorted(before.keys() - after.keys())
    added = sorted(after.keys() - before.keys())
    changed = sorted(p for p in before.keys() & after.keys() if before[p] != after[p])
    require(not removed, "A prior file was removed")
    require(all(before[p][:2] == after[p][:2] for p in before), "Prior mode or type changed")
    expected_changes = {"CATALOG.md", "README.md", "RESOLVED.md", "tools/render_problems.py",
                        "matrix-functions-and-stability/README.md", CANONICAL,
                        CANONICAL.replace("README.md", "problem.pdf"),
                        CANONICAL.replace("README.md", "problem.tex")}
    require(set(changed) == expected_changes, "Unexpected changed-file scope")
    require(len(added) == 14 and all(p.startswith("references/mf24-counterexample/") for p in added),
            "Unexpected addition scope")
    old_reference_paths = [p for p in before if p.startswith("references/")]
    require(all(before[p] == after[p] for p in old_reference_paths), "Prior reference artifact changed")
    old_registry = data(BASE, "problem_ids.json")
    require(old_registry == data(SOURCE, "problem_ids.json"), "Registry changed")
    registry = json.loads(old_registry)
    require(len(registry) == len(set(registry.values())) == 217, "Registry identity count changed")
    statuses = {BASE: Counter(), SOURCE: Counter()}
    category_counts = {BASE: Counter(), SOURCE: Counter()}
    prior_links = 0
    for identity, path in registry.items():
        old, new = data(BASE, path).decode(), data(SOURCE, path).decode()
        require(old.splitlines()[0] == new.splitlines()[0], f"Title changed: {identity}")
        require(old.splitlines()[0].startswith("# " + identity + " — "), f"Wrong ID: {identity}")
        if path != CANONICAL:
            require(old == new, f"Other canonical README changed: {identity}")
        for field in ("Topic", "Difficulty", "Importance", "Rating rationale"):
            expr = r"^\*\*" + field + r":\*\* (.+?)\s*$"
            a, b = re.search(expr, old, re.M), re.search(expr, new, re.M)
            require((a.group(1) if a else None) == (b.group(1) if b else None),
                    f"Rating/topic changed: {identity} {field}")
        old_links = Counter(re.findall(r"\]\(([^\n)]+)\)", old))
        new_links = Counter(re.findall(r"\]\(([^\n)]+)\)", new))
        require(not old_links - new_links, f"Prior canonical reference lost: {identity}")
        prior_links += sum(old_links.values())
        for ref, content in ((BASE, old), (SOURCE, new)):
            status = re.search(r"^\*\*Status:\*\* (.+?)\s*$", content, re.M).group(1)
            statuses[ref][status] += 1
            if status in {"Open", "Partially resolved"}:
                category_counts[ref][path.split("/")[0]] += 1

    old, new = data(BASE, CANONICAL).decode(), data(SOURCE, CANONICAL).decode()
    start = new.index("## Resolution claim (14 September 2026)\n")
    end = new.index("## Context and notation\n", start)
    recovered = new[:start] + new[end:]
    recovered = recovered.replace("**Status:** Solution claimed\n", "**Status:** Partially resolved  \n", 1)
    recovered = recovered.replace("**Last checked:** 2026-09-14", "**Last checked:** 2026-09-11", 1)
    history = "## Original scope and literature check\n\nThe following is the repository's pre-claim literature record, retained unchanged.\n\n\n"
    require(history in recovered, "Unexpected literature-history insertion")
    recovered = recovered.replace(history, "## Scope and status check\n\n", 1)
    require(recovered == old, "Prior MF-24 text was altered beyond disclosed edits")

    def section(content, name, next_name):
        return content.split("## " + name + "\n", 1)[1].split("## " + next_name + "\n", 1)[0]

    require(section(old, "Problem statement", "References") ==
            section(new, "Problem statement", "References"), "Original mathematical target changed")
    require("Determine whether $`\\sup_{N\\geq1}C_N<\\infty`$" in old, "Original uniform target absent")
    expected_before = {"Open": 42, "Partially resolved": 72, "Solved": 72, "Lean verified": 31}
    expected_after = {"Open": 42, "Partially resolved": 71, "Solved": 72, "Lean verified": 31,
                      "Solution claimed": 1}
    require(dict(statuses[BASE]) == expected_before and dict(statuses[SOURCE]) == expected_after,
            "Unexpected canonical status distribution")
    summary = "**113 problems with open targets:** 42 open and 71 partially resolved. **104 other retained entries**, excluded from the open count."
    for path in ("README.md", "CATALOG.md"):
        text = data(SOURCE, path).decode()
        require(summary in text, f"Incorrect index summary: {path}")
        require("**Resolution evidence:** 72 solved (published or independently audited); 31 solved with Lean verification." in text,
                f"Incorrect evidence counts: {path}")
    require(category_counts[SOURCE]["matrix-functions-and-stability"] == 13, "Category count mismatch")
    require("**13 problems with open targets.** 12 retained entries are excluded from the open count." in
            data(SOURCE, "matrix-functions-and-stability/README.md").decode(), "Wrong category summary")
    for path in {p.split("/")[0] + "/README.md" for p in registry.values()} - {"matrix-functions-and-stability/README.md"}:
        require(before[path] == after[path], f"Other category index changed: {path}")

    old_resolved, new_resolved = data(BASE, "RESOLVED.md").decode(), data(SOURCE, "RESOLVED.md").decode()
    start = new_resolved.index("### MF-24 — a claimed negative resolution of uniform boundedness\n")
    end = new_resolved.index("### 🏆 MI-32", start)
    require(new_resolved[:start] + new_resolved[end:] == old_resolved, "Prior RESOLVED text changed")

    old_renderer = data(BASE, "tools/render_problems.py").decode()
    new_renderer = data(SOURCE, "tools/render_problems.py").decode()
    removed_string = "'IE-27', 'MF-24', 'MI-30', 'MI-31',"
    retained_string = "'IE-27', 'MI-30', 'MI-31',"
    require(old_renderer.count(removed_string) == 1 and
            old_renderer.replace(removed_string, retained_string, 1) == new_renderer,
            "Renderer edit exceeds single MF-24 set-entry removal")
    old_ast, new_ast = ast.parse(old_renderer), ast.parse(new_renderer)
    def reference_break_set(parsed):
        for node in ast.walk(parsed):
            if isinstance(node, ast.If) and isinstance(node.test, ast.Compare) and isinstance(node.test.comparators[0], ast.Set):
                values = ast.literal_eval(node.test.comparators[0])
                if {"IE-27", "MI-30", "MI-31", "AA-01"} <= values:
                    return values
        raise RuntimeError("Reference-break set not found")
    old_set, new_set = reference_break_set(old_ast), reference_break_set(new_ast)
    require(old_set - new_set == {"MF-24"} and not new_set - old_set, "Renderer scope error")
    require(all((identity in old_set) == (identity in new_set) for identity in registry if identity != "MF-24"),
            "Other ID rendering condition changed")
    source_tex = data(SOURCE, CANONICAL.replace("README.md", "problem.tex")).decode()
    require("\\newpage\n\\subsection{References}" not in source_tex, "Stale reference break remains")

    relevant_paths = changed + added + ["problem_ids.json"]
    result = {
        "verdict": "PASS preservation, source status arithmetic, and scoped renderer change; improve canonical PDF pagination",
        "base_commit": BASE, "source_commit": SOURCE,
        "base_tree": git("rev-parse", BASE + "^{tree}").decode().strip(),
        "source_tree": git("rev-parse", SOURCE + "^{tree}").decode().strip(),
        "existing_files": len(before), "source_files": len(after), "removed_files": removed,
        "added_files": added, "modified_existing_files": changed,
        "prior_reference_artifacts_unchanged": len(old_reference_paths),
        "registry_count": len(registry), "registry_sha256": sha(old_registry),
        "identical_canonical_readmes": 216,
        "mf24_prior_readme_exactly_recovered_after_disclosed_edits": True,
        "mf24_problem_statement_sha256": sha(section(old, "Problem statement", "References").encode()),
        "prior_canonical_markdown_link_occurrences_retained": prior_links,
        "status_before": dict(statuses[BASE]), "status_source": dict(statuses[SOURCE]),
        "open_target_count_before": sum(category_counts[BASE].values()),
        "open_target_count_source": sum(category_counts[SOURCE].values()),
        "renderer_only_affected_registered_id": "MF-24",
        "renderer_base_reference_break_set_size": len(old_set),
        "renderer_source_reference_break_set_size": len(new_set),
        "source_file_sha256": {p: sha(data(SOURCE, p)) for p in sorted(relevant_paths)},
        "limits": ["This script checks retained bytes and field/index consistency, not proof correctness.",
                   "Source status is Solution claimed. A future Solved integration requires regenerating evidence counts and PDF.",
                   "PDF layout observations and primary literature checks are recorded separately in README.md."]
    }
    Path(args.output).write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k:result[k] for k in ("verdict", "registry_count", "identical_canonical_readmes",
                                          "prior_reference_artifacts_unchanged", "open_target_count_source",
                                          "renderer_only_affected_registered_id")}, indent=2))


if __name__ == "__main__":
    main()
