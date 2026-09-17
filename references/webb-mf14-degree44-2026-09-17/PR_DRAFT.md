# Proposed pull request

**Title:** Resolve MF-14 negatively with independently audited degree-44 coverage

**Base:** `ajt60gaibb/OpenProblemsInNLA:main`

**Local branch:** `codex/mf14-degree44-resolution`

## Description

MF-14 asks whether the largest degree covered by the complex Zariski closure of all seven-product polynomial evaluations is 42. This contribution by Marcus Webb (The University of Manchester) proves coverage through degree 44, giving a complete negative answer to that equality. The exact new maximum is not determined; the proof also derives `44 <= d_7 <= 47` using Jarlebring–Lorentzon's published dimension theorem.

The proof supplies a simultaneous four-product border construction followed by three products with an exact 45-by-45 Jacobian determinant of 256. Two separate Codex agents independently audited the mathematical argument and recomputed the symbolic and integer certificates. The package contains a standalone six-page proof, source provenance, their reports, three standard-library Python verifiers and complete certificates. The proof was developed with substantial ChatGPT assistance; the reviews are informal AI-agent reviews, not external human peer review or formal verification.

The canonical entry changes from `Partially resolved` to `Solved` with an explicit negative-resolution notice. Its permanent ID, path and original problem statement are unchanged. Colbrook's earlier degree-42 theorem and original archive retain their credit and contents. The resolution archive, indexes, counts and canonical PDF/TeX are updated; the open count changes from 113 to 112.

## Review links

- [Canonical entry](../../matrix-functions-and-stability/MF-14/README.md)
- [Complete proof](proof.pdf) and [LaTeX source](proof.tex)
- [Submission and reproduction](README.md)
- [Border review](verification/border-review.md) and [continuation review](verification/continuation-review.md)
- [Verification record](verification/checks.md)

## Validation

- All three exact verifiers pass, including optimized Python execution; the two independently reconstructed Jacobians agree in all 2,025 entries.
- Permanent-ID validation against `origin/main`; ID safeguard and catalog-status tests.
- GitHub math-format checks and formatting/rendering tests.
- Canonical indexes regenerated; original target and registry preservation checked.
- Proof and canonical PDFs compiled and visually inspected; `git diff --check` passes.

This file is the prepared PR text. No branch has been pushed and no pull request has been opened; publication awaits the author's review and instruction.
