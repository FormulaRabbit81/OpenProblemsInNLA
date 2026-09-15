# Maintainer audit of PR #264: MF-24

**Decision: accept the complete negative resolution and mark MF-24 Solved.**
Georg Maierhofer's explicit weighted shifts refute the original request for a
dimension-independent polynomial-norm comparison constant. The exact constants
and their optimal dimension growth remain open. This is an independent informal
AI audit, not external human peer review, a novelty determination, or Lean
verification.

- Source: [PR #264](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/264),
  commit `32b028cf16e210f8f628ab1cc7c8f5b389df0632`.
- Published base: `6d840cd6bdf811e166ba0a07501407fb121ff0ce`.
- Source tree: `48d6aeebdd12b908b3166e41444b14b79f222434`.
- Source-preserving integration merge: `3daadb3783872f4d62ee922dfafc46127aa23a2b`.
- Review date: 15 September 2026.

## Why the proof resolves the retained target

The [original statement](../../matrix-functions-and-stability/MF-24/README.md)
asks whether the comparison constants are uniformly bounded over all dimensions.
It permits both the matrices and their common polynomial to depend on dimension.
Determining sharp constants is separately identified there as a related question.

[Theorem 1 and equation (15)](../../references/mf24-counterexample/proof.pdf)
provide finite rational examples at every integer parameter `m >= 2`, of order
`(m+1)^2`, with norm ratio at least `(4/5)sqrt(m)`. This diverges, so it refutes
every proposed finite universal constant. The denominator is explicitly nonzero.
The proof establishes equality of **all** singular values after **every complex**
shift, including zero, by a polynomial determinant identity. Sampled SVDs are
supplementary evidence, not the justification for that universal statement.

The independent [mathematical review](mathematics/review.md) checks the complete
written proof: the bridge identity over a commutative ring, transfer-product
orientation, multiplicities, residue-class block decomposition, spectral-norm
domination for complex vectors, and the finite rational divergent witnesses.
Corollary 3's additional lower bound for arbitrary dimensions follows by taking
a supremum over finite parameters and padding by identical zero blocks. It
does not assert attainment or optimal growth.

The separate [computational review](computation/review.md) inspects the source
programs before execution, reruns them under their pinned NumPy/SymPy versions,
and supplies an independent checker. It reconstructs shifted-Gram determinant
polynomials through bipartite-path matchings rather than importing the submitted
transfer recurrence. Exact rational norm certificates and deliberate corruptions
provide additional checks. The reports distinguish these finite checks from the
all-size written argument.

The [preservation and PDF review](preservation-pdf/README.md) independently
checks the original target, references, permanent numbering and document
presentation. The source manuscript and its four pages are retained unchanged.
The current Cambridge affiliation is supported by the
[university-hosted profile](https://www.damtp.cam.ac.uk/user/gam37/).
Authorship remains as asserted by the contributor, with AI assistance disclosed.

The new counterexample is self-contained elementary linear algebra. The cited
Ransford–Walsh definition and upper bound were checked in the primary paper.
The full 2009 article was inaccessible in this bounded review, so its page-513
locator was not freshly authenticated. This does not supply a missing premise
for the counterexample or change its correspondence with the fixed base target.

## Integration changes and validation

- Promote **Solution claimed** to **Solved**, date the maintainer assessment,
  credit Georg Maierhofer and link this fresh audit. Keep the original target,
  historical difficulty/importance ratings, prior references and supplied proof.
- Preserve the entire submitted research package. Its README gains a dated
  maintainer addendum; earlier proposed-status and self-review text remains
  explicitly historical.
- Regenerate the canonical PDF with a page break before Context and notation,
  keeping the complete original statement and its universal quantifiers together.
  The source's removal of an unnecessary References break is retained. Both
  renderer exceptions affect MF-24 only.
- Required permanent-ID validation, catalog regeneration and 17 ID tests pass.
  All 77 repository tests pass at both the source and final integration content.
  Mathematics formatting checks pass; Lean project selection is empty.
- Counts become **113 open targets** (42 Open, 71 Partially resolved),
  **73 Solved**, and **31 Lean verified**, across the same 217 retained IDs.
  The recently published repository motivation text is preserved.

[Root preservation evidence](root/preservation.json) binds the final source
files and explicit integration exceptions. Original submission Markdown contains
intentional hard-break spaces and a historical log ends with a blank line; this
audit does not claim that the complete inherited diff is whitespace-clean.
No safeguard, workflow or formalization is weakened or replaced.

## Evidence and reproduction

The pairwise reports include their portable checks, commands, hashes and evidence
limits. Root repository test logs and preservation scripts are under `root/`.
`SHA256SUMS` binds all files in this review directory except itself. Final GitHub
CI and publication receipts are attached to the integration PR, so they can
identify the final tested commit without changing the tree after testing.
