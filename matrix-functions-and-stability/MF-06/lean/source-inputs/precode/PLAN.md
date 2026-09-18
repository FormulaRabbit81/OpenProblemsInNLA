# MF-06 pre-code handoff

The complete unchanged pointwise lower-Lipschitz target is plausible to formalize, but is not a short extension of MF05/MF07. This packet records a bounded feasibility task. It contains no new Lean declaration, proof body, statement approval, freeze, local compile or Comparator result. Complete formalization and new mathematical-resolution counts both increase by zero.

Read `NUMERICAL_TARGETS.md` first, then `SOURCE_CORRESPONDENCE.md` and `API_MAP.md`. The numerical obligations were written before any new Lean source. The source table covers every argument needed for arbitrary dimension and arbitrary nonempty compact complex matrix families, including zero radius, singular matrices, irreducible/reducible references and perturbations that do not preserve the reference invariant flag.

The two large missing foundations are the product-bounded-reference stable-kernel/quotient/cone theorem, and the critical exterior theorem. The latter includes genuine irreducible-family product boundedness, finite invariant flags, exterior allocation triangularization and paired nonresonance. None may be supplied as an assumed oracle. Existing algebraic exterior maps and determinant coordinates are useful but do not supply those dynamical results.

A smaller route is available for geometry: use concrete compound matrices with their ordinary coordinate spectral norm and fixed dimension-dependent bounds. Such constants disappear in word-root limits. Elementary two-sided entry estimates also avoid exact Hilbert tensor norm multiplicativity. This preserves the theorem while avoiding an absent complex exterior inner-product library. The cone and finite-sum estimates can remain symbolic; no dimension/permutation enumeration or numerical interval subdivision is needed.

The seven user requirements remain mandatory if development continues:

1. Consume the exact kernel-mode LeanCert half-radius result in the actual cone/transfer proof, after fixing the MF05 published source pin. No unused-certificate claim.
2. Retain the copied Schiffer/Forsythe structure examples and exact MF05/MF07 reuse boundary.
3. Use the computation reductions above and the symbolic obligations N0–N6.
4. Choose complete concrete definitions and write the independent Challenge before implementation. Obtain two independent nonauthor statement reviews, then freeze the exact types. This packet is not that freeze.
5. Apply the pinned Tau Ceti correctness, generality, proof-quality, reuse and attribution standards with independent full proof referees.
6. Run local Lean first, under root's single-compiler limit. Run real Comparator only on GitHub non-root Linux, with exact frozen contracts and published source bindings.
7. Add truthful schema-v0.4 `formalization.yaml` when an actual formalization package exists. The copied schema and guidance are references, not evidence that a new MF-06 package validates.

`SOURCE-CAPTURE.json` records successful read-only extraction of 37 authoritative source/review files at upstream commit `3923b68ecee13d02e732085a57b42a2e7e95ac7a`. Historical scripts and Lean files are inert `.txt` copies. The original manuscript and historical independent review remain attributed to their authors; historical informal approval does not substitute for a new formal-code review.

The duplicate scope is bounded and explicit. The retained 16 September snapshot contains 14 public repositories, 249 branch heads and 203 complete tree inventories. Its independent MF-06 identifier-named Lean/metadata scan has zero hits. A fresh 17 September upstream all-state MF-06 PR query returns the merged informal solution PR149 and context PR110/PR231; the captured current canonical tree has no MF-06 Lean directory. Fresh upstream and user-fork branch-head metadata is also retained. This does not exclude later, private, deleted, unpushed or differently named work, and does not claim a complete contemporaneous all-fork scan. Initial network failures are retained separately from the successful read-only retry.

Run the packet checker without Lean or network:

```bash
python3 verify_packet.py
```

To re-read the original retained compressed public tree inventories as well:

```bash
python3 verify_packet.py --live-public-snapshot
```

Both commands are read-only. Their successful execution establishes only the stated inventory, hash, command-record and status checks. They do not certify the proposed mathematics. Preserve this directory once sealed; future statement/code work belongs outside it, with a separate source-bound review and freeze.

After the source capture, root reported MF05 proof commit `06b8cf49740205c4b7b0b71ee5c636855fbe26a6` and successful Linux run `35252365986`. `PARENT-STATUS.json` records this as a parent report; this agent has not audited that runtime in the present task. The original pending-publication capture records are preserved unchanged.
