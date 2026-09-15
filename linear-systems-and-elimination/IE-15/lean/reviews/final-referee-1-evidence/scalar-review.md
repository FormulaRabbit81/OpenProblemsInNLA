# IE-15 proof referee 1 — scalar, coordinate and witness pass

Date: 2026-09-15. Reviewer: independent OpenAI Codex AI agent `/root/reference_api_review`; no proof implementation by this reviewer. The same reviewer independently approved the unchanged pre-proof statement boundary. This pass applies Tau Ceti's adversarial semantic, scope, attribution, reuse and proof-quality standards at rubric revision `603b28011f779bd341d0a08e788498b81542bd7d`.

## Provisional verdict

**APPROVE the reviewed scalar/coordinate/witness modules. No material findings. Overall final proof approval is withheld pending the complete NormalizedBounds, Reduction, Proof and Solution modules, full-target correspondence, reproducible verification and Comparator evidence.**

This pass includes the actual imported Basic and Definitions source, not only the four assigned files. No proof, source or project configuration was changed. Copies and checks were made under this scratch directory.

## Exact inspected source hashes

| Input relative to project root | SHA-256 |
|---|---|
| `NLA/IE15/Definitions.lean` | `8d43a24d1aba8dfd616a66a49463d0bb4bee798c1dd904c2bf7614a5e4bb90ab` |
| `NLA/IE15/Basic.lean` | `1df00296842bb5970508912dbd52834f308e930dc5e9cce023d203b41a53033a` |
| `NLA/IE15/Scalar.lean` | `5acf89a5f311819c151399299bebcfdc8602b7c466b7473652584fce65d509aa` |
| `NLA/IE15/FourthScalar.lean` | `3c55e8dc0d253a726aa7963d087b13bdfbaf1b547a56a0ebb03507aca20a30af` |
| `NLA/IE15/Coordinates.lean` | `a889559725d1faab768d21c109b4e3ce4500cc13a88f52b22afccf04c8908de3` |
| `NLA/IE15/Witnesses.lean` | `1ef349f423ffa8bab7d55fba3662417a3cbd9a5ccd4a94819db4fadaaf0f2241` |
| `lakefile.toml` | `ede3790abea57c69ba1fe6591b1b5d6ff52f17fe9d313ab7c5372359f9422639` |
| `lake-manifest.json` | `870a86a98be8aef373fc3461f690535afbd67d33a44f210c488e65fabe2d9a06` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `Challenge.lean` | `2193762b8e25272342703e34d8246a4a5901dd0cdb0eec71f30ad97ccf5186b9` |
| `NUMERICAL_TARGETS.md` | `36a0149348cad5c9e71bc18b506df384d0641470cb70510add53871129ee4546` |
| `comparator.json` | `5198b3f85a070ce13298ee7af09cfef9984e0a932eb888e62fd4213634893b7a` |

## Semantic findings checked

- `scalar_product_bound` is a valid exact replacement for the manuscript's Phi/min monotonicity: the inequalities imply nonnegative q*x and q*y, their product is <=U*V, x*y<=1 and q*x*y<=2. Expanding `(2-q)*(2-q*x*y)>=0` establishes the desired bound. It includes boundary q=0, q=2 and x,y=0,1 and imposes no unsupported sign restriction on U or V beyond what the premises imply.
- `scalar_two_pivot_bound` matches the full frozen signed scalar domain and all three original-entry constraints. Its q<=1, b>0, b<0/a>0, d2<=0, d1>=0 and d1<0<d2 cases are exhaustive. The final algebraic substitution U=1+c1, V=1-d1 follows from the original inequalities and multiplier bounds. No continuous domain was replaced by a finite search or numerical sample.
- `scalar_two_pivot_cross_bound` derives W<=2 from the full scalar inequality when p+q>=2; when p+q<2 it uses each c*d<=1. It therefore does not need a nonzero final three-by-three Schur value or a positivity premise on that value. This removes the manuscript's singular-submatrix detour without weakening the required bound or introducing circular dependence.
- `scalar_bilinear_corner_bound` directly sums the four nonnegative corner deficits using unit-square weights; `scalar_bilinear_lower` substitutes `(u+1)/2,(v+1)/2` and retains u,v,d in their full signed domains. These are exact identities.
- `scalar_fourth_bound` uses the complete signed domains of d1,d2,D,u1,u2,v1,v2. D<=0 follows directly from r>0,C>=0 and W<=2; for D>0 all multipliers of the original-entry inequalities are nonnegative. The alpha,beta,gamma bilinear expression equals the required fixed-u,v upper bound; corners use W<=2, p+q<=3 and the scalar h bound. It avoids taking an optimizer minimum by proving a common bound for every fixed choice of the actual u,v. The final contribution bound 11/3 is exact. The named lower bound on D is unused but matches the source multiplier domain; it does not restrict the canonical target.
- `Coordinates` defines pivots and multipliers from the actual diagonal no-swap trajectory. Admissibility proves each divisor nonzero and each row/column multiplier bound. The prefix-coordinate identity is proved by induction from the actual Schur recurrence, with no LDR factorization or reconstruction assumed. This module alone concerns diagonal paths; the not-yet-reviewed Reduction must transfer arbitrary canonical paths and normalization to it.
- `Basic` uses the frozen definitions and ordinary finite maximum semantics. Its per-step bound handles actual independent row/column swaps and bounds all entries, not pivots alone. Its positive initial maximum follows from the actual first admissible nonzero pivot, sufficient even without using determinant nonsingularity.
- `Witnesses` computes every padded Schur matrix, determinant, weak rook inequalities including ties, stage maxima and growth exactly. The order-four second Schur complement maximum is 3, correctly distinguished from the rough universal bound 4. Both final witness packages have the exact frozen signatures. Existing rational witness arithmetic was independently checked during the pre-proof review; this pass additionally checks the Lean proofs.

## Trust and execution evidence

I copied the exact source inputs above to `scalar-snapshot/`, sharing only the pinned project dependency cache through `.lake/packages`, and independently ran with PATH prefixed by `/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin`:

```text
lake build NLA.IE15.FourthScalar NLA.IE15.Coordinates NLA.IE15.Witnesses
```

The command exited 0 and newly built Definitions, Basic, Coordinates, Witnesses, Scalar and FourthScalar; it reported a successful 3011-job build with no warnings. Reported module times were 1.0s, 2.3s, 2.6s, 4.2s, 12s and 2.2s respectively. These source files had no prior local module build output in this scratch project; Mathlib/LeanCert dependency caches were reused. This was a local macOS build, not isolated Linux Comparator verification.

I then ran the retained `scalar-snapshot/Audit.lean` via `lake env lean Audit.lean`. It prints actual elaborated key signatures and transitive axioms, and runs LeanCert `#assert_trust kernel` for ten load-bearing exports: scalar_product_bound, scalar_two_pivot_bound, scalar_two_pivot_cross_bound, scalar_bilinear_lower, scalar_fourth_bound, entry_prefix_coordinates, witness_three_proved, witness_four_proved, rook_stage_bound_proved and entryMax_semantics_proved. All ten print exactly `propext`, `Classical.choice`, `Quot.sound`, and all trust assertions passed. The durable output and command/exit/timing record are `scalar-axiom-audit.log` and `scalar-axiom-audit.json`. The initial interactive axiom inspection also exited 0; the retained rerun exists to preserve reproducible audit evidence.

Source scans of these proof modules found no sorry, admit, custom axiom, native_decide, native compiler axiom reference, unsafe definition, implemented_by or kernel-bypass setting. Explicit finite local heartbeat budgets in the two nonlinear scalar proofs change elaboration resources, not the target or trusted axioms. The imported Mathlib tactic closure is trusted at its pinned manifest revision; the axiom audit examines the actual theorem closures rather than assuming that every library module is automatically admissible.

## Scope, reuse and attribution

The proof follows the original George Stepaniants solution with explicit algebraic simplifications. Headers preserve original proof attribution, the requested Caltech affiliation and AI assistance. Basic credits its retained IE-05 finite-maximum design. Searches of Mathlib found standard multiplication and absolute-value inequalities used by these proofs and no direct replacement for the problem-specific signed two-pivot or order-four inequalities. The bilinear corner lemma is a short exact specialized interpolation identity with a direct consumer. No competing general-purpose theory was introduced. Source claims and comments match the proof scope.

```json
{"verdict":"approve","summary":"The inspected scalar, coordinate, Basic and witness proof modules preserve all reviewed domains and pass an independent local Lean build and foundational-axiom assertions. Overall final approval remains pending the arbitrary-path reduction, normalized bounds and public exports.","findings":[]}
```
