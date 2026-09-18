# NM-04 independent referee 1: exact-source204 continuation

**Verdict: APPROVE_EXACT_SOURCE204_CONTINUATION.** No mathematical or proof-source blocker remains in the reviewed repair. This is a continuation of my complete original-target, 38-module, 35-contract source187 review. It does not certify a new Linux Comparator run, accept a final published commit, or increase the completed-target count.

I am `/root/nm04_final_referee1`. I have never authored NM-04 statement, proof, helper, repair, or compiler-harness code. I did not edit the candidate, run Lean or Lake, run Comparator, or start GitHub jobs. I independently inspected the changed source, unchanged boundaries, root's actual local evidence, raw expression dumps, and the relevant primary Mathlib and Lean source. I recorded my conclusions before reading any other referee's continuation findings; I have not read those findings. My only executed verification is read-only Python consistency checking. Agent review is not external human peer review or official Tau Ceti endorsement.

## Exact scope and inherited review

The complete earlier review is copied unchanged under `baseline187/`. Its original manifest is `afc66176571c99fc2cbac88c6dd691a60b5fa0123402d247407eb35485598e87`; its verdict is `e5576e37a87e81bf6b1b58b6b6dc901368227e9b21fd20bacd4124650510fad6`. That report, its individual assessment of all 35 contracts, all 38 sources, primary target/manuscript evidence, pinned Tau Ceti standards, bounded theorem-reuse searches, and original local evidence retain their original scope. Copying them here does not turn their old source approval into an unrecorded approval of the later repair.

I compared every reviewed source hash with source187, the current development directory, the immutable local204 snapshot, and the current package. Exactly one of the 38 proof files changes: `NLA/NM04/AnalyticBasics.lean`, now SHA256 `7105ee575ec4c24f1617485bf841426fe5042e282f4c49e49b8d9340712bea28`. The frozen Definitions, Challenge, Comparator contract list, statement headers, numerical plan, and source-correspondence file remain exact. The original freeze remains `9f81c6ce7f27cf17bcc12df5715928fd2e5220fbfad94b1867e4bb1fe84d73f2`. The complete Solution import closure still contains 38 modules and excludes both Challenge and diagnostic modules. All 35 literal theorem headers still match their independent frozen specifications. The original unrestricted positive rectangular-matrix target is preserved.

The original findings F01–F05 remain closed. Their relevant implementation and explanatory comments are byte-identical to the approved source187. This review adds no new exception to their resolution.

## The source change and mathematical neutrality

I read all of current `AnalyticBasics.lean` and the complete source187-to204 diff. The only insertion is a named `FrozenDerivativeInstance` section, an explanatory comment, two existing-instance attribute commands, and its closing `end`. The section encloses exactly C04, `potential_line_derivative`. Removing these exact inserted blocks recovers the previously approved file byte for byte. Its statement and entire proof body, including finite exponential/logarithmic differentiation, nonzero row-partition argument, and rearrangement into the exact column imbalance, are unchanged.

The section registers `ContinuousMul.to_continuousSMul` locally and disables `IsModuleTopology.toContinuousSMul` during that section. These are existing Mathlib constructions of `ContinuousSMul`, which is a `Prop` class asserting continuity of the already specified scalar multiplication and topologies. The selected multiplication-continuity construction does not change the real field, matrix entries, line being differentiated, potential, derivative value, or hypotheses. It introduces no assumption or axiom. `HasDerivAt` takes this continuity witness as an implicit parameter, so two proofs of the same continuity property can appear differently in a structural expression comparison even though the mathematical derivative assertion is the same.

I checked the subtle scope question directly in the installed Lean v4.33.1 sources. The instance attribute eraser uses `instanceExtension.modifyState`. This extension is a `SimpleScopedEnvExtension`; its `modifyState` changes the top state only, and `popScope` restores the preceding state. The command elaborator pushes and pops these scopes when entering and leaving the section. Thus `attribute [-instance]` here is restored at the named section's end; it is not a permanent removal from later declarations or importing files. The explicit local registration is likewise scoped. The section closes before the file's axiom and kernel-trust reports. Relevant Lean and pinned Mathlib primary source copies and hashes are retained under `evidence/primary/`.

Under the previously pinned Tau Ceti rubrics, this is an appropriate narrow repair: it reuses an existing proved instance, documents the reason and scope, preserves theorem generality, and adds no computation or proof workaround. Attribution and the original mathematical/code authorship remain unchanged. No additional library search is needed for a repair containing no new mathematical lemma; the bounded reuse assessment of the full proof remains in the baseline report.

## Actual local204 evidence

The retained coordinator completion record is SHA256 `4063492a265402d4c9cf50d6019911f00d939d294d44702f966975119a7c3e6d`. I inspected all eight fresh module commands and complete logs: AnalyticBasics, Coercivity, Minimum, Stationary, ScalingExistence, SinkhornSemantics, Canonical, and Solution. Each succeeded. The other 30 modules use exact source/dependency/output-matched successful local outputs. This is not 38 fresh compiler invocations. The receipt records one local compiler process, one thread, and a 4096 MiB limit. Its serial driver is byte-identical to the driver retained in my earlier review.

The replayable verifier authenticates the original receipt/log hashes and the recursive successful reuse origins for all 38 modules. It checks exact transitive source identities and direct dependency output hashes. All 35 final exported theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the successful Solution execution contains all corresponding `#assert_trust kernel` commands. These are evidence of root's actual macOS Lean run. I did not rerun the compiler, and neither hashing nor logs make these an unforgeable attestation.

## Actual local205 type comparison and earlier failures

The diagnostic comparison record is SHA256 `220012b2101b1167db78d3bb0e07ae90ede3b3f2021d1b57535e5ce3ceb4fa2f`, and explicitly references the exact local204 completion record. I read its generator and comparison scripts, both diagnostic source modules, both complete fresh diagnostic logs, and the relevant raw expression representations. The specification observer retains the frozen Challenge text, adds an `import Lean`, and appends the observation code. The proof observer imports the same two proof entrypoint dependencies as Solution. They execute in separate compiler processes, so the intentional specification placeholders are not proof dependencies. The specification log's 35 `sorry` warnings are expected and retained; the proof diagnostic log is clean.

The observer retrieves `getConstInfo` for the exact 35 contract names. Its normalizer erases only the names of forall, lambda, and let binders; it preserves types, bodies, binder information, constants, universe parameters, and metadata. I independently recomputed the equality results from the two raw JSON arrays. Additionally, my Python verifier reconstructs binder-name erasure from each original raw expression representation and checks its tokens against the reported normalized representation, accounting only for pretty-printer whitespace changes. All 35 normalized types and universe parameter lists match. C04 now uses the frozen `ContinuousMul.to_continuousSMul` witness. This is a local elaborated-type diagnostic, not an execution of Comparator, kernel replay, or Linux isolation controls.

The failure history remains explicit. GitHub run **35269165327**, published commit `34a8bc2dd1330f2c51e496329341804eb5859d67`, completed with failure. Its candidate log ends at the C04 theorem-statement mismatch, before the candidate default-kernel replay phase. Passing regression-control examples in that job do not certify NM-04. The first local adjustment also remained insufficient: diagnostic202 still differs at exactly C04. I compared the retained historical raw dumps and preserved this failure. Neither attempt is relabeled as success by this continuation.

## Remaining gates and replay

The package snapshot I inspected has all 38 exact source204 proof bytes and candid README/state metadata describing the earlier failure and pending repaired-source checks. This is a limited observation, not a new full package or schema audit. I did not use the other referee's findings to reach this verdict. The coordinator must still integrate independent reviews and complete the final publication checks, including actual non-root Linux Comparator/default-kernel/sandbox/rejection checks on the exact published repair. No canonical status or count promotion is authorized by this packet alone.

Run the read-only verifier from any extracted copy of this packet:

```bash
python3 verify_review.py
```

To bind it to the current development directory as well:

```bash
python3 verify_review.py --check-current /private/tmp/nla-lean-next-20260915/next-proofs/NM-04
```

The manifest binds every retained payload. The verifier checks the unchanged earlier packet, the narrow source delta, original frozen headers, actual local provenance, independently reconstructed type comparisons, retained failure status, and honest approval scope. It never invokes a shell, subprocess, compiler, network call, or Comparator. Its successful execution only certifies consistency of the retained review evidence; the mathematical review above and the separate runtime gates have their own stated scope.
