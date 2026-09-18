# NM-04: independent failed Linux run and exact mismatch diagnosis

Run 35269165327, attempt 1, job 105364154708, at actual candidate commit `34a8bc2dd1330f2c51e496329341804eb5859d67` **failed**. It does not establish Comparator acceptance or default-kernel replay of NM-04. No verified-status promotion or campaign count increase is supported.

I independently inspected the downloaded GitHub run/jobs/artifact metadata, raw job logs, complete relevant phase logs, pinned Comparator implementation and root's actual local199 diagnostic outputs. I did not execute Lean, Lake, Comparator or a Linux sandbox, and edited no proof, frozen statement, checker or Git state. Previous source-review approvals remain unchanged and retain their original scopes.

## What actually ran

The metadata identifies the reviewed commit and terminal failure. The raw log records checkout of that same commit. The selection job selected NM-04 alone. The downloaded artifact's SHA256 is `f4d41f070642d1c3a69e1b46e221eed5176671c819722cf5330b93d4e462ae52`, matching the advertised digest; every one of its 12 extracted log members was checked byte-for-byte against the zip.

Challenge built successfully with 35 deliberate specification placeholders. The full Solution built successfully, and all 35 requested declarations printed only propext, Classical.choice and Quot.sound. The project Comparator phase then stopped with:

`Challenge and solution theorem statement do not match: 'NLA.NM04.potential_line_derivative'`

That phase's exit status was 1. The wrapping verification step exited 2. The NM-04 comparator.log contains neither its default-kernel replay marker nor its success marker, and no result.json was produced. Success text elsewhere in the raw job belongs to controls, not the candidate proof.

The same job did execute successful comparator regression, kernel replay probe and sandbox controls, together with expected rejection of sorry and native_decide fixtures. I read their actual logs and distinguished those fixtures from the candidate. The separate checker-controls job was skipped because the harness had not changed; that does not erase the per-project controls that actually ran.

## Exact cause

The pinned Comparator/Compare.lean at the source-lock digest `9bc34cb7de5a069a6fef7f3b13b20fea22f1d52603f74320a93d519b735ad3dd` compares theorem ConstantVal records using their names, level parameters and elaborated expressions. It does not perform definitional equality or erase proof arguments. Main.lean invokes this matching step before axiom checking and candidate default-kernel replay.

Root's successful local199 run executed two fresh diagnostic Lean modules and retained their actual source hashes, commands, exit-zero logs and all 35 type dumps. I independently compared these dumps. Every universe-parameter list matches. There are 24 literally identical type representations, ten differences confined to binder names/hygiene, and one substantive expression difference at potential_line_derivative.

Challenge elaborated its implicit real scalar-continuity witness using the existing `ContinuousMul.to_continuousSMul`; Solution's larger import environment selected `IsModuleTopology.toContinuousSMul`. I identified the fully applied subexpressions and checked that replacing only those witnesses makes all remaining C04 expression text identical. The two witnesses provide the same ordinary real scalar-continuity proposition. The pinned Mathlib definition declares ContinuousSMul as Prop, so this is a proof-irrelevant choice mathematically; it remains visibly different to Comparator's expression matching.

The ten binder-label differences are harmless for that comparison: Lean 4.33.1's Expr source explicitly defines BEq Expr using alpha equivalence and ignores binder annotations. My textual binder-only normalization of all 35 dumps is a diagnostic reflecting that documented rule, not a substitute execution of Comparator.

## Repair assessment and remaining gates

The proposed change adds a local section around C04 and locally registers the already existing `ContinuousMul.to_continuousSMul` instance. I read the precise diff. The theorem's header and proof-body text are untouched, and the section ends immediately afterward. This is an appropriate narrow way to reproduce the frozen specification's elaboration. A newly named instance wrapper would risk another expression mismatch, so using the existing declaration matters.

This packet does not approve a repaired source revision or predict the next runtime outcome. Fresh full-closure local compilation, all 35 elaborated-type checks, exact-source continuation review and a new actual Linux run remain separate gates. The root subsequently reported local201 success and scheduled local202 type diagnostics; review of those belongs to the next packet.

The actual read-only audit here passed 89 consistency/diagnosis checks. AUDIT-RUN.json retains the command and actual exit/output. verify.py is a packet integrity check only. The complete failure, its limited successful subphases and the unaccepted candidate status are preserved.
