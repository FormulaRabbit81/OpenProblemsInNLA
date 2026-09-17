# Padding rectangular-zero repair

The only Lean changes from padding-02 are two replacements of unqualified zero_mul/mul_zero by Matrix.zero_mul/Matrix.mul_zero, plus a comment explaining why rectangular block products need those versions. All three exact frozen headers and public gram_charpoly reuse remain unchanged. SOURCE.diff is complete.

Pinned Mathlib Mathlib/Data/Matrix/Mul.lean lines 338–351 supplies these matrix-specific laws with separate row, inner, and column index types. Full source SHA256: `9ce6ecd0751e977f58fc47d6f271dff381e59868474a6955730ff07a99aa0e6b`. The existing original pinned evidence remains bound, and all 13 frozen files plus both previous handoffs remain byte-identical.

Actual root local49 failed with two remaining Gram block simplifications and no accepted Padding output. Its exact command/source/receipt/log are preserved under local49 and FAILURE-BINDING.json. Earlier API repairs are no longer errors in that log. This is failed local macOS evidence, not a Comparator run.

The source/hash/header audit passes. New Lean elaboration, axiom/trust execution, independent final proof review, and real Linux Comparator/kernel/sandbox checks are UNRUN; root owns the serial retry. No compiler/cache/shared runner/Git/frozen files were touched by this author. No complete MI-13 claim is made.

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance. Nobori, Audenaert, and repository reduction credit retained; no email.
