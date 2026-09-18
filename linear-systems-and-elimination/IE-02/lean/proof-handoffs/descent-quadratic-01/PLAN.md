# IE-02 descent quadratic identity: pre-code plan

Prove exactly the frozen descent_quadratic_expansion contract for every dimension (including zero), every complex T,D and vector x, and every real epsilon (including negative/zero). No extra numerical hypotheses or interval computation.

Expose the genuine Euclidean matrix linear map and use map_sub/map_smul to identify the action of T minus real epsilon times D. Apply Mathlib norm_sub_sq over the complex inner product space. Expand inner_smul_right; the real part of multiplication by ofReal epsilon is epsilon times the original real part. Expand norm_smul and norm ofReal. Squaring abs epsilon gives epsilon squared; ring closes the exact symbolic identity.

Use only the frozen Definitions and pinned primary Mathlib norm/inner APIs. Kernel LeanCert trust assertions inspect the exported theorem; the existing genuinely consumed positive-half certificate remains in DescentSteps, not artificially added here. No frozen signature/source changes. Root writes and runs the proof; two nonauthor full reviews remain later gates.
