# MF-14: exact seven-product closure degree

Started 17 September 2026. User specifically requests the exact value of d_7,
using the NLA research prompt pack. This is a stronger follow-up to the already
resolved original equality d_7=42; it does not replace that archived statement.
Repository baseline: 393ad40047f01159595e270660acf1f2530f0cea.

Let P_7 consist of outputs obtainable from 1,x in C[x] with arbitrary free
complex linear combinations of previously computed polynomials and at most
seven multiplications. Let X_7 be its Zariski closure in the FULL coefficient
space V_128=C[x]_{<=128}. Determine exactly

    d_7=max {d in {0,...,128}: V_d subset X_7}.

An answer d requires both V_d subset X_7 and V_(d+1) not subset X_7.
Coefficient projection, exact representation, real density, or stable
coefficient recovery are different questions. High coefficients of any border
construction must tend to zero, not be discarded.

Starting evidence: Webb's archived proof establishes V_44 subset X_7 with a
simultaneous four-product border lemma and a 45-by-45 Jacobian of determinant
256. Two independent informal reviews and executable exact verifiers accompany
it. Jarlebring--Lorentzon v3 Theorem 10 states dim X_7=49. Irreducibility and
x^128 in X_7 imply d_7<=47. Thus d_7 is one of 44,45,46,47.

Principal missing claim to test first: V_45 subset X_7. If false, d_7=44;
if true, repeat for V_46 and V_47 until matching bounds are established.
Equivalently this first claim quantifies over EVERY (c_0,...,c_45) in C^46.

Budget: up to three substantive rounds, followed by meaningful independent
verification and repair; no purchases, paid jobs, publication, PR submission or
upstream status changes. The dedicated local workspace may be edited freely.
No backup switch: user has specified MF-14. Prior proofs and campaigns remain
preserved. Mathematical software available initially: Python 3.14 and NumPy;
standard-library exact arithmetic is usable. Separate agents are real sessions.

Initial independent routes: (1) degree-stratum/normal-form upper bounds;
(2) improved simultaneous border construction and continuation lower bounds;
(3) compactification/geometry of circuit spans; coordinator: exact finite-field
jet experiments on continuations and degree profiles. Additional strategies
will be tested only when they discriminate the surviving obstruction.

## Final disposition

The exact target has been resolved as d7=47. The final proof establishes
V47 subset X7 and V48 not subset X7, in full V128, with no change to the
original quantifiers or model. See proof.md and the source-bound final review.
The previously missing V45 claim was proved and superseded by V46, then V47.
