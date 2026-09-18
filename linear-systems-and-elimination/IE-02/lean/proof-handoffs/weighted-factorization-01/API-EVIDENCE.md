# Exact weighted scalar factorization28

Implements approved scalar plan steps8-14. The private unweighted helper uses
Nat.strong_induction_on on the degree bound with the entire finite family
generalized. It separates allzero inputs (including l=0), the proved strict27
case, and an actual common circle root. Existing common_circle_root_reduction22
gives m>=1 and all quotient degree bounds. Polynomial.degree_mul_le_of_le and
degree_X_sub_C reconstruct degree<=m; extended degree retains zero quotients.
The circle identity multiplies by |z-zeta|^2 and moves that scalar through the
finite sum. It never cancels this factor, so z=zeta and repeated roots remain.

weighted_fold21 gives the actual square-root folded family, including zero
weights. Its existing degree and evaluation conclusions are reused exactly.
The final polynomial equality uses circle_reflection_square with the SAME
bound m for h and every q_j. Polynomial.eval_finsetSum (current API name),
Complex.ofReal_sum/ofReal_mul and Finset.mul_sum identify both evaluations.
Existing circle_polynomial_uniqueness20 supplies equality from the entire
infinite circle. No finite sampling, root parity, degree equality, weight-sum
normalization, nonempty-family assumption or extra certificate is introduced.

Exact27 passed actual113 with unchanged source before this implementation.
This exact28 candidate is UNRUN; root alone compiles at unchanged resources.
No compiler/cache/Git/network mutation occurred. Root's later minimax and
canonical target remain separate outstanding obligations, not counted here.
