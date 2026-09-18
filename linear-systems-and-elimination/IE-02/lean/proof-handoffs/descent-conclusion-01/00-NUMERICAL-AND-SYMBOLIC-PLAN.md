# Exact descent conclusions: pre-code plan

Scope: frozen descent_empty_complement, descent_nonempty_complement, and positive_gradient_descent, unchanged headers. All dimensions admitted by hn, arbitrary complex matrices, positive real gamma/beta and exactly the frozen emptyStep/gapStep. No new numerical approximation, interval subdivision, square-root estimate or eigenvalue computation.

Use the already proved Euclidean norm-attainment theorem for the perturbed operator to select one actual unit maximizing vector. It suffices to prove strict squared decrease there; this avoids introducing an extra uniform compactness estimate. For any unit x, actual action norms are bounded by M=operatorNorm T and N=operatorNorm D; squared D norm is at most L=N^2. The real inner product f=descentForm T D x obeys f>=-M*N by Complex.abs_re_le_norm and Cauchy-Schwarz.

For epsilon>0 and epsilon<=gamma/(2*(L+1)), clearing the positive denominator gives epsilon*L<gamma. If f>gamma/2 then 2*epsilon*f>epsilon*gamma, while epsilon^2*||Dx||^2<epsilon*gamma. The already proved exact quadratic expansion gives ||(T-epsilon D)x||^2<||Tx||^2<=M^2. This handles the empty complement and the high-form branch of the nonempty case.

For the complementary branch, the frozen gap premise gives ||Tx||^2<=M^2-beta. If epsilon<=1 then epsilon^2 L<=epsilon L, so C=2*M*N+L bounds the whole error correction by epsilon*C. Clearing the positive denominator in epsilon<=beta/(2*(C+1)) yields epsilon*C<beta. Thus the perturbed squared norm is again strictly below M^2. Split on actual complement membership, with unit membership available. No use of a sampled sphere or asserted oracle bound.

Use descent_step_bounds with dummy positive beta=1 only to extract the already proved empty-step bounds; the actual gap branch uses its supplied beta. All half positivity is inherited transitively from the genuine kernel LeanCert certificate. Convert squared inequality to strict norm inequality with nonnegative norms. Finally positive_gradient_descent splits the actual complement into empty/nonempty, uses the proved compact gap in the nonempty case, and returns the exact frozen step.

The frozen hne premise (and nonempty hK in its conditional-bound theorem) can be redundant for these stronger implications; retain it without dummy uses. All13 frozen files are unchanged. Root implements and compiles serially; independent proof review and final Linux Comparator remain separate required gates. This plan is not a proof or successful execution claim.
