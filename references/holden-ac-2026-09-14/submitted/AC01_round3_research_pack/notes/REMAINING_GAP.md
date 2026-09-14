# The remaining exponent-two gap

AC-01 asks for O(n^(2+epsilon)) arithmetic operations for every epsilon > 0 on arbitrary complex matrices. The statement is not merely a better fixed exponent, a faster finite-size identity, or a floating-point algorithm.

Writing M_2 for the 2-by-2 matrix-multiplication tensor, the missing statement is

    R(M_2^(⊗n)) = 4^n exp(o(n)).

The equivalent asymptotic-rank statement is asymptotic_rank(M_2) = 4. Neither is proved in this package.

The known sufficient CW route is asymptotic_rank(cw_2) = 3. The new bound 3.876919161 remains above three. No convergence-to-three theorem is supplied.

## A limit that is actually proved

The product-envelope theorem admits rho = 3.652 in every finite binary-tree scalar test covered by the stated lower estimates, when every leaf is the initial (d,t,D,H) = (108,112,328,330) state. This remains true for unbalanced trees and mixtures covered by the scalar envelopes. Thus merely increasing the depth of those tests cannot prove the sufficient CW target.

This does not forbid stronger information about the same retained tensors. Their actual spectral values may exceed the lower estimates being substituted. Identifications across branches, a smaller source upper bound, new initial exchanges, a different retained tensor, or genuinely stronger inequalities could remove the feasible assignment. The theorem says nothing about the feasibility of extending rho = 3.652 to a spectral point on all tensors.

## What a decisive additional result would have to supply

A near-dimension-rank construction for powers of M_2 would directly close AC-01. For the CW route, one needs a proof that the asymptotic rank is three. Within the present framework this requires information beyond the scalar tests proved limited here, such as a stronger relative value theorem or a new exchange with a quantitatively controlled asymptotic saving.

A claim that every finite construction admits some strict improvement is insufficient. The improvement can shrink with the tensor power, while the finite decomposition's overhead relative to its asymptotic rate may dominate the saving. An argument using such an iteration needs a uniform quantitative estimate; none is assumed here.

No numerical percentage of completion is assigned. The unresolved asymptotic step is a mathematical gap, not a count of remaining computations.
