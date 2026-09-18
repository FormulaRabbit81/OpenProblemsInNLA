# Exact strict scalar factorization27

Implements accepted plan steps2-7. The actual effective_factor_polynomial24
and reciprocal_inside_factor26 supply the exact effective polynomial and
inside-root product including ell=0. The circle_reflection_square helper
compares their evaluations, canceling only a proved nonzero power z^ell.
At z=1, existing sumSquares_pos and the no-circle-root clause imply positive
real numerator and denominator. eq_div_iff plus Complex.ofReal_div identify
the complex kappa as the real beta=Q(1)/|h0(1)|^2; div_pos proves beta>0.
Complex.ofReal_injective/ofReal_mul recover the real identity everywhere.

The scalar rescaling is the existing weighted_fold21 specialized to Fin1.
Fin.sum_univ_one supplies its pointwise norm identity and the same theorem
supplies the degree bound. Thus no square-root algebra, root multiplicity,
Fourier expansion, reflection coefficient proof or norm bridge is duplicated.
No m>=1, l>=1 or real coefficient assumption enters the exact frozen header.

Actual111 reciprocal pairing25, inside factor26 and CircleSquares all passed
with current source hashes before this source was written; full raw logs were
read and bound in00. The target27 itself is UNRUN. Exact28 is not implemented
before root actual27 success. No compiler, cache, Git, certificate or resource
change is made in this author handoff.
