# Exact IE02 circle-polynomial uniqueness contract20 before implementation

For arbitrary complex polynomials p,q, prove the full unit circle is infinite and equality of both evaluations at every circle point implies p=q. There is no degree bound, approximation, sampled circle or finite numerical surrogate.

Use the existing Polynomial.eq_of_infinite_eval_eq theorem for uniqueness. For infinitude, inject the real interval [-1,1] into the circle by the exact upper semicircle parameter t + I*sqrt(1-t^2); its real part is exactly t. Reuse Complex.normSq_ofReal_add_I_mul_sqrt_one_sub (already genuinely reused in MI13) to prove unit modulus, and Set.Icc_infinite plus Set.infinite_of_injOn_mapsTo. Thus no trigonometric import, coefficient-root reproof, interval subdivision, or numerical computation is required. The bounded pinned-library searches located these direct components but no exact full circle-polynomial bridge; no exhaustive absence/priority claim.

Primary sources read: Analysis/Complex/Norm.lean lines380-388; Order/Interval/Set/Infinite.lean lines35-62; Data/Set/Finite/Basic.lean lines884-897; Algebra/Polynomial/Roots.lean lines145-163. All exact frozen statements/definitions/pins remain unchanged. New proof source is unrun until root serial local compile and independent review; no Linux execution or full original-target progress claim.
