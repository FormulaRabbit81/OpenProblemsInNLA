# Shared circle reflection-square helper

Implements accepted scalar plan step1 only. The original fixed-bound
reflection_evaluation19 gives conjReflect m p evaluated at every nonzero
circle point. Polynomial.eval_mul and complex commutativity move z^m outside.
Complex.mul_conj (Data/Complex/Basic587) and Complex.sq_norm
(Analysis/Complex/Norm150) identify the product with the exact embedded real
square norm. The zero polynomial, m=0 and slack in DegreeLE are allowed.

This helper depends only on already-proved Reflection and Definitions. It
contains no placeholder for pending reciprocal-factor26, strict27 or weighted28.
It will genuinely serve both the positive-real normalization and the final
fixed-m weighted polynomial identity. No numerical certificate, source/frozen
change, resource override, compiler, cache or Git action occurs here.
