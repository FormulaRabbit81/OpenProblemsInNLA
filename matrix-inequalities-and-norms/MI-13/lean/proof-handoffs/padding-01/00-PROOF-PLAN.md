# Padding proof plan before source

The accepted MI-13 frozen contracts quantify over every complex rectangular A,C : m by n and B : n by m, including m=0 or n=0. The square padding is exactly the frozen Fin-sum reindexing of the off-diagonal zero block. No target, definition, pin, resource setting, or existing proof file is changed.

The three exact obligations are: preserve the alternating triple product under this padding; preserve the actual Euclidean entry norm and continuous Euclidean operator norm; preserve the full decreasing nonnegative zero-extended singular-value sequence at every natural index. Repeated singular values and the zero matrix are included without generic-rank assumptions.

1. Calculate the alternating triple product in Sum-index block matrices and transport it by the pinned Matrix.reindexRingEquiv.
2. Reindex the two entry-energy sums bijectively. Splitting the Sum indices leaves precisely the original rectangular entry-energy sum. Norm nonnegativity converts equality of squares to equality of norms.
3. Identify the Gram endomorphism with toEuclideanLin of the conjugate-transpose product. The padded Gram matrix is block diagonal, so its characteristic polynomial is the original Gram characteristic polynomial multiplied by X to the number of added domain coordinates.
4. Use the pinned self-adjoint spectral theorem's sorted real roots to identify the ordered eigenvalue list. Multiplication by X adds exactly that many zero roots with multiplicity. Nonnegativity puts these zeros after the original list, including repeated zeros. Natural-index list lookup with default zero gives equality of squared singular values at every index; nonnegativity then gives equality of singular values.
5. The separately authored operator_norm_semantics identifies the genuine CLM norm with singular value zero. Apply the singular-value padding result at index zero to finish the two operator-norm equalities.

This is source-only authoring. This agent does not run Lean, Lake, cache tools, Git, or the shared runner. Root alone may compile the sealed candidate serially with one thread and 4096 MiB. All compiler, axiom, trust, and Comparator results for this new module are UNRUN until actual root evidence exists. The whole MI-13 canonical target remains outside this handoff's scope.

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance. Nobori, Audenaert, and repository reduction attribution are retained. No email is included.
