# Exact MI-13 normalized-image obligations before new proof code

The accepted numerical target is retained in the frozen NUMERICAL_TARGETS.md: the original rectangular, all-complex MI-13 inequality with its exact coefficient 2 and genuine entry-Euclidean Frobenius norm, Euclidean operator norm, and actual ordered singular values. This bounded module only supplies three frozen singular-vector contracts on every natural square dimension, including zero. It neither changes nor claims completion of that numerical target.

For a supplied full orthonormal basis v satisfying the actual Gram equations T* T v_j = s_j^2 v_j, derive the exact complex inner product identity <T v_i,T v_j> = s_j^2 <v_i,v_j>. On the subtype of positive singular indices, the normalized image is s_i^{-1} T v_i. Off the diagonal its inner product vanishes by orthonormality of v; on the diagonal it equals 1 by conjugation fixing real casts and cancellation of a nonzero positive s_i. No distinctness of singular values is used.

For s_i=0, the same Gram inner product identity gives <T v_i,T v_i>=0, so positive definiteness yields T v_i=0. Choose v from the proved ordered Gram-basis contract, extend only its positive normalized images by the proved partial-basis extension contract, and recover T v_i=s_i u_i. Positive indices cancel the inverse; all other indices have s_i=0 by nonnegativity, and both sides vanish. At dimension zero the pointwise obligations are vacuous and the existing full-basis existence/extension APIs remain applicable.

Exact exports: positive_image_orthonormal, zero_singular_image, full_singular_vector_bases. No nonempty-dimension, full-rank, distinct-value, or reality restriction is added. Root owns all compiler execution; this source-author packet is explicitly unrun.
