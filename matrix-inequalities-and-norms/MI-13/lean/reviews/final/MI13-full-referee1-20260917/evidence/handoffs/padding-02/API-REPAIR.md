# Repair API bindings

The unchanged pinned API declarations used for reindexRingEquiv, charpoly_reindex, Multiset.map_replicate, coe_replicate, and coe_add are bound by padding-01/PRIMARY-BINDINGS.json; this packet binds that record and original manifest by SHA256. No new external library API or pin is introduced. The root requested reuse of the existing project theorem below rather than a duplicate proof.

UnitaryInvariance.lean SHA256 `bd825d92218cf9b947bad95d34ba6f45bc37b29a0fa5246cd929a9a00889dae8`:

```lean
theorem gram_charpoly {m n : ℕ} (A : Rect m n) :
    ((euclideanLin A).adjoint ∘ₗ euclideanLin A).charpoly =
      (A.conjTranspose * A).charpoly := by
  have hg : (euclideanLin A).adjoint ∘ₗ euclideanLin A =
      Matrix.toEuclideanLin (A.conjTranspose * A) := by
    rw [euclideanLin, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    exact (Matrix.toLpLin_mul 2 2 2 A.conjTranspose A).symm
  rw [hg, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]

```

The two Frobenius applications reuse `(frobenius_semantics A).2.2.1`, keeping the actual frozen Frobenius object in the square comparison. The reindex `change` commands expose two definitionally identical bundled/unbundled views, following the same wrapper exposure already accepted for padding_product in local45. Sequential `rw` maps the replicate before `coe_replicate` can rewrite its argument into a coerced list.
