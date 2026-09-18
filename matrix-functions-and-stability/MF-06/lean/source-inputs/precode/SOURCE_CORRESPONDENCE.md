# MF-06 full source and prospective statement boundary

The authoritative current source is upstream Git object `3923b68ecee13d02e732085a57b42a2e7e95ac7a`. `SOURCE-CAPTURE.json` binds the canonical README, complete solution.md/solution.tex and 34 supporting source/review files. The full solution and full mathematical review were read. The retained informal review is historical evidence and is not substituted for the two new independent statement reviews or future formal-code reviews.

The final contract, after importing exact MF05/MF07 definitions, must have this complete meaning (not yet a typechecked Lean declaration):

```lean
theorem canonical_pointwise_lower_lipschitz {d : ℕ} (hd : 1 ≤ d)
    (M : Set (NLA.MF07.Square d)) (hM : IsCompact M) (hneM : M.Nonempty) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ N : Set (NLA.MF07.Square d),
        IsCompact N → N.Nonempty →
        NLA.MF05.canonicalHausdorff M N < r →
        NLA.MF07.jointSpectralRadius M - C * NLA.MF05.canonicalHausdorff M N ≤
          NLA.MF07.jointSpectralRadius N
```

## Concrete definitions needed

- Reuse Square, EuclideanVector, applyMatrix, spectralNorm, matrixProduct, WordIn, familyGrowth and jointSpectralRadius from exact MF07 sources; use the MF05 arbitrary-radius root-limit theorem and canonical Hausdorff semantics unchanged.
- `IsProductBounded M` means `exists K>=1, forall n, familyGrowth M n<=K`, including n=0. It does not encode the final perturbation conclusion.
- `FamilyInvariant M S` means the actual linear operator of every A in M maps every x in the complex submodule S into S. Irreducibility says each such S is bottom or top; it does not supply an extremal norm.
- For a product-bounded reference, define v by the existing concrete word `productEnvelope M id 1`. Define g_n by the actual maximum/supremum of v(Px) over all length-n original words. Define p(x) as the real infimum of these g_n values. Continuity, seminorm laws, max recurrence, nonzero quotient and stability of its kernel must be proved; they cannot be assumed as structure fields.
- Define the k-th exterior matrix using `exteriorPower.map k` of the actual matrix linear map and `Module.Basis.exteriorPower` of the standard coordinate basis. Reindex the finite basis `Set.powersetCard (Fin d) k` by a fixed `Fintype.equivFin` if the existing `Square` APIs require Fin indexing. The exterior family is the actual image of M under this concrete map. Its dimension is the cardinality of the k-subset basis, proved equal to `Nat.choose d k`; positivity is needed only for 0<=k<=d.
- A block profile is a finite ordered list of positive block dimensions summing to d, together with an actual invertible change of basis and concrete diagonal/off-diagonal submatrices. No triangularization, irreducible diagonal condition or block-radius formula may appear as an unproved oracle in a structure consumed by the final theorem.
- Allocation a assigns 0<=a_i<=d_i, and its matrix is the paired tensor/Kronecker product of the actual a_i-th exterior maps of diagonal blocks of one original generator A. The same A must be used in every factor. Degree-zero components are scalar identities.

## Obligations mapped to the complete manuscript

| Stage | Full obligation | Source | Existing support / required new work |
|---|---|---|---|
| S01 | Actual all-word supremum/max/root semantics and positive scalar normalization | Sections 1–2 | Reuse MF05/MF07, add positive Hausdorff scaling |
| S02 | Product-envelope norm and g_n monotone/Lipschitz convergence to a genuine continuous seminorm | Lemma 1, first paragraphs | Reuse ProductEnvelope and Dini; prove the g_n/p properties |
| S03 | p(x)=max_A p(Ax); kernel invariant, restricted radius<1, quotient nonzero and actual quotient norm | Lemma 1 | New complete stable-kernel and quotient argument |
| S04 | Constructed stable-block norm, fixed norm equivalence, cone-preserving perturbed trajectories and product-bounded-reference lower Lipschitz | Lemma 1 | New; perturbing lower-left block must be retained |
| S05 | Scalar cross-cut and uniform transition-sum estimate for all lengths | Lemma 2 | New scalar proof, optimize as N2–N3 |
| S06 | JSR of any finite block triangular family equals the maximum of diagonal radii, preserving common-generator pairing | Section 2 | New complete block-word growth proof; zero diagonal radii included |
| S07 | Two-block paired tensor nonresonance gives product boundedness; induct to all finite blocks | Lemmas 3–4 | New; grouped prefix tensor family must retain off-diagonal terms |
| S08 | Actual finite invariant flag with irreducible quotient blocks; irreducible radius-one families are product bounded | Lemma 5, first paragraphs | New substantial theorem; Barabanov/Wirth cannot be an axiom |
| S09 | Algebraic exterior map multiplication, basis/minor identity, compact image, wordwise norm power bound and local Lipschitz map | Section 5 and (5), Section 6 (10) | Algebraic functor/basis available; geometry and coordinate bounds still new |
| S10 | Exterior representation of a triangular family is triangular on allocations with exactly the paired tensor diagonal blocks | Lemma 5, equation (7) | New universal allocation-order/sign/basis proof |
| S11 | For distinct maximal-critical-degree allocations a,b, max/min factor identity and paired tensor radius<1 | Lemma 5 (8)–(9) | New, preserving zero factors, ties, degree zero and common words |
| S12 | Exists k, 1<=k<=d, with actual exterior family radius1 and product bounded | Lemma 5 | Must prove from S06–S11 without added irreducibility/product-boundedness assumptions on M |
| S13 | Actual image Hausdorff bound, radius power domination, exterior-to-original transfer and zero/positive normalization | Section 6 | Reuse compact Hausdorff/roots; new map estimate and N5 algebra |
| S14 | Complete canonical pointwise lower Lipschitz theorem above | Theorem (1) | Only after all previous actual conclusions and two statement/proof review gates |

A theorem proving only S04, an irreducible or product-bounded subcase, a determinant/top-exterior surrogate, or the trivial zero-radius case is not a completed MF-06 verification and increases no count.

## Original attribution and external theorem gap

Epperlein–Wirth §2 Conjecture 3(P2) and §3 agree with the canonical target and state the real/complex irreducible Barabanov-norm background. Their primary page was checked directly on 17 September 2026: [arXiv:2311.18633v2](https://arxiv.org/html/2311.18633v2), especially the target at lines121–125 and norm background at lines160–165 of the retrieved HTML. That published mathematics supplies context, not an accepted Lean axiom. The source proof credits Barabanov/Wirth, Chitour–Mason–Sigalotti and Morris; retain that credit in any formalization.

The original solution author is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Preserve the source's AI-assistance and informal-review qualifications and omit his email. MF05/MF07 mathematical/code contributions retain their own source attribution.
