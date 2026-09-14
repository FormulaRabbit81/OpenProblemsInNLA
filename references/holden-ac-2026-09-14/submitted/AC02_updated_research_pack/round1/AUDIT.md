# Mathematical and software audit map

## Status

This is a self-audited computer-assisted research report, not an independently
refereed or formally verified solution of AC-02. No improved global rank bound
is proved. The global target and known interval remain unchanged.

## Dependency structure

1. Direct integer evaluation of 729 coefficients establishes both baseline
   identities. Attribution is separate from verification of the transcribed
   data.
2. Each forcing trace is an induction over two-monomial equations. This proves
   nonvanishing for every complex support-constrained solution, not only the
   baseline. The Sun conclusion uses 162 forced entries, not all 175 entries.
3. Pairwise triangular peeling uses only prescribed zeros and proved nonzeros.
   It gives full pairwise Khatri–Rao rank throughout the two support varieties.
4. All 153 Laderman entries are nonzero, permitting Laurent elimination.
   Integer inverses of selected exponent minors prove completeness of the
   parametrization without an unproved saturation or root-of-unity assumption.
   Four signed cancellations are supported by integer row-lattice identities.
5. Direct symbolic Laurent substitution verifies all 729 identities and all
   23 constant signatures. These are exact polynomial calculations, not tests
   at finitely many parameter values.
6. The G x S action gives actual tangent vectors, not merely abstract vectors
   in the Jacobian kernel. This is essential to the lower dimension bound.
7. Two modular minors plus JH=0 prove complex ranks 545 and 76. They do not
   transfer a finite-field tensor-rank lower bound to C.
8. Irreducibility, derivative rank, tangent upper bounds, and nonsingularity
   identify the irreducible component through Laderman. Constant nonzero
   signatures persist on its Zariski closure.
9. Independently of that component, reshuffling gives I_(n^3) = LR. Under the
   explicitly stated output-tight hypothesis L and R become square and
   RL=I, yielding the cross-block identities and the 22-slot rank profile.

## Non-implications that must remain explicit

- A zero-slot obstruction on one component is not global nonexistence.
- Nonzero slots do not make a displayed decomposition globally minimal.
- Independence of a particular Khatri–Rao matrix does not exclude a different
  collection of factors of smaller length.
- The 58 parameters include term and basis gauges; they are not 58 parameters
  of pairwise inequivalent algorithms. The six-parameter slice has only the
  explicitly stated elementary-gauge meaning.
- A path can move between components at an intersection away from Laderman.
- Output tightness is not proved for every putative rank-22 decomposition.
- Nonconvergence in numerical search is not nonexistence. A small nonzero
  residual is not an exact identity.
- No exhaustive search over arbitrary complex coefficient arrays was done.
- Passing the Python checker does not establish independent review or Lean
  verification of the algebraic-geometric reasoning.

## Remaining global target

For a lower-bound solution at 23, exclude every zero-slot point in X_23,
not only those in the component certified here. Equivalently, produce a
Nullstellensatz identity 1 in the ideal of the unrestricted rank-22 Brent
system over Q. The report gives the exact 594-variable, 729-equation target.
No such certificate is supplied.

For an upper-bound improvement, provide an exact rank-22 identity with all
coefficients represented rigorously (rational, algebraic, or another exact
complex description), verify all coefficients, and then supply a matching
lower bound to determine the minimum. The best stored numerical point does
not satisfy the identity.

## Productive scope for another research pass

The proven component obstruction means that trying to delete a slot while
remaining in the Laderman component cannot work. A substantially new next
step must address another component, a globally complete normal form, or a
new lower-bound invariant. The output-tight cross-block equations form one
concrete conditional branch: five rank-two and seventeen rank-one outputs
must satisfy all diagonal and off-diagonal identities. Classifying or
excluding that branch alone still would not settle non-tight candidates.

## Software tests run

Exact replay: PASS.
Regression tests: 7/7 PASS, including intentionally corrupted fixtures.
Stand-alone Q(i) identity checker: both baselines and the six-parameter sample
PASS. JSON coefficient floats are intentionally rejected.

The generator and replay checker share common.py. The stand-alone checker
avoids it but is authored in the same session. Assertions in the proof checker
must remain enabled. NumPy object arrays use unbounded Python integers for
large products; finite-field elimination uses a bounded prime and safe int64
products. No computer algebra simplification is trusted in the replay step.
