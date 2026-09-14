# Completion status and exact next targets

## Not resolved

No exact complex border rank for M3 has been proved. No numerical endpoint has
improved. The package is verified partial research.

## Rank-17 target

Let E be the 17-dimensional matrix plane consisting, after reordering rows, of

    [ H P R ]
    [ 0 H 0 ]
    [ 0 0 H ]

where H is arbitrary 3 x 3 and P,R are supported on rows 2,3 and columns 1,2.
Decide whether E is a limit of 17-dimensional spans of 17 rank-one matrices.
Its 35-coordinate inclusion tensor is exported in `results/pair_geometry.json`.

A positive certificate must exhibit an actual degeneration, with all unwanted
coefficients controlled. A negative certificate must hold over C and cover every
remaining parameter family and every relevant limiting scheme/arc.

## Routes now ruled out or demonstrably insufficient

The monomial Fourier ansatz is excluded exactly. Normalized cubic-pole arcs at
the 24 cyclic-root base configurations and the grid-plus-barycenter configuration
are excluded exactly. A generic open set of reduced configurations is also
excluded at cubic order, but an exceptional locus and higher poles remain.

Cactus-rank exclusion alone cannot decide the border question: an explicit
17 x 9 x 9 control tensor has border rank 17 and cactus rank at least 18.
Grouping two original factors is also insufficient: all three grouped targets
already have exact border rank 17.

## A logically decisive continuation

For a construction route, move beyond single-character monomials and the
excluded cubic base configurations; use the 35-coordinate target rather than
retesting weaker grouped tensors. Treat the first complete Laurent constant-term
identity as the success criterion, not a small residual.

For a lower-bound route, complete a complex-parameter classification of compatible
concise extensions or prove a new obstruction that rules out the exceptional
span limits. The optional basis-line enumeration has not accomplished that
classification. An 18 lower bound would still need an 18 upper certificate, or
further exclusions up to the retained 20 upper bound, to finish AC-03.
