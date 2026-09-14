# Exploratory diagnostics — not proofs

These scripts are separated from the exact verification path. They require NumPy and PyTorch (the tangent probe requires only NumPy). They do not run when `code/verify.py` is run.

`search_variable_weights.py` attempts a complex rank-16 decomposition of P^2 together with a rank-three two-mode contraction. It normalizes the first two factor columns, permits bounded variable weight magnitudes and variable phases, and minimizes a relative tensor residual plus a relative contraction singular-value tail. `search_unit_weights.py` fixes weight magnitudes to one. Neither search supplied an exact candidate. Small singular values are not exact rank certificates.

Recorded commands:

```sh
python exploratory/search_variable_weights.py --start 0 --count 4 --iterations 1600 --noise .12
python exploratory/search_unit_weights.py --start 20 --count 3 --iterations 2000 --noise .08
python exploratory/tangent_probe.py
```

There are seven recorded local optimization starts, not an exhaustive search. Their numerical residuals, conditioning information, and weight ranges are recorded under `results/exploratory`. The bounded-weight and initialization choices limit what the searches explore. The residual objectives can approach degenerate or ill-conditioned configurations; that is not a proof of an admissible full-support contraction.

The tangent probe builds the coefficient Jacobian of the rank-one summation map at the standard product decomposition. Its ranks over the three recorded finite fields are 26 for one copy and 384 for two copies. These modular results are diagnostic only: they are not a proof of the characteristic-zero fiber dimension, integrability of tangent vectors, or existence of a new decomposition. No tangent-space dimension claim is used in the report.

The exploratory records are not intended as evidence that the required nonhierarchical decomposition does not exist. Versions and floating-point implementation details may affect local optimizer trajectories.
