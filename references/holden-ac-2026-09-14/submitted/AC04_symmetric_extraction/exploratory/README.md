# Exploratory search, not a mathematical certificate

`search_far.py` runs the complex numerical search described in report Section 8.2.
It requires NumPy and PyTorch. It is not called by the exact verification suite.
The stored records for 24 starts are in `../results/far_search.json` and the
corresponding execution log. No run supplied an exact decomposition with a
fully supported rank-three contraction. Numerical failure does not prove
global nonexistence, and none of these residuals is used in a theorem.
