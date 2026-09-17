# Bounded selection: three candidates

Exactly three uncovered canonical Solved IDs were compared by their complete
canonical README statements and resolution descriptions:

| Candidate | Main implementation burden | Decision |
| --- | --- | --- |
| MI-13 | Full refined complex commutator inequality, SVD and rectangular singular-value invariance; the short repository reduction depends on a substantial external theorem | Defer |
| MI-28 | Real-power functional calculus, Furuta inequalities and exterior-power log-majorization; overlaps the already identified missing machinery for MI-24 | Defer |
| MF-07 | Approximate extremal norms, finite-dimensional norm rounding, exact triangular damping, all-word expansion and a scalar exponential bound; the complete argument is supplied in the repository | Select for statements |

MF-07 is not a claim of a short or already implemented proof. Norm rounding and
the quantitative triangular comparison are substantial remaining work. It was
preferred among these three because the full mathematical proof is available
and actual product/operator-norm infrastructure can reuse accepted MF-12/MF-24
patterns. No additional candidate was screened in this bounded selection.

The full canonical MF-07 README and complete 294-line mathematical manuscript
were read. The separate historical review was also read as supporting context;
it does not replace independent review of the new formal statements or code.
`DUPLICATE-AUDIT.json` records the fresh upstream PR check and the earlier full
public-branch coverage snapshot, including their different timestamps and
absence limits.
