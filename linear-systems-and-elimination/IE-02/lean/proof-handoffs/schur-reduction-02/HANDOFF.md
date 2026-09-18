# Strict reduction repair02 after actual95

Only the three observed sites changed: a commented change exposes euclideanCLM
application as euclideanLin; mul_le_mul_iff_left₀ cancels a strictly positive
RIGHT factor (pinned GroupWithZero/Defs.lean:303); and the final existential
reuses the explicit q,hq witness after obtain consumed hBtoep.

The similarly named mul_le_mul_iff_right₀ cancels a LEFT factor, so it is not
the direct spelling for this goal. The old mul_le_mul_right was a one-way
monotonicity function, not an iff. No mathematical hypothesis changed.

Actual95 passed SchurEnergy with standard three axioms and failed SchurReduction;
the full receipt and both logs are preserved. SchurEnergy remains unchanged.
No failed source output is accepted. Exact contract12, all13 frozen inputs,
trust assertions and resource settings remain fixed. Retry and independent
proof review are pending; no agent compiler or GitHub Comparator run occurred.
