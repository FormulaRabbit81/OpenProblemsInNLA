# Approved strict-reduction module split, before source

The accepted numerical obligations and steps1-9 of the sealed Schur12/14 plan
remain the implementation target. Use a small SchurEnergy.lean for the actual
Euclidean matrix action/Gram energy bridges and the scalar-valued defect.
SchurReduction.lean then constructs the finite inverse and proves exactly the
frozen strict reduction. This keeps each module within the default resources;
there is no resource override or statement/definition change.

SchurPairStep.lean is not written in this batch. Its accepted plan remains in
proof-handoffs/schur-reduction-pair-01. Root alone runs the serial compiler.
Every new source and imported project source will be bound in the final handoff.
