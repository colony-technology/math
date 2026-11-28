# Verification contract

The mathematical proofs cover every case. The Lean 4 development in `lean/` checks every statement of the paper, and the executable checks supplement both.

Failure modes:

- the second sheet traversed forward, C(j) = μ(H(j − N)), in place of backward, which breaks the join and the closure;
- the mirror taken as x ↦ 2n − x in place of x ↦ 2n − 1 − x, which leaves the rectangle;
- a Hilbert quarter map that is not transposed or reflected, which breaks adjacency at the junctions;
- the x step taken as a plain difference in place of a cyclic one, which makes every closed cycle wind zero times;
- a signed x step at k = 0, where the period is 2 and +1 and −1 are the same step;
- a mean taken in a field whose characteristic divides the number of cells;
- the inflow at a cell read from v + (1, 0) in place of v − (1, 0);
- a negative remainder for x mod p, or a floating-point inverse modulo p;
- the principal logarithm taken as ct for every t, which fails once |bt| > π.

`verify.py` builds the Hilbert map of Definition 6.1 of the Unifier paper twice, by quarters and point by point, and compares the two up to k = 8. It checks the ring's bijection, mirror reversal, unit steps, join and closure for k up to 8, and its winding for 1 ≤ k ≤ 8. The parity split is checked on 24 rational fields. The seam divergence is checked on 96 random rational edge fields and 288 seam fields, on every grid 2n × n with n up to 32. The sign-mirror orbits are counted by enumeration for every odd prime below 200, and at p = 97 all 9,312 quotients are rebuilt from the 2,352 representatives. The corner charges are checked on every orientation of the complete graph on four vertices, the triangular prism, three hexagons around one vertex and the honeycomb on the 2 × 2 torus. W11 is checked with Gaussian rationals held as pairs of Fractions, through z = (u − 1)/(u + 1) and (1 + z)/(1 − z) = u, with squared norms in place of norms. The bounds of W11(e) are checked at the points u whose modulus is rational, where they can be compared exactly. The exponential law and the limits are not checked by the script; they are proved in the paper and in Lean. The run writes `evidence/verification.json`.

Three mutations run inside the script on every invocation: the second sheet traversed forward, the first Hilbert quarter left untransposed, and the x step taken as a plain difference. Each makes the corresponding check fail, and the script reports a failure if one of them passes.

The public replay uses Python's standard library. It reports exact equality on the stated finite ranges. General validity follows from the proofs.
