# Verification contract

The mathematical proofs cover every case. The Lean 4 development in `lean/` checks every statement of the paper, and the executable checks supplement both.

Failure modes:

- Python's built-in round, which rounds half to even, in place of round(y) = floor(y + 1/2);
- a floating-point base-3 logarithm in place of the integer clog;
- a negative remainder for x mod n;
- the empty OR taken as 1 or the empty AND taken as 0;
- concatenated windows read bottom stage first;
- the paired map x ↦ (f1(x), f2(x)) used in place of the product map in the cost inequality;
- a Hilbert quarter map that is not transposed or reflected, which breaks adjacency at the junctions;
- checking the normal forms from a recurrence that already assumes them;
- reporting a planted example as a complete check.

`verify.py` builds the response of every window of length up to 12 from the definition F(step :: S)(R) = step(F_S(R)). It cross-checks the tables against direct folding of each window of length up to 6. It compares every concatenation of total length up to 12 with functional composition. It checks the residue compositions on all 751 decompositions 1/N = Σ εᵢ/nᵢ with distinct moduli up to 30 and at most three dials. The tolerance and rounding statements use exact rationals. The Hilbert map is compared with an independent top-down evaluation. The run writes `evidence/verification.json`.

A mutation of the carry table, of the rounding rule, or of the first Hilbert quarter makes the corresponding check fail.

The public replay uses Python's standard library. It reports exact equality on the stated finite ranges and makes no claim about speed. General validity follows from the proofs.
