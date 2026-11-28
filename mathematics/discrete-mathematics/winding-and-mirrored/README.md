# Winding and Mirrored: Exact Two-Sheet Geometry on the Hilbert Ring

**🜘lmtlssss🜐 · 28 November 2026 · Version 1.1.0**

Mathematics / Discrete mathematics

[Paper](https://github.com/colony-technology/math/releases/download/winding-and-mirrored-v1.0.0/paper.pdf) · [DOI](https://doi.org/10.5281/zenodo.24618375)

The Hilbert map of order k and its mirror image join into one closed Hamiltonian cycle of the periodic 2^(k+1) × 2^k rectangle. The first sheet is traversed forward and the mirrored sheet backward. Every cell occurs once, every step is a unit step, and for every k ≥ 1 the cycle winds once around the periodic direction. The mirror carries the cycle onto its reversal, which winds once in the opposite sense.

The other parts are exact statements with proofs:

- a vector field on the ring is the sum of its torsion (the mirror-odd part), its drive (the mirror-even part) and its retained global component (the mean);
- one half of a dipole and the return field: a pulse q across the seam has divergence +q on one sheet and −q on the mirrored sheet;
- in a network of magnets, every corner where an odd number of magnets meet carries a nonzero charge, and the charges sum to zero; where three meet, the charge is ±1 or ±3;
- the two-chart potentials of the Wu–Yang monopole differ by ν on the overlap and have the same curvature;
- a rotation and a mirror of twelve sectors generate 24 distinct maps;
- the two sign mirrors on division modulo an odd prime p have (p² − 1)/4 orbits, which is 2,352 orbits on the 9,312 pairs at p = 97;
- the Möbius map w ↦ (1 + w)/(1 − w) carries the double spiral z = tanh(ct/2) to the logarithmic spiral e^(ct), and a logarithm carries it to the straight line t ↦ ct.

## Files

`paper.tex` contains every definition and theorem with its complete proof. Each theorem carries its statement identifier, W1 to W11. `verify.py` is a standard-library script that checks the finite content independently with exact integer and rational arithmetic. `evidence/verification.json` records the result of its last run. `lean/` holds the Lean 4 proof of every statement. `figures/00-cover-4k.png` is the figure, and `visual/` holds the Blender script that builds it and the record of its checks.

## Reproduce

```sh
python3 verify.py
make paper
cd lean && lake exe cache get && lake build Winding
```

`verify.py` prints one line per statement and exits non-zero on any failure. It checks the ring and its winding for k up to 8, which is 131,072 cells at k = 8, and the seam divergence on every grid 2n × n with n up to 32. It counts the sign-mirror orbits by enumeration for all 45 odd primes below 200, and it checks the corner charges on all 37,440 orientations of four small networks. W11 is checked through the identity (1 + z)/(1 − z) = u on 591 Gaussian rationals. `make paper` runs xelatex, or tectonic if xelatex is absent.

## Formal verification

Every statement, W1 to W11, is proved in Lean 4.35.0 with Mathlib v4.35.0 in `lean/`: 158 theorems in nine files. One of the files, `Winding/Hilbert.lean`, is the Hilbert file of the Unifier paper, unchanged. `lake build Winding` rebuilds them. None uses `sorry`, `native_decide` or an added axiom, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`, or no axiom. The paper's last section lists the declarations for each statement. A build from the sources alone on 21 November 2026 completed 2,751 jobs with exit status 0.

## Figure

The native Blender scene shows Theorem W11 as a lattice of dots. Row 0 is the curve z(t) = tanh(ct/2) with c = 1/3 + i, at the equal steps t = jπ/20. Rows 1 to 11 are the same curve turned about the two poles ±1 by the angles 2πm/12, so that (1 + z)/(1 − z) = e^(2πim/12) e^(ct). In the coordinate L = log((1 + z)/(1 − z)) the twelve rows are a square lattice, and Re L is the logarithm of the ratio of the distances to the two poles. The two discs are the dots with |Re L| ≥ π/3, and their outermost dots lie on the two circles of Apollonius where that ratio is e^(π/3) and e^(−π/3). Between the discs only row 0 is drawn. It is the S, and it enters each disc as its outer row. The radius of a dot is a fixed fraction of the local lattice step, so the dots shrink into the poles with their spacing. The half-turn z ↦ −z carries the picture onto itself. `visual/build_scene.py` checks these relations at each of the 1,887 dots before it renders, and writes the numbers to `visual/evidence.json`. Nothing typed appears in the image.

## Scope

The general statements are proved in the manuscript and checked in Lean, and the executable checks supplement those proofs. The paper builds on Hilbert's curve (Hilbert, 1891), Moore's closed variant (Moore, 1900), the two-chart Wu–Yang potentials for the Dirac monopole (Wu & Yang, 1975, doi:10.1103/PhysRevD.12.3845), the dihedral group of order 24, graph-divergence conservation, and the loxodromic double spiral as the Möbius image of a logarithmic spiral (Needham, 1997, ISBN 978-0-19-853447-1). The charged corners are what the honeycomb artificial spin ice of Ladak, Read, Perkins, Cohen and Branford shows. Division modulo 97 is the task of "Are UFOs Real? Introducing Unified Factored Organizers" (arXiv:2611.11862). The paper adds the two-sheet ring as a closed Hamiltonian cycle with winding one for every size, built from the Hilbert map and its mirror. It reads the mirror as the reversal of the traversal, on the grid and on the smooth curve. It counts the sign-mirror orbits for every odd prime, and every theorem has a Lean proof.

The paper, figure and data are licensed CC BY 4.0, and the executable source MIT; see `LICENSE.md`. Cite the paper with `CITATION.cff` or `CITATION.bib`.
