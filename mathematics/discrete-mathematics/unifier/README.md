# The Unifier: Exact State Contraction on the Hydrostatic Inertia Plane

**🜘lmtlssss🜐 · 21 November 2026 · Version 1.0.0**

Mathematics / Discrete mathematics

[Paper](https://github.com/colony-technology/math/releases/download/unifier-v1.0.0/paper.pdf) · [DOI](https://doi.org/10.5281/zenodo.24415211)

Every function f factors as f = enc ∘ τ ∘ dec. Here dec is a surjection onto the exact contraction of f's own observations, τ is a bijection onto the retained keys, and enc is an injection. Any two such factorizations differ by unique bijections. The cost of f is the length of the trit key of its values, ⌈log₃ m⌉ for m values. That length is necessary and sufficient, and for a product of two functions it is additive up to one trit.

The retained state is the trit fork. Any ordered window of or and and decisions acts on its incoming bit in one of three ways: constant 0, identity, or constant 1. The trit records which. Concatenating windows composes their trits by an associative table with identity 1. The window has two normal forms, one in its or values and one in its and values. For one carry stage, three states are necessary and sufficient. For a binary addition position the trit is the column sum a + b = (a XOR b) + a ⊗ b, where a ⊗ b = 2ab is the native product.

The other parts are exact statements with proofs:

- the hydrostatic column, P = ρgh;
- the reverse lookup x ≡ Σ εᵢ (N/nᵢ)(x mod nᵢ) (mod N) whenever 1/N = Σ εᵢ/nᵢ;
- the dial reader's tolerance 1/(2(n_max + n_min)), which does not depend on N, against 1/(2N) for a straight scale;
- the Hilbert coordinate, a bijection onto the 2^k × 2^k grid with adjacent consecutive cells;
- a straight scale's Lyapunov exponent, log n;
- the closed dial's reader, a retraction onto its ticks with tolerance κₙ/(4π).

## Files

`paper.tex` contains every definition and theorem with its complete proof. Each theorem carries its statement identifier, T1 to T25 and C1 to C5. `verify.py` is a standard-library script that checks the finite content independently with exact integer and rational arithmetic. `evidence/verification.json` records the result of its last run. `lean/` holds the Lean 4 proof of every statement. `figures/00-cover-4k.png` is the figure, and `visual/` holds the Blender script that builds it and the record of its checks.

## Reproduce

```sh
python3 verify.py
make paper
cd lean && lake exe cache get && lake build Unifier
```

`verify.py` prints one line per statement and exits non-zero on any failure. It checks every or/and window up to length 12, which is 22,369,621 windows. It also checks every concatenation of total length up to 12, 751 residue decompositions with moduli up to 30, the Hilbert map up to the 256 × 256 grid, and the cost inequalities for range sizes up to 120 × 120. `make paper` runs xelatex, or tectonic if xelatex is absent.

## Formal verification

Every statement, T1 to T25 and C1 to C5, is proved in Lean 4.35.0 with Mathlib v4.35.0 in `lean/`: 132 theorems in 17 files. `lake build Unifier` rebuilds them. None uses `sorry`, `native_decide` or an added axiom, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. The paper's last section lists the declarations for each statement. A build from the sources alone on 21 November 2026 completed 2,269 jobs with exit status 0.

## Figure

The native Blender scene shows circles that all touch at one point and shrink toward it, with a chain of tangent circles around them, drawn on a dome. The floor below carries the same figure after inversion in the touching point. There the nested circles are parallel straight lines, and the chain is one straight row of equal circles. A thread joins each contact point on the dome to its contact point on the floor, and every thread lies on a line through the touching point. `visual/build_scene.py` computes each circle and checks 1,769 exact rational facts about the configuration before it renders. `visual/evidence.json` records the checks. The configuration is the author's picture for this paper, and no theorem depends on it.

## Scope

The general statements are proved in the manuscript and checked in Lean, and the executable checks supplement those proofs. The paper names the established parts: quotient constructions and Nerode-style minimisation, the canonical factorization of a map through its image, the Chinese remainder composition, Hilbert's curve, generate and propagate in carry look-ahead, and the alternating split of AND-OR paths. Its contribution is the frame that holds them. The factorization is read as surface gauge, trit-key path and pressure inversion, and cost is the length of the trit key. The trit fork is the retained state of every ordered decision, for windows of any shape. The table reader is set against the straight scale. Every theorem has a Lean proof.

The paper, figure and data are licensed CC BY 4.0, and the executable source MIT; see `LICENSE.md`. Cite the paper with `CITATION.cff` or `CITATION.bib`.
