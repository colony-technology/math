# Lean 4 formalization

**lmtlssss🜐 · 21 November 2026**

Every theorem of the paper, W1 to W11, is proved in Lean 4.35.0 with Mathlib v4.35.0. The nine files contain 158 theorems. None uses `sorry`, `native_decide` or an added axiom. `#print axioms` reports `propext`, `Classical.choice` and `Quot.sound` for 125 of them, `propext` and `Quot.sound` for 17, `propext` alone for 15, and no axiom for 1.

| Paper | Lean declarations | File |
| --- | --- | --- |
| W1 | `cycle`, `rect`, `cycle_bijOn` | `Winding/Ring.lean` |
| W2 | `mirror`, `mirror_mirror`, `cycle_reverse` | `Winding/Ring.lean` |
| W3 | `Neighbour`, `cycle_step`, `cycle_adjacent`, `cycle_join_left`, `cycle_join_right`, `cycle_close_left`, `cycle_start`, `cycle_hamiltonian` | `Winding/Ring.lean` |
| W4 | `cycDx`, `cycDx_welldefined`, `cycDx_two_ambiguous`, `winding_dx`, `winding_dy`, `winding_dx_reverse`, `winding_dy_reverse`, `winding_number` | `Winding/Ring.lean` |
| W5 | `avg`, `parity_split`, `parity_split_charZero`, `vecMirror`, `vecMirror_involutive`, `vecMirror_meanZero`, `parity_split_rect` | `Winding/Parity.lean` |
| W6 | `divergence`, `divergence_sum`, `seamField`, `seam_divergence`, `seam_divergence_left`, `seam_divergence_right`, `seam_divergence_other`, `seam_left_sheet`, `seam_right_sheet`, `seam_sheets_pow` | `Winding/Flux.lean` |
| W7 | `chartN`, `chartS`, `chart_overlap`, `chartN_north`, `chartS_south`, `chartN_hasDerivAt`, `chartS_hasDerivAt`, `chart_deriv`, `chart_flux` | `Winding/Charts.lean` |
| W8 | `rot12`, `refl12`, `rot12_order`, `refl12_order`, `refl_rot_refl`, `dihedral12_injective`, `dihedral12_card` | `Winding/Dihedral.lean` |
| W9 | `signMap`, `signMap_comp`, `signMap_div`, `signOrbit`, `signOrbits`, `signOrbit_signMap`, `signReps_represent`, `card_signOrbit_four`, `card_signOrbit_two`, `sign_orbits`, `sign_orbits_97` | `Winding/SignOrbits.lean` |
| W10 | `Multigraph`, `Multigraph.charge`, `degree_eq_head_tail`, `charge_parity`, `charge_ne_zero_of_odd`, `charge_sum`, `charge_degree_three`, `charge_degree_three_attained`, `cornerCharge_counts`, `charge_eq_cornerCharge` | `Winding/Corner.lean` |
| W11 | `spiralZ`, `mobius`, `spiral_cosh_ne_zero`, `spiralZ_zero`, `spiralZ_neg`, `one_sub_spiralZ_ne_zero`, `mobius_spiralZ`, `mobius_poles`, `log_mobius_spiralZ`, `log_mobius_spiralZ_principal`, `norm_mobius_spiralZ`, `norm_mobius_spiralZ_step`, `norm_spiralZ_sub_one`, `norm_spiralZ_sub_one_le`, `norm_spiralZ_add_one_le`, `spiralZ_tendsto_atTop`, `spiralZ_tendsto_atBot` | `Winding/Spiral.lean` |

`cycle k j` is the two-sheet ring C(j) and `mirror k` the mirror μ, with n = 2^k. `Neighbour k` is the neighbour relation of the periodic rectangle, with the x coordinate taken modulo 2n, and `cycDx m a b` is the signed cyclic x step. `avg` is the mean of a function on a finite set. `divergence` is outflow minus inflow of an edge field on the periodic grid, and `seamField` is the constant field with the seam pulse. `Multigraph` is a finite graph without loops, and `Multigraph.charge` counts heads minus tails at a vertex for a choice of directions. `signMap` is one of the four sign mirrors, and `signOrbits` is the set of their orbits on the pairs with nonzero divisor. `spiralZ a b t` is tanh(ct/2) with c = a + ib, and `mobius w` is (1 + w)/(1 − w). `Winding/Hilbert.lean` is the Hilbert file of the Unifier paper, unchanged, in namespace `Unifier`. Every other declaration is in namespace `Winding`, and the lemmas of W10 on multigraphs are in `Winding.Multigraph`.

## Rebuild

```sh
lake exe cache get
lake build Winding
lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` prints the axioms of every declaration in the table. A build from the sources alone on 21 November 2026 completed 2,751 jobs with exit status 0.

## Statements as compiled

### W1, every cell once

`Winding.cycle_bijOn`, `Winding/Ring.lean`, line 38

```lean
theorem cycle_bijOn (k : ℕ) : Set.BijOn (cycle k) {j | j < 2 * 4 ^ k} (rect k)
```

```text
'Winding.cycle_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W2, the mirror reverses the traversal

`Winding.mirror_mirror`, `Winding/Ring.lean`, line 99

```lean
theorem mirror_mirror (k : ℕ) (p : ℕ × ℕ) (hp : p ∈ rect k) : mirror k (mirror k p) = p
```

```text
'Winding.mirror_mirror' depends on axioms: [propext, Quot.sound]
```

`Winding.cycle_reverse`, `Winding/Ring.lean`, line 107

```lean
theorem cycle_reverse (k j : ℕ) (hj : j < 2 * 4 ^ k) :
    cycle k (2 * 4 ^ k - 1 - j) = mirror k (cycle k j)
```

```text
'Winding.cycle_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W3, unit steps, closed

`Winding.cycle_step`, `Winding/Ring.lean`, line 196

```lean
theorem cycle_step (k j : ℕ) (hj : j < 2 * 4 ^ k) :
    Neighbour k (cycle k j) (cycle k ((j + 1) % (2 * 4 ^ k)))
```

```text
'Winding.cycle_step' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.cycle_hamiltonian`, `Winding/Ring.lean`, line 211

```lean
theorem cycle_hamiltonian (k : ℕ) :
    Set.BijOn (cycle k) {j | j < 2 * 4 ^ k} (rect k) ∧
    ∀ j, j < 2 * 4 ^ k → Neighbour k (cycle k j) (cycle k ((j + 1) % (2 * 4 ^ k)))
```

```text
'Winding.cycle_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W4, winding

`Winding.winding_number`, `Winding/Ring.lean`, line 406

```lean
theorem winding_number (k : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range (2 * 4 ^ k), stepDx k j) / ((2 * 2 ^ k : ℕ) : ℤ) = 1 ∧
    ∑ j ∈ Finset.range (2 * 4 ^ k), stepDy k j = 0 ∧
    (∑ j ∈ Finset.range (2 * 4 ^ k), revDx k j) / ((2 * 2 ^ k : ℕ) : ℤ) = -1 ∧
    ∑ j ∈ Finset.range (2 * 4 ^ k), revDy k j = 0
```

```text
'Winding.winding_number' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.cycDx_two_ambiguous`, `Winding/Ring.lean`, line 244

```lean
theorem cycDx_two_ambiguous : (0 + 1) % 2 = 1 ∧ (1 + 1) % 2 = 0
```

```text
'Winding.cycDx_two_ambiguous' does not depend on any axioms
```

### W5, mirror parity split

`Winding.parity_split`, `Winding/Parity.lean`, line 52

```lean
theorem parity_split (h2 : (2 : K) ≠ 0) (hX : (Fintype.card X : K) ≠ 0)
    (M : (X → V) →ₗ[K] (X → V)) (hMM : ∀ F, M (M F) = F)
    (hM0 : ∀ F, avg K F = 0 → avg K (M F) = 0) (F : X → V) :
    let h : X → V := fun _ => avg K F
    let G := F - h
    let m := (2 : K)⁻¹ • (G - M G)
    let k := (2 : K)⁻¹ • (G + M G)
    F = m + k + h ∧ M m = -m ∧ M k = k ∧ avg K m = 0 ∧ avg K k = 0
```

```text
'Winding.parity_split' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.parity_split_rect`, `Winding/Parity.lean`, line 158

```lean
theorem parity_split_rect (k : ℕ) (F : Rect k → ℚ × ℚ) :
    let h : Rect k → ℚ × ℚ := fun _ => avg ℚ F
    let G := F - h
    let m := (2 : ℚ)⁻¹ • (G - vecMirror k G)
    let kk := (2 : ℚ)⁻¹ • (G + vecMirror k G)
    F = m + kk + h ∧ vecMirror k m = -m ∧ vecMirror k kk = kk ∧ avg ℚ m = 0 ∧ avg ℚ kk = 0
```

```text
'Winding.parity_split_rect' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W6, mirror-return flux

`Winding.divergence_sum`, `Winding/Flux.lean`, line 25

```lean
theorem divergence_sum {m n' : ℕ} [NeZero m] [NeZero n'] (E : EdgeField m n') :
    ∑ v, divergence E v = 0
```

```text
'Winding.divergence_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.seam_divergence`, `Winding/Flux.lean`, line 73

```lean
theorem seam_divergence (c q : ℚ) (v : ZMod (2 * n) × ZMod n) :
    divergence (seamField n c q) v =
      (if v = seamLeft n then q else 0) - (if v = seamRight n then q else 0)
```

```text
'Winding.seam_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.seam_left_sheet`, `Winding/Flux.lean`, line 95

```lean
theorem seam_left_sheet (c q : ℚ) :
    ∑ v ∈ Finset.univ.filter (fun v : ZMod (2 * n) × ZMod n => v.1.val < n),
      divergence (seamField n c q) v = q
```

```text
'Winding.seam_left_sheet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W7, two charts

`Winding.chart_overlap`, `Winding/Charts.lean`, line 19

```lean
theorem chart_overlap (n u : ℝ) : chartN n u - chartS n u = n
```

```text
'Winding.chart_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.chart_deriv`, `Winding/Charts.lean`, line 54

```lean
theorem chart_deriv (n u : ℝ) :
    deriv (chartN n) u = -n / 2 ∧ deriv (chartS n) u = -n / 2
```

```text
'Winding.chart_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.chart_flux`, `Winding/Charts.lean`, line 59

```lean
theorem chart_flux (n : ℝ) : ∫ _ in (-1 : ℝ)..1, n / 2 = n
```

```text
'Winding.chart_flux' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W8, twelve sectors

`Winding.rot12_order`, `Winding/Dihedral.lean`, line 32

```lean
theorem rot12_order : orderOf rot12 = 12
```

```text
'Winding.rot12_order' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.refl_rot_refl`, `Winding/Dihedral.lean`, line 59

```lean
theorem refl_rot_refl : refl12 * rot12 * refl12 = rot12⁻¹
```

```text
'Winding.refl_rot_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.dihedral12_injective`, `Winding/Dihedral.lean`, line 69

```lean
theorem dihedral12_injective : Function.Injective dihedral12
```

```text
'Winding.dihedral12_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W9, sign mirrors on division modulo a prime

`Winding.signMap_div`, `Winding/SignOrbits.lean`, line 39

```lean
theorem signMap_div {p : ℕ} [Fact p.Prime] (x : ZMod p × ZMod p) :
    (signMap (true, false) x).1 / (signMap (true, false) x).2 = -(x.1 / x.2) ∧
    (signMap (false, true) x).1 / (signMap (false, true) x).2 = -(x.1 / x.2) ∧
    (signMap (true, true) x).1 / (signMap (true, true) x).2 = x.1 / x.2
```

```text
'Winding.signMap_div' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.sign_orbits`, `Winding/SignOrbits.lean`, line 340

```lean
theorem sign_orbits (hp2 : p ≠ 2) :
    (divDomain p).card = p * (p - 1) ∧
    (∀ O ∈ signOrbits p, O.card = 4 ∨ O.card = 2) ∧
    ((signOrbits p).filter (fun O => O.card = 4)).card = (p - 1) ^ 2 / 4 ∧
    ((signOrbits p).filter (fun O => O.card = 2)).card = (p - 1) / 2 ∧
    (signOrbits p).card = (p ^ 2 - 1) / 4 ∧
    (signReps p).card = ((p + 1) / 2) * ((p - 1) / 2)
```

```text
'Winding.sign_orbits' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.sign_orbits_97`, `Winding/SignOrbits.lean`, line 391

```lean
theorem sign_orbits_97 :
    (divDomain 97).card = 9312 ∧
    (signOrbits 97).card = 2352 ∧
    ((signOrbits 97).filter (fun O => O.card = 4)).card = 2304 ∧
    ((signOrbits 97).filter (fun O => O.card = 2)).card = 48
```

```text
'Winding.sign_orbits_97' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W10, an odd corner is never neutral

`Winding.Multigraph.charge_ne_zero_of_odd`, `Winding/Corner.lean`, line 76

```lean
theorem charge_ne_zero_of_odd (o : E → Bool) (v : V) (h : G.degree v % 2 = 1) :
    G.charge o v ≠ 0
```

```text
'Winding.Multigraph.charge_ne_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.Multigraph.charge_sum`, `Winding/Corner.lean`, line 84

```lean
theorem charge_sum [Fintype V] (o : E → Bool) : ∑ v, G.charge o v = 0
```

```text
'Winding.Multigraph.charge_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.cornerCharge_counts`, `Winding/Corner.lean`, line 219

```lean
theorem cornerCharge_counts :
    #{c : Fin 3 → Bool | cornerCharge c = 3} = 1 ∧
    #{c : Fin 3 → Bool | cornerCharge c = 1} = 3 ∧
    #{c : Fin 3 → Bool | cornerCharge c = -1} = 3 ∧
    #{c : Fin 3 → Bool | cornerCharge c = -3} = 1 ∧
    Fintype.card (Fin 3 → Bool) = 8
```

```text
'Winding.cornerCharge_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.Multigraph.charge_eq_cornerCharge`, `Winding/Corner.lean`, line 247

```lean
theorem charge_eq_cornerCharge (o : E → Bool) (v : V) (h : G.degree v = 3) :
    ∃ e : Fin 3 → E, Function.Injective e ∧
      (∀ x, (G.fst x = v ∨ G.snd x = v) ↔ ∃ i, e i = x) ∧
      G.charge o v = cornerCharge (fun i => decide (G.head o (e i) = v))
```

```text
'Winding.Multigraph.charge_eq_cornerCharge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### W11, the double spiral is a straight line

`Winding.spiralZ_neg`, `Winding/Spiral.lean`, line 95

```lean
theorem spiralZ_neg (t : ℝ) : spiralZ a b (-t) = -spiralZ a b t
```

```text
'Winding.spiralZ_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.mobius_spiralZ`, `Winding/Spiral.lean`, line 111

```lean
theorem mobius_spiralZ (ha : a ≠ 0) (t : ℝ) : mobius (spiralZ a b t) = exp (spiralC a b * t)
```

```text
'Winding.mobius_spiralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Winding.log_mobius_spiralZ_principal`, `Winding/Spiral.lean`, line 133

```lean
theorem log_mobius_spiralZ_principal (ha : a ≠ 0) (t : ℝ) (h1 : -Real.pi < b * t) (h2 : b * t ≤ Real.pi) :
    Complex.log (mobius (spiralZ a b t)) = spiralC a b * t
```

```text
'Winding.log_mobius_spiralZ_principal' depends on axioms: [propext, Classical.choice, Quot.sound]
```
