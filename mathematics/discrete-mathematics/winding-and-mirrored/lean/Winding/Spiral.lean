import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Filter.AtTopBot.Field

/-! # Winding and Mirrored, W11: the double spiral is a straight line

`a, b` real with `a ≠ 0`, `c = a + i b`, `z(t) = tanh(c t / 2)` for real `t`, and the Moebius map
`w ↦ (1 + w) / (1 - w)`. Classical; the file proves the identities used. In (b) the logarithm is
multivalued: Lean's `Complex.log` is the principal branch, so the statement is proved as
`log = c t + 2 π i m` for an integer `m`, and `log = c t` exactly when `-π < b t ≤ π`
(NOTE-2.md). -/

namespace Winding

open Complex Filter Topology

/-- `c = a + i b`. -/
noncomputable def spiralC (a b : ℝ) : ℂ := (a : ℂ) + (b : ℂ) * I

/-- `z(t) = tanh(c t / 2)`. -/
noncomputable def spiralZ (a b t : ℝ) : ℂ := Complex.tanh (spiralC a b * t / 2)

/-- The Moebius map `w ↦ (1 + w) / (1 - w)`. -/
noncomputable def mobius (w : ℂ) : ℂ := (1 + w) / (1 - w)

variable (a b : ℝ)

theorem spiralC_mul_re (t : ℝ) : (spiralC a b * t).re = a * t := by simp [spiralC]

theorem spiralC_mul_im (t : ℝ) : (spiralC a b * t).im = b * t := by simp [spiralC]

theorem norm_exp_spiral (t : ℝ) : ‖exp (spiralC a b * t)‖ = Real.exp (a * t) := by
  rw [Complex.norm_exp, spiralC_mul_re]

theorem exp_spiral_add_one_ne_zero (ha : a ≠ 0) (t : ℝ) : exp (spiralC a b * t) + 1 ≠ 0 := by
  intro h
  have h1 : exp (spiralC a b * t) = -1 := eq_neg_of_add_eq_zero_left h
  have h2 := norm_exp_spiral a b t
  rw [h1, norm_neg, norm_one] at h2
  have h3 : a * t = 0 := Real.exp_eq_one_iff (a * t) |>.1 h2.symm
  have ht : t = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h ha
    · exact h
  subst ht
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1
  have := congrArg Complex.re h1
  norm_num at this

theorem exp_spiral_half (t : ℝ) :
    exp (spiralC a b * t) = exp (spiralC a b * t / 2) * exp (spiralC a b * t / 2) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- W11(a): `cosh(c t / 2) ≠ 0` for every real `t`, so `z(t)` is defined. -/
theorem spiral_cosh_ne_zero (ha : a ≠ 0) (t : ℝ) : Complex.cosh (spiralC a b * t / 2) ≠ 0 := by
  have hE := exp_spiral_half a b t
  have hE1 := exp_spiral_add_one_ne_zero a b ha t
  set w := spiralC a b * t / 2
  have hu : exp w ≠ 0 := Complex.exp_ne_zero w
  intro h
  have h2 := Complex.two_cosh w
  rw [h, mul_zero, Complex.exp_neg] at h2
  apply hE1
  rw [hE]
  calc exp w * exp w + 1 = exp w * (exp w + (exp w)⁻¹) := by rw [mul_add, mul_inv_cancel₀ hu]
    _ = 0 := by rw [← h2, mul_zero]

/-- `z(t) = (e^{ct} - 1) / (e^{ct} + 1)`. -/
theorem spiralZ_eq (ha : a ≠ 0) (t : ℝ) :
    spiralZ a b t = (exp (spiralC a b * t) - 1) / (exp (spiralC a b * t) + 1) := by
  have hc := spiral_cosh_ne_zero a b ha t
  have hE1 := exp_spiral_add_one_ne_zero a b ha t
  have hE := exp_spiral_half a b t
  unfold spiralZ
  set w := spiralC a b * t / 2
  have hu : exp w ≠ 0 := Complex.exp_ne_zero w
  have hs : Complex.sinh w = (exp w - (exp w)⁻¹) / 2 := by
    rw [eq_div_iff two_ne_zero, mul_comm, Complex.two_sinh, Complex.exp_neg]
  have hch : Complex.cosh w = (exp w + (exp w)⁻¹) / 2 := by
    rw [eq_div_iff two_ne_zero, mul_comm, Complex.two_cosh, Complex.exp_neg]
  rw [hch] at hc
  rw [hE] at hE1 ⊢
  rw [Complex.tanh_eq_sinh_div_cosh, hs, hch, div_eq_div_iff hc hE1]
  field_simp

/-- W11(a): `z(0) = 0`. -/
theorem spiralZ_zero : spiralZ a b 0 = 0 := by
  simp [spiralZ]

/-- W11(a): `z(-t) = -z(t)`: the half-turn about the centre reverses the direction. -/
theorem spiralZ_neg (t : ℝ) : spiralZ a b (-t) = -spiralZ a b t := by
  unfold spiralZ
  rw [show spiralC a b * ((-t : ℝ) : ℂ) / 2 = -(spiralC a b * t / 2) by push_cast; ring,
    Complex.tanh_neg]

/-- W11(b): `1 - z(t) ≠ 0`. -/
theorem one_sub_spiralZ_ne_zero (ha : a ≠ 0) (t : ℝ) : 1 - spiralZ a b t ≠ 0 := by
  have hE1 := exp_spiral_add_one_ne_zero a b ha t
  rw [spiralZ_eq a b ha t]
  intro h
  rw [sub_eq_zero, eq_div_iff hE1, one_mul] at h
  have h2 : (2 : ℂ) = 0 := by linear_combination h
  norm_num at h2

/-- W11(b): `(1 + z(t)) / (1 - z(t)) = exp(c t)`: the Moebius map carries the curve to the
logarithmic spiral. -/
theorem mobius_spiralZ (ha : a ≠ 0) (t : ℝ) : mobius (spiralZ a b t) = exp (spiralC a b * t) := by
  have hd := one_sub_spiralZ_ne_zero a b ha t
  have hE1 := exp_spiral_add_one_ne_zero a b ha t
  unfold mobius
  rw [div_eq_iff hd, spiralZ_eq a b ha t]
  field_simp
  ring

/-- W11(b): the Moebius map sends the pole `-1` to `0`; its denominator vanishes exactly at the
pole `+1`, where the numerator is `2` (so `+1` goes to infinity). -/
theorem mobius_poles : mobius (-1) = 0 ∧ (∀ w : ℂ, 1 - w = 0 ↔ w = 1) ∧ (1 + 1 : ℂ) ≠ 0 := by
  refine ⟨by simp [mobius], fun w => by rw [sub_eq_zero, eq_comm], by norm_num⟩

/-- W11(b): the logarithm carries the curve to the straight line `t ↦ c t`, up to the branch:
`log((1 + z)/(1 - z)) = c t + 2 π i m` for an integer `m`. -/
theorem log_mobius_spiralZ (ha : a ≠ 0) (t : ℝ) :
    ∃ m : ℤ, Complex.log (mobius (spiralZ a b t)) = spiralC a b * t + m * (2 * Real.pi * I) := by
  rw [← Complex.exp_eq_exp_iff_exists_int, Complex.exp_log, mobius_spiralZ a b ha t]
  rw [mobius_spiralZ a b ha t]
  exact Complex.exp_ne_zero _

/-- W11(b), principal branch: `log((1 + z)/(1 - z)) = c t` when `-π < b t ≤ π`. -/
theorem log_mobius_spiralZ_principal (ha : a ≠ 0) (t : ℝ) (h1 : -Real.pi < b * t) (h2 : b * t ≤ Real.pi) :
    Complex.log (mobius (spiralZ a b t)) = spiralC a b * t := by
  rw [mobius_spiralZ a b ha t, Complex.log_exp] <;> rw [spiralC_mul_im] <;> assumption

/-- W11(c): `|(1 + z(t)) / (1 - z(t))| = exp(a t)`. -/
theorem norm_mobius_spiralZ (ha : a ≠ 0) (t : ℝ) :
    ‖mobius (spiralZ a b t)‖ = Real.exp (a * t) := by
  rw [mobius_spiralZ a b ha t, norm_exp_spiral]

/-- W11(d): the ratio at `t + d` is `exp(a d)` times the ratio at `t`. -/
theorem norm_mobius_spiralZ_step (ha : a ≠ 0) (t d : ℝ) :
    ‖mobius (spiralZ a b (t + d))‖ = Real.exp (a * d) * ‖mobius (spiralZ a b t)‖ := by
  rw [norm_mobius_spiralZ a b ha, norm_mobius_spiralZ a b ha, ← Real.exp_add]
  congr 1
  ring

/-- W11(e): `|z(t) - 1| = 2 / |exp(c t) + 1|`. -/
theorem norm_spiralZ_sub_one (ha : a ≠ 0) (t : ℝ) :
    ‖spiralZ a b t - 1‖ = 2 / ‖exp (spiralC a b * t) + 1‖ := by
  have hE1 := exp_spiral_add_one_ne_zero a b ha t
  rw [spiralZ_eq a b ha t, div_sub_one hE1,
    show exp (spiralC a b * t) - 1 - (exp (spiralC a b * t) + 1) = -2 by ring,
    norm_div, norm_neg]
  norm_num

/-- W11(e): for `a > 0` and `t > 0`, `|z(t) - 1| ≤ 2 / (exp(a t) - 1)`. -/
theorem norm_spiralZ_sub_one_le (ha : 0 < a) (t : ℝ) (ht : 0 < t) :
    ‖spiralZ a b t - 1‖ ≤ 2 / (Real.exp (a * t) - 1) := by
  rw [norm_spiralZ_sub_one a b ha.ne' t]
  have h1 : 1 < Real.exp (a * t) := Real.one_lt_exp_iff.2 (mul_pos ha ht)
  have h2 : Real.exp (a * t) - 1 ≤ ‖exp (spiralC a b * t) + 1‖ := by
    have := norm_sub_norm_le (exp (spiralC a b * t)) (-1)
    rw [norm_neg, norm_one, sub_neg_eq_add, norm_exp_spiral] at this
    exact this
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) h2

/-- W11(e), the mirror statement: for `a > 0` and `t < 0`, `|z(t) + 1| ≤ 2 / (exp(-a t) - 1)`. -/
theorem norm_spiralZ_add_one_le (ha : 0 < a) (t : ℝ) (ht : t < 0) :
    ‖spiralZ a b t + 1‖ ≤ 2 / (Real.exp (a * -t) - 1) := by
  have h := norm_spiralZ_sub_one_le a b ha (-t) (by linarith)
  rw [spiralZ_neg, show -spiralZ a b t - 1 = -(spiralZ a b t + 1) by ring, norm_neg] at h
  exact h

/-- W11(e): for `a > 0`, `z(t) → 1` as `t → +∞`. -/
theorem spiralZ_tendsto_atTop (ha : 0 < a) : Tendsto (spiralZ a b) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun t => 2 / (Real.exp (a * t) - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.exp (a * t)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha)
    have h2 : Tendsto (fun t => Real.exp (a * t) + -1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) h1
    have h4 := h2.inv_tendsto_atTop.const_mul 2
    simpa [div_eq_mul_inv, sub_eq_add_neg] using h4
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hg
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact norm_spiralZ_sub_one_le a b ha t ht

/-- W11(e): for `a > 0`, `z(t) → -1` as `t → -∞`, by (a). -/
theorem spiralZ_tendsto_atBot (ha : 0 < a) : Tendsto (spiralZ a b) atBot (𝓝 (-1)) := by
  have h := ((spiralZ_tendsto_atTop a b ha).comp tendsto_neg_atBot_atTop).neg
  have e : spiralZ a b = fun t => -(spiralZ a b (-t)) := by
    funext t
    rw [spiralZ_neg, neg_neg]
  rw [e]
  exact h

#print axioms spiral_cosh_ne_zero
#print axioms spiralZ_eq
#print axioms spiralZ_zero
#print axioms spiralZ_neg
#print axioms one_sub_spiralZ_ne_zero
#print axioms mobius_spiralZ
#print axioms mobius_poles
#print axioms log_mobius_spiralZ
#print axioms log_mobius_spiralZ_principal
#print axioms norm_mobius_spiralZ
#print axioms norm_mobius_spiralZ_step
#print axioms norm_spiralZ_sub_one
#print axioms norm_spiralZ_sub_one_le
#print axioms norm_spiralZ_add_one_le
#print axioms spiralZ_tendsto_atTop
#print axioms spiralZ_tendsto_atBot

end Winding
