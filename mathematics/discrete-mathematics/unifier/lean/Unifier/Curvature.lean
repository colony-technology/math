import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp

/-! # The Unifier: T25, dial curvature and the straight limit -/

namespace Unifier

noncomputable def dialCurvature (n : ℕ) : ℝ := (2 * Real.pi) / (n : ℝ)

noncomputable def dialTolerance (n : ℕ) : ℝ := 1 / (2 * (n : ℝ))

/-- The dial with `n` ticks at unit spacing has circumference `n`, so its radius is `n/(2π)`. -/
noncomputable def dialRadius (n : ℕ) : ℝ := (n : ℝ) / (2 * Real.pi)

/-- T25: the circle of radius `dialRadius n` has circumference `n` (unit tick spacing). -/
theorem dial_circumference (n : ℕ) : 2 * Real.pi * dialRadius n = n := by
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  unfold dialRadius
  field_simp

/-- T25: its curvature, the inverse radius, is `κ_n = 2π/n`. -/
theorem dial_curvature_inverse_radius (n : ℕ) : dialCurvature n = 1 / dialRadius n := by
  unfold dialCurvature dialRadius
  rw [one_div_div]

theorem dial_curvature_relation (n : ℕ) (hn : 0 < n) :
    dialTolerance n = dialCurvature n / (4 * Real.pi) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold dialCurvature dialTolerance
  field_simp [hn0, hp]
  ring

theorem dial_tolerance_positive (n : ℕ) (hn : 0 < n) :
    0 < dialTolerance n := by
  unfold dialTolerance
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem dial_tolerance_straight_limit :
    Filter.Tendsto (fun n : ℕ => dialTolerance n)
      Filter.atTop (nhds (0 : ℝ)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hm := (tendsto_const_nhds.mul hlim :
      Filter.Tendsto (fun n : ℕ => (1/2 : ℝ) * (n : ℝ)⁻¹)
        Filter.atTop (nhds ((1/2 : ℝ) * 0)))
  convert hm using 1 <;> simp [dialTolerance, div_eq_mul_inv, mul_comm, mul_left_comm]

#print axioms dial_circumference
#print axioms dial_curvature_inverse_radius
#print axioms dial_curvature_relation
#print axioms dial_tolerance_positive
#print axioms dial_tolerance_straight_limit
end Unifier
