import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # The Unifier: C2, segmented base-two logarithm -/

namespace Unifier

theorem segmented_log_two (x : ℝ) (e : ℤ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ e ≤ x)
    (hhi : x < (2 : ℝ) ^ (e + 1)) :
    Real.logb 2 x = (e : ℝ) + Real.logb 2 (x / (2 : ℝ) ^ e) ∧
      (1 : ℝ) ≤ x / (2 : ℝ) ^ e ∧
      x / (2 : ℝ) ^ e < 2 := by
  have hbase : (2 : ℝ) ≠ 0 := by norm_num
  have hpower : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hpower0 : (2 : ℝ) ^ e ≠ 0 := ne_of_gt hpower
  have hlogpow : Real.logb 2 ((2 : ℝ) ^ e) = (e : ℝ) := by
    unfold Real.logb
    rw [Real.log_zpow]
    exact mul_div_cancel_right₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  constructor
  · have hdiv := Real.logb_div (b := 2) (ne_of_gt hx) hpower0
    rw [hlogpow] at hdiv
    linarith
  constructor
  · exact (le_div_iff₀ hpower).2 (by simpa using hlo)
  · have hhi' : x < 2 * (2 : ℝ) ^ e := by
      rw [zpow_add_one₀ hbase] at hhi
      linarith
    exact (div_lt_iff₀ hpower).2 hhi'

#print axioms segmented_log_two
end Unifier
