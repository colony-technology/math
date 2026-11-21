import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # The Unifier: T22, expansion of the straight segment -/

namespace Unifier

def straightStep (n : ℕ) (x : ℝ) : ℝ := (n : ℝ) * x

theorem straight_iterate (n t : ℕ) (x : ℝ) :
    (straightStep n)^[t] x = (n : ℝ) ^ t * x := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [straightStep, pow_succ]
      ring

theorem straight_distance (n t : ℕ) (x y : ℝ) :
    |(straightStep n)^[t] x - (straightStep n)^[t] y| =
      (n : ℝ) ^ t * |x - y| := by
  rw [straight_iterate, straight_iterate]
  have hn : 0 ≤ (n : ℝ) ^ t := pow_nonneg (Nat.cast_nonneg _) _
  calc
    |(n : ℝ) ^ t * x - (n : ℝ) ^ t * y| =
      |((n : ℝ) ^ t) * (x - y)| := by rw [mul_sub]
    _ = |(n : ℝ) ^ t| * |x - y| := abs_mul _ _
    _ = (n : ℝ) ^ t * |x - y| := by rw [abs_of_nonneg hn]

theorem straight_lyapunov (n t : ℕ) (hn : 2 ≤ n)
    (ht : 0 < t) (x y : ℝ) (hxy : x ≠ y) :
    (1 / (t : ℝ)) *
      Real.log (|(straightStep n)^[t] x -
        (straightStep n)^[t] y| / |x - y|) =
      Real.log (n : ℝ) := by
  have hdiff : |x - y| ≠ (0 : ℝ) := by
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hxy)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  rw [straight_distance]
  rw [mul_div_cancel_right₀ _ hdiff, Real.log_pow]
  field_simp [ht0]

theorem straight_lyapunov_positive (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n by omega)

theorem straight_scale_unstable (n : ℕ) (hn : 2 ≤ n)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℝ, ∃ t : ℕ,
      |x - y| < ε ∧
      1 ≤ |(straightStep n)^[t] x - (straightStep n)^[t] y| := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  obtain ⟨t, ht⟩ :=
    pow_unbounded_of_one_lt ((1 : ℝ) / δ) hn1
  refine ⟨x + δ, t, ?_, ?_⟩
  · have heq : |x - (x + δ)| = δ := by
      rw [show x - (x + δ) = -δ by ring, abs_neg, abs_of_pos hδ]
    rw [heq]
    dsimp [δ]
    linarith
  · rw [straight_distance]
    have heq : |x - (x + δ)| = δ := by
      rw [show x - (x + δ) = -δ by ring, abs_neg, abs_of_pos hδ]
    rw [heq]
    have ht' := mul_lt_mul_of_pos_right ht hδ
    have hdiv : (1 / δ) * δ = (1 : ℝ) := by field_simp [ne_of_gt hδ]
    rw [hdiv] at ht'
    exact ht'.le

#print axioms straight_iterate
#print axioms straight_distance
#print axioms straight_lyapunov
#print axioms straight_lyapunov_positive
#print axioms straight_scale_unstable

end Unifier
