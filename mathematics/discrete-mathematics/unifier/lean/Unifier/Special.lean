import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 8, impossible halfway roots -/

namespace Unifier

theorem impossible_halfway_root (n k : ℕ) :
    4 * n ≠ (2 * k + 1) ^ 2 := by
  intro h
  have hm : (2 * k) * (2 * k) = 4 * (k * k) := by
    calc
      (2 * k) * (2 * k) = (2 * 2) * (k * k) := by ac_rfl
      _ = 4 * (k * k) := by rfl
  have hs : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by
    calc
      (2 * k + 1) ^ 2 = (2 * k + 1) * (2 * k + 1) := by simp [Nat.pow_succ]
      _ = (2 * k) * (2 * k) + 2 * (2 * k) + 1 := by
        simp [Nat.add_mul, Nat.mul_add]
        omega
      _ = 4 * (k * k + k) + 1 := by rw [hm]; omega
  omega

#print axioms impossible_halfway_root

/-- C3, the consequence: the square root of a natural number is never an integer plus one half. -/
theorem sqrt_ne_half_integer (n : ℕ) (k : ℤ) : Real.sqrt n ≠ (k : ℝ) + 1 / 2 := by
  intro h
  have hsq : ((k : ℝ) + 1 / 2) ^ 2 = n := by
    rw [← h]
    exact Real.sq_sqrt (Nat.cast_nonneg n)
  have hz : (((4 * (n : ℤ)) : ℤ) : ℝ) = (((4 * (k * k + k) + 1) : ℤ) : ℝ) := by
    push_cast
    nlinarith [hsq]
  have hz' : 4 * (n : ℤ) = 4 * (k * k + k) + 1 := by exact_mod_cast hz
  omega

#print axioms sqrt_ne_half_integer

end Unifier
