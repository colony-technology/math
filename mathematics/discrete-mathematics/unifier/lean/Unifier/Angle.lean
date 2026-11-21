import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # The Unifier: T13, Mordell angular decomposition over rationals -/

namespace Unifier

theorem reverse_lookup_angle (k : ℕ) (N x : ℤ)
    (n ε : Fin k → ℤ)
    (hN : (N : ℚ) ≠ 0)
    (hn : ∀ i, (n i : ℚ) ≠ 0)
    (hunit : 1 / (N : ℚ) = ∑ i : Fin k, (ε i : ℚ) / (n i : ℚ)) :
    ∃ m : ℤ, (x : ℚ) / (N : ℚ) =
      (∑ i : Fin k, (ε i : ℚ) * ((x % n i : ℤ) : ℚ) / (n i : ℚ))
       + (m : ℚ) := by
  refine ⟨∑ i : Fin k, ε i * (x / n i), ?_⟩
  have hterm (i : Fin k) :
      (ε i : ℚ) * ((x % n i : ℤ) : ℚ) / (n i : ℚ) +
      (ε i : ℚ) * ((x / n i : ℤ) : ℚ) =
      (ε i : ℚ) * (x : ℚ) / (n i : ℚ) := by
    have heq : (x : ℚ) = ((x % n i : ℤ) : ℚ) +
        (n i : ℚ) * ((x / n i : ℤ) : ℚ) := by
      exact_mod_cast (Int.emod_add_mul_ediv x (n i)).symm
    rw [heq]
    field_simp [hn i]
  have hs : (∑ i : Fin k, (ε i : ℚ) * ((x % n i : ℤ) : ℚ) / (n i : ℚ)) +
        (∑ i : Fin k, (ε i : ℚ) * ((x / n i : ℤ) : ℚ)) =
        ∑ i : Fin k, (ε i : ℚ) * (x : ℚ) / (n i : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i
  have hcast : ((∑ i : Fin k, ε i * (x / n i) : ℤ) : ℚ) =
      ∑ i : Fin k, (ε i : ℚ) * ((x / n i : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [hcast]
  calc
    (x : ℚ) / (N : ℚ) = (x : ℚ) * (1 / (N : ℚ)) := by ring
    _ = (x : ℚ) * ∑ i : Fin k, (ε i : ℚ) / (n i : ℚ) := by rw [hunit]
    _ = ∑ i : Fin k, (ε i : ℚ) * (x : ℚ) / (n i : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := hs.symm

#print axioms reverse_lookup_angle
end Unifier
