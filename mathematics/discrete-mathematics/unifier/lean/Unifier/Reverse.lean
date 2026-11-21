import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 5, exact reverse lookup -/

namespace Unifier

theorem zodiac_reverse_mod12 (x : ℤ) :
    (x - (4 * (x % 3) - 3 * (x % 4))) % 12 = 0 := by
  omega

theorem successor_reverse_divisible (n x : ℤ) :
    n * (n + 1) ∣ x - ((n + 1) * (x % n) - n * (x % (n + 1))) := by
  refine ⟨x / n - x / (n + 1), ?_⟩
  have hr1 : x % n = x - n * (x / n) := by
    have h := Int.emod_add_mul_ediv x n
    omega
  have hr2 : x % (n + 1) = x - (n + 1) * (x / (n + 1)) := by
    have h := Int.emod_add_mul_ediv x (n + 1)
    omega
  rw [hr1, hr2]
  ring

theorem successor_reverse_mod (n : ℕ) (hn : 1 ≤ n) (x : ℤ) :
    ((n : ℤ) * ((n : ℤ) + 1)) ∣
      x - (((n : ℤ) + 1) * (x % (n : ℤ)) -
           (n : ℤ) * (x % ((n : ℤ) + 1))) := by
  exact successor_reverse_divisible n x

theorem reverse_lookup_coefficient (k : ℕ) (N x : ℤ)
    (n c a : Fin k → ℤ)
    (hcoeff : ∀ i, N ∣ c i * n i)
    (hres : ∀ i, n i ∣ a i - x)
    (hsum : N ∣ (∑ i : Fin k, c i) - 1) :
    N ∣ (∑ i : Fin k, c i * a i) - x := by
  have hdiv : ∀ i : Fin k, N ∣ c i * (a i - x) := by
    intro i
    obtain ⟨z, hz⟩ := hres i
    obtain ⟨w, hw⟩ := hcoeff i
    refine ⟨w * z, ?_⟩
    calc
      c i * (a i - x) = c i * (n i * z) := by rw [hz]
      _ = (c i * n i) * z := by ring
      _ = (N * w) * z := by rw [hw]
      _ = N * (w * z) := by ring
  have hs : N ∣ (∑ i : Fin k, c i * (a i - x)) := by
    apply Finset.dvd_sum
    intro i hi
    exact hdiv i
  have hm : N ∣ ((∑ i : Fin k, c i) - 1) * x := by
    obtain ⟨d, hd⟩ := hsum
    refine ⟨d * x, ?_⟩
    rw [hd]
    ring
  have hv : (∑ i : Fin k, c i * (a i - x)) =
      (∑ i : Fin k, c i * a i) - (∑ i : Fin k, c i) * x := by
    calc
      (∑ i : Fin k, c i * (a i - x)) =
          ∑ i : Fin k, (c i * a i - c i * x) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i : Fin k, c i * a i) -
          (∑ i : Fin k, c i * x) := by rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin k, c i * a i) - (∑ i : Fin k, c i) * x := by
        rw [Finset.sum_mul]
  have heq : (∑ i : Fin k, c i * a i) - x =
      (∑ i : Fin k, c i * (a i - x)) +
       ((∑ i : Fin k, c i) - 1) * x := by
    rw [hv]
    ring
  rw [heq]
  exact dvd_add hs hm

theorem reverse_lookup_integer (k : ℕ) (N x : ℤ)
    (n ε a : Fin k → ℤ)
    (hn : ∀ i, n i ∣ N)
    (hres : ∀ i, n i ∣ a i - x)
    (hsum : (∑ i : Fin k, ε i * (N / n i)) = 1) :
    N ∣ (∑ i : Fin k, (ε i * (N / n i)) * a i) - x := by
  apply reverse_lookup_coefficient k N x n (fun i => ε i * (N / n i)) a
  · intro i
    refine ⟨ε i, ?_⟩
    calc
      (ε i * (N / n i)) * n i =
        ε i * ((N / n i) * n i) := by ring
      _ = ε i * N := by rw [Int.ediv_mul_cancel (hn i)]
      _ = N * ε i := by ring
  · exact hres
  · simpa [hsum]

#print axioms reverse_lookup_coefficient
#print axioms reverse_lookup_integer

#print axioms zodiac_reverse_mod12
#print axioms successor_reverse_divisible
#print axioms successor_reverse_mod

end Unifier
