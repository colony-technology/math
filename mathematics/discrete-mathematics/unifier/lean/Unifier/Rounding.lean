import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Unifier.Reverse

/-! # The Unifier: T15, T16, T23, nearest-tick readers

`round` is Mathlib's round-half-up on a floor ring: `round x = ⌊x + 1/2⌋`. -/

namespace Unifier

theorem round_of_abs_error (z : ℝ) (a : ℤ)
    (h : |z - (a : ℝ)| < 1 / 2) : round z = a := by
  rw [round_eq, Int.floor_eq_iff]
  rcases abs_lt.mp h with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- T15, first part: a reading within `1/(2n)` of the tick `a/n` rounds to `a`. -/
theorem dial_round_tolerance (n : ℕ) (hn : 0 < n)
    (a : ℤ) (θ : ℝ)
    (h : |θ - (a : ℝ) / n| < 1 / (2 * n)) :
    round ((n : ℝ) * θ) = a := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  apply round_of_abs_error
  have heq : (n : ℝ) * θ - (a : ℝ) = (n : ℝ) * (θ - (a : ℝ) / n) := by
    field_simp <;> ring
  have hr : (n : ℝ) * (1 / (2 * n)) = (1 / 2 : ℝ) := by
    field_simp <;> ring
  rw [heq, abs_mul, abs_of_pos hnpos]
  calc (n : ℝ) * |θ - (a : ℝ) / n| < (n : ℝ) * (1 / (2 * n)) :=
        mul_lt_mul_of_pos_left h hnpos
    _ = 1 / 2 := hr

/-- T16: a straight scale of `N` positions tolerates every error below `1/(2N)`. -/
theorem straight_scale_tolerance (N : ℕ) (hN : 0 < N)
    (x : ℤ) (δ : ℝ)
    (h : |δ| < 1 / (2 * N)) :
    round ((N : ℝ) * ((x : ℝ) / N + δ)) = x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  apply dial_round_tolerance N hN x
  have heq : (x : ℝ) / N + δ - (x : ℝ) / N = δ := by ring
  rw [heq]
  exact h

/-- T16: at exactly half of `1/N` the straight scale reads the next position. -/
theorem straight_scale_half_tie (N : ℕ) (hN : 0 < N)
    (x : ℤ) :
    round ((N : ℝ) * ((x : ℝ) / N + 1 / (2 * N))) = x + 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have heq : (N : ℝ) * ((x : ℝ) / N + 1 / (2 * N)) =
      (x : ℝ) + (1 / 2 : ℝ) := by
    field_simp <;> ring
  rw [heq, round_eq, Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

/-- T23: the reader of a closed dial with `n` ticks. -/
noncomputable def dialReader (n : ℕ) (θ : ℝ) : ℝ :=
  (round ((n : ℝ) * θ) : ℝ) / n

/-- T23: every tick `a/n` is fixed by the reader. -/
theorem dial_reader_tick (n : ℕ) (hn : 0 < n) (a : ℤ) :
    dialReader n ((a : ℝ) / n) = (a : ℝ) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmul : (n : ℝ) * ((a : ℝ) / n) = (a : ℝ) := by
    field_simp
  unfold dialReader
  rw [hmul, round_intCast]

/-- T23: the reader is idempotent. -/
theorem dial_reader_idempotent (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    dialReader n (dialReader n θ) = dialReader n θ :=
  dial_reader_tick n hn (round ((n : ℝ) * θ))

/-- T23: a reading within `1/(2n)` of the tick `a/n` is read as `a/n`. -/
theorem dial_reader_tolerance (n : ℕ) (hn : 0 < n)
    (a : ℤ) (θ : ℝ)
    (h : |θ - (a : ℝ) / n| < 1 / (2 * n)) :
    dialReader n θ = (a : ℝ) / n := by
  unfold dialReader
  rw [dial_round_tolerance n hn a θ h]

/-- T15, second part: an error below `1/(2(nmax+nmin))` is below the tolerance
of every dial with `nmin ≤ n ≤ nmax`. -/
theorem uniform_dial_error (nmin nmax n : ℕ)
    (hmin : 1 ≤ nmin) (hmid : nmin ≤ n) (hmax : n ≤ nmax)
    (δ : ℝ)
    (hδ : |δ| < 1 / (2 * ((nmax + nmin : ℕ) : ℝ))) :
    |δ| < 1 / (2 * (n : ℝ)) := by
  have hn : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (n : ℝ) ≤ ((nmax + nmin : ℕ) : ℝ) := by
    exact_mod_cast (le_trans hmax (Nat.le_add_right nmax nmin))
  have hb : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hc : 1 / (2 * ((nmax + nmin : ℕ) : ℝ)) ≤ 1 / (2 * (n : ℝ)) :=
    one_div_le_one_div_of_le hb (by linarith)
  exact lt_of_lt_of_le hδ hc

theorem round_uniform_dial (nmin nmax n : ℕ)
    (hmin : 1 ≤ nmin) (hmid : nmin ≤ n) (hmax : n ≤ nmax)
    (a : ℤ) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / n| <
      1 / (2 * ((nmax + nmin : ℕ) : ℝ))) :
    round ((n : ℝ) * θ) = a := by
  apply dial_round_tolerance n (by omega) a θ
  exact uniform_dial_error nmin nmax n hmin hmid hmax _ hθ

/-- T15, the composition: read each dial `i` (modulus `n i`, between `nmin` and `nmax`)
to its closest tick and compose by T12; the result is `x` modulo `N`. The error bound
`1/(2(nmax+nmin))` does not mention `N`. -/
theorem reverse_lookup_from_readings (k : ℕ) (N x : ℤ) (nmin nmax : ℕ)
    (n : Fin k → ℕ) (c : Fin k → ℤ) (θ : Fin k → ℝ)
    (hmin : 1 ≤ nmin) (hrange : ∀ i, nmin ≤ n i ∧ n i ≤ nmax)
    (hcoeff : ∀ i, N ∣ c i * (n i : ℤ))
    (hsum : N ∣ (∑ i : Fin k, c i) - 1)
    (hθ : ∀ i, |θ i - ((x % (n i : ℤ) : ℤ) : ℝ) / (n i : ℝ)| <
      1 / (2 * ((nmax + nmin : ℕ) : ℝ))) :
    N ∣ (∑ i : Fin k, c i * round ((n i : ℝ) * θ i)) - x := by
  have hread : ∀ i, round ((n i : ℝ) * θ i) = x % (n i : ℤ) := fun i =>
    round_uniform_dial nmin nmax (n i) hmin (hrange i).1 (hrange i).2 _ _ (hθ i)
  apply reverse_lookup_coefficient k N x (fun i => (n i : ℤ)) c
    (fun i => round ((n i : ℝ) * θ i)) hcoeff
  · intro i
    rw [hread i]
    have he := Int.emod_add_mul_ediv x (n i : ℤ)
    exact ⟨-(x / (n i : ℤ)), by linarith⟩
  · exact hsum

#print axioms round_of_abs_error
#print axioms dial_round_tolerance
#print axioms uniform_dial_error
#print axioms round_uniform_dial
#print axioms reverse_lookup_from_readings
#print axioms straight_scale_tolerance
#print axioms straight_scale_half_tie
#print axioms dial_reader_tick
#print axioms dial_reader_idempotent
#print axioms dial_reader_tolerance

end Unifier
