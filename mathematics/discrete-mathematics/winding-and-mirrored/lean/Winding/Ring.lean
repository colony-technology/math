import Winding.Hilbert
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Winding and Mirrored, W1 to W4: the two-sheet Hilbert ring

Notation of SPEC.md: `n = 2^k`, `N = 4^k`, the rectangle `R = {0..2n-1} × {0..n-1}`,
the mirror `mu(x, y) = (2n-1-x, y)` and the ring
`C(j) = H(j)` for `j < N`, `C(j) = mu(H(2N-1-j))` for `N ≤ j < 2N`,
with `H = Unifier.hilbertH k`. -/

namespace Winding

open Unifier

/-- The mirror `mu(x, y) = (2n - 1 - x, y)`, `n = 2^k`. -/
def mirror (k : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 * 2 ^ k - 1 - p.1, p.2)

/-- The rectangle `R = {0..2n-1} × {0..n-1}`. -/
def rect (k : ℕ) : Set (ℕ × ℕ) := {p | p.1 < 2 * 2 ^ k ∧ p.2 < 2 ^ k}

/-- The ring `C_k : {0..2N-1} → R`. -/
def cycle (k j : ℕ) : ℕ × ℕ :=
  if j < 4 ^ k then hilbertH k j else mirror k (hilbertH k (2 * 4 ^ k - 1 - j))

theorem cycle_lt (k j : ℕ) (hj : j < 4 ^ k) : cycle k j = hilbertH k j := by
  simp only [cycle, if_pos hj]

theorem cycle_ge (k j : ℕ) (hj : ¬ j < 4 ^ k) :
    cycle k j = mirror k (hilbertH k (2 * 4 ^ k - 1 - j)) := by
  simp only [cycle, if_neg hj]

/-! ## W1: every cell once -/

/-- W1: `C` is a bijection from `{0, ..., 2N-1}` onto `R`. -/
theorem cycle_bijOn (k : ℕ) : Set.BijOn (cycle k) {j | j < 2 * 4 ^ k} (rect k) := by
  have hs := two_pow_pos' k
  have hS := four_pow_pos k
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    simp only [Set.mem_setOf_eq] at hj
    by_cases h : j < 4 ^ k
    · rw [cycle_lt k j h]
      obtain ⟨h1, h2⟩ := hilbert_mapsTo k j h
      exact ⟨by omega, h2⟩
    · rw [cycle_ge k j h]
      obtain ⟨h1, h2⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j) (by omega)
      exact ⟨by simp only [mirror]; omega, h2⟩
  · intro j hj j' hj' heq
    simp only [Set.mem_setOf_eq] at hj hj'
    by_cases h : j < 4 ^ k <;> by_cases h' : j' < 4 ^ k
    · rw [cycle_lt k j h, cycle_lt k j' h'] at heq
      exact hilbert_injOn k j j' h h' heq
    · rw [cycle_lt k j h, cycle_ge k j' h'] at heq
      obtain ⟨h1, _⟩ := hilbert_mapsTo k j h
      obtain ⟨h1', _⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j') (by omega)
      have := congrArg Prod.fst heq
      simp only [mirror] at this
      omega
    · rw [cycle_ge k j h, cycle_lt k j' h'] at heq
      obtain ⟨h1, _⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j) (by omega)
      obtain ⟨h1', _⟩ := hilbert_mapsTo k j' h'
      have := congrArg Prod.fst heq
      simp only [mirror] at this
      omega
    · rw [cycle_ge k j h, cycle_ge k j' h'] at heq
      obtain ⟨h1, _⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j) (by omega)
      obtain ⟨h1', _⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j') (by omega)
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      simp only [mirror] at hx hy
      have hH : hilbertH k (2 * 4 ^ k - 1 - j) = hilbertH k (2 * 4 ^ k - 1 - j') :=
        Prod.ext (by omega) hy
      have := hilbert_injOn k _ _ (by omega) (by omega) hH
      omega
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only at hx hy
    by_cases h : x < 2 ^ k
    · obtain ⟨d, hd, hH⟩ := hilbert_surjOn k x y h hy
      refine ⟨d, by simp only [Set.mem_setOf_eq]; omega, ?_⟩
      rw [cycle_lt k d hd, hH]
    · obtain ⟨d, hd, hH⟩ := hilbert_surjOn k (2 * 2 ^ k - 1 - x) y (by omega) hy
      refine ⟨2 * 4 ^ k - 1 - d, by simp only [Set.mem_setOf_eq]; omega, ?_⟩
      rw [cycle_ge k _ (by omega)]
      have he : 2 * 4 ^ k - 1 - (2 * 4 ^ k - 1 - d) = d := by omega
      rw [he, hH]
      simp only [mirror, Prod.mk.injEq, and_true]
      omega

theorem cycle_mapsTo (k j : ℕ) (hj : j < 2 * 4 ^ k) :
    (cycle k j).1 < 2 * 2 ^ k ∧ (cycle k j).2 < 2 ^ k :=
  (cycle_bijOn k).mapsTo hj

/-! ## W2: the mirror reverses the traversal -/

/-- W2, first part: `mu (mu p) = p` on `R`. -/
theorem mirror_mirror (k : ℕ) (p : ℕ × ℕ) (hp : p ∈ rect k) : mirror k (mirror k p) = p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, _⟩ := hp
  simp only at hx
  simp only [mirror, Prod.mk.injEq, and_true]
  omega

/-- W2, second part: `C(2N-1-j) = mu(C(j))` for every `j < 2N`. -/
theorem cycle_reverse (k j : ℕ) (hj : j < 2 * 4 ^ k) :
    cycle k (2 * 4 ^ k - 1 - j) = mirror k (cycle k j) := by
  by_cases h : j < 4 ^ k
  · rw [cycle_ge k _ (by omega), cycle_lt k j h]
    have he : 2 * 4 ^ k - 1 - (2 * 4 ^ k - 1 - j) = j := by omega
    rw [he]
  · rw [cycle_lt k _ (by omega), cycle_ge k j h, mirror_mirror]
    obtain ⟨h1, h2⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - j) (by omega)
    exact ⟨by omega, h2⟩

/-! ## W3: unit steps, closed -/

/-- Neighbours in the periodic rectangle: one coordinate equal, the other differing by 1,
the `x` coordinate taken modulo `2n`. -/
def Neighbour (k : ℕ) (p p' : ℕ × ℕ) : Prop :=
  (p.1 = p'.1 ∧ (p.2 + 1 = p'.2 ∨ p'.2 + 1 = p.2)) ∨
  (p.2 = p'.2 ∧ ((p.1 + 1) % (2 * 2 ^ k) = p'.1 ∨ (p'.1 + 1) % (2 * 2 ^ k) = p.1))

/-- Plain grid adjacency inside the rectangle is periodic adjacency. -/
theorem neighbour_of_adj (k : ℕ) (p p' : ℕ × ℕ) (hp : p.1 < 2 * 2 ^ k)
    (hp' : p'.1 < 2 * 2 ^ k) (h : GridAdjacent p p') : Neighbour k p p' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · refine Or.inr ⟨h1, Or.inl ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    exact h2
  · refine Or.inr ⟨h1, Or.inr ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    exact h2

/-- The mirror preserves adjacency and reverses its direction. -/
theorem mirror_adj (k : ℕ) (p p' : ℕ × ℕ) (hp : p.1 < 2 * 2 ^ k) (hp' : p'.1 < 2 * 2 ^ k)
    (h : GridAdjacent p p') : GridAdjacent (mirror k p') (mirror k p) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only at hp hp'
  unfold GridAdjacent at h ⊢
  simp only [mirror] at h ⊢
  omega

/-- W3, join: `C(N-1) = (n-1, 0)`. -/
theorem cycle_join_left (k : ℕ) : cycle k (4 ^ k - 1) = (2 ^ k - 1, 0) := by
  rw [cycle_lt k _ (by have := four_pow_pos k; omega), hilbert_end]

/-- W3, join: `C(N) = (n, 0)`. -/
theorem cycle_join_right (k : ℕ) : cycle k (4 ^ k) = (2 ^ k, 0) := by
  have hs := two_pow_pos' k
  rw [cycle_ge k _ (lt_irrefl _)]
  have he : 2 * 4 ^ k - 1 - 4 ^ k = 4 ^ k - 1 := by omega
  rw [he, hilbert_end]
  simp only [mirror, Prod.mk.injEq, and_true]
  omega

/-- W3, closure: `C(2N-1) = (2n-1, 0)`. -/
theorem cycle_close_left (k : ℕ) : cycle k (2 * 4 ^ k - 1) = (2 * 2 ^ k - 1, 0) := by
  have hS := four_pow_pos k
  rw [cycle_ge k _ (by omega)]
  have he : 2 * 4 ^ k - 1 - (2 * 4 ^ k - 1) = 0 := by omega
  rw [he, hilbert_start]
  simp [mirror]

/-- W3, closure: `C(0) = (0, 0)`. -/
theorem cycle_start (k : ℕ) : cycle k 0 = (0, 0) := by
  rw [cycle_lt k 0 (four_pow_pos k), hilbert_start]

/-- Consecutive cells of the ring, without wrapping, are adjacent in the plain grid. -/
theorem cycle_adjacent (k j : ℕ) (hj : j + 1 < 2 * 4 ^ k) :
    GridAdjacent (cycle k j) (cycle k (j + 1)) := by
  have hs := two_pow_pos' k
  have hS := four_pow_pos k
  by_cases h1 : j + 1 < 4 ^ k
  · rw [cycle_lt k j (by omega), cycle_lt k (j + 1) h1]
    exact hilbert_locality k j h1
  · by_cases h2 : j + 1 = 4 ^ k
    · have hj' : j = 4 ^ k - 1 := by omega
      rw [h2, hj', cycle_join_left, cycle_join_right]
      unfold GridAdjacent
      simp only [true_and]
      omega
    · rw [cycle_ge k j (by omega), cycle_ge k (j + 1) (by omega)]
      have he : 2 * 4 ^ k - 1 - j = (2 * 4 ^ k - 1 - (j + 1)) + 1 := by omega
      rw [he]
      have hd : (2 * 4 ^ k - 1 - (j + 1)) + 1 < 4 ^ k := by omega
      obtain ⟨a1, _⟩ := hilbert_mapsTo k _ hd
      obtain ⟨a2, _⟩ := hilbert_mapsTo k (2 * 4 ^ k - 1 - (j + 1)) (by omega)
      exact mirror_adj k _ _ (by omega) (by omega) (hilbert_locality k _ hd)

/-- W3: for every `j < 2N`, `C(j)` and `C((j+1) mod 2N)` are neighbours. This holds for every
`k ≥ 0`, including `k = 0`, where the rectangle is 2 by 1. -/
theorem cycle_step (k j : ℕ) (hj : j < 2 * 4 ^ k) :
    Neighbour k (cycle k j) (cycle k ((j + 1) % (2 * 4 ^ k))) := by
  have hs := two_pow_pos' k
  by_cases h : j + 1 < 2 * 4 ^ k
  · rw [Nat.mod_eq_of_lt h]
    exact neighbour_of_adj k _ _ (cycle_mapsTo k j hj).1 (cycle_mapsTo k (j + 1) h).1
      (cycle_adjacent k j h)
  · have hj' : j = 2 * 4 ^ k - 1 := by omega
    have he : j + 1 = 2 * 4 ^ k := by omega
    rw [he, Nat.mod_self, hj', cycle_close_left, cycle_start]
    refine Or.inr ⟨rfl, Or.inl ?_⟩
    show (2 * 2 ^ k - 1 + 1) % (2 * 2 ^ k) = 0
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]

/-- W1 and W3 together: `C` is a closed Hamiltonian cycle of the periodic rectangle. -/
theorem cycle_hamiltonian (k : ℕ) :
    Set.BijOn (cycle k) {j | j < 2 * 4 ^ k} (rect k) ∧
    ∀ j, j < 2 * 4 ^ k → Neighbour k (cycle k j) (cycle k ((j + 1) % (2 * 4 ^ k))) :=
  ⟨cycle_bijOn k, cycle_step k⟩

/-! ## W4: winding -/

/-- The cyclic `x` difference in `{-1, 0, 1}` modulo `m`, a function of the two `x` values and the
modulus only: `+1` when `b = a + 1 mod m`, `-1` when `a = b + 1 mod m`, `0` otherwise. -/
def cycDx (m a b : ℕ) : ℤ :=
  if (a + 1) % m = b then 1 else if (b + 1) % m = a then -1 else 0

/-- For `m ≥ 3` the two cases of `cycDx` exclude each other, so the sign is well defined. -/
theorem cycDx_welldefined (m a b : ℕ) (hm : 3 ≤ m) (ha : a < m) (hb : b < m) :
    ¬ ((a + 1) % m = b ∧ (b + 1) % m = a) := by
  rintro ⟨h1, h2⟩
  by_cases ha' : a + 1 < m
  · rw [Nat.mod_eq_of_lt ha'] at h1
    subst h1
    by_cases hb' : a + 1 + 1 < m
    · rw [Nat.mod_eq_of_lt hb'] at h2
      omega
    · have : a + 1 + 1 = m := by omega
      rw [this, Nat.mod_self] at h2
      omega
  · have : a + 1 = m := by omega
    rw [this, Nat.mod_self] at h1
    subst h1
    rw [Nat.mod_eq_of_lt (by omega)] at h2
    omega

/-- For `m = 2` (the case `k = 0`) both cases hold for the step `0 → 1`, so the sign is not
defined there. -/
theorem cycDx_two_ambiguous : (0 + 1) % 2 = 1 ∧ (1 + 1) % 2 = 0 := by decide

/-- On a non-wrapping unit step the cyclic difference is the integer difference. -/
theorem cycDx_of_step (m a b : ℕ) (hm : 3 ≤ m) (ha : a < m) (hb : b < m)
    (h : a + 1 = b ∨ b + 1 = a ∨ a = b) : cycDx m a b = (b : ℤ) - a := by
  unfold cycDx
  rcases h with h | h | h
  · rw [if_pos (by rw [Nat.mod_eq_of_lt (by omega)]; exact h)]
    omega
  · have hn : ¬ (a + 1) % m = b := by
      by_cases ha' : a + 1 < m
      · rw [Nat.mod_eq_of_lt ha']; omega
      · have : a + 1 = m := by omega
        rw [this, Nat.mod_self]; omega
    rw [if_neg hn, if_pos (by rw [Nat.mod_eq_of_lt (by omega)]; exact h)]
    omega
  · subst h
    have hn : ¬ (a + 1) % m = a := by
      by_cases ha' : a + 1 < m
      · rw [Nat.mod_eq_of_lt ha']; omega
      · have : a + 1 = m := by omega
        rw [this, Nat.mod_self]; omega
    rw [if_neg hn, if_neg hn]
    simp

theorem cycDx_of_adj (m : ℕ) (p p' : ℕ × ℕ) (hm : 3 ≤ m) (hp : p.1 < m) (hp' : p'.1 < m)
    (h : GridAdjacent p p') : cycDx m p.1 p'.1 = (p'.1 : ℤ) - p.1 := by
  apply cycDx_of_step m _ _ hm hp hp'
  rcases h with ⟨h1, _⟩ | ⟨_, h2 | h2⟩
  · exact Or.inr (Or.inr h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)

theorem gridAdjacent_symm (p p' : ℕ × ℕ) (h : GridAdjacent p p') : GridAdjacent p' p := by
  unfold GridAdjacent at h ⊢
  omega

/-- The sum of `dx` around a closed path of `L + 1` cells whose first `L` steps are plain unit
steps: the telescoped difference plus the closing step. -/
theorem cyclic_sum_dx (f : ℕ → ℕ × ℕ) (m L : ℕ) (hm : 3 ≤ m) (hb : ∀ j, j ≤ L → (f j).1 < m)
    (hadj : ∀ j, j < L → GridAdjacent (f j) (f (j + 1))) :
    ∑ j ∈ Finset.range (L + 1), cycDx m (f j).1 (f ((j + 1) % (L + 1))).1 =
      ((f L).1 : ℤ) - (f 0).1 + cycDx m (f L).1 (f 0).1 := by
  rw [Finset.sum_range_succ, Nat.mod_self]
  congr 1
  rw [← Finset.sum_range_sub (fun j => ((f j).1 : ℤ)) L]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Nat.mod_eq_of_lt (by omega)]
  exact cycDx_of_adj m _ _ hm (hb j (by omega)) (hb (j + 1) (by omega)) (hadj j hj)

/-- The sum of `dy` around any closed path is `0`. -/
theorem cyclic_sum_dy (f : ℕ → ℕ × ℕ) (L : ℕ) :
    ∑ j ∈ Finset.range (L + 1), (((f ((j + 1) % (L + 1))).2 : ℤ) - (f j).2) = 0 := by
  rw [Finset.sum_range_succ, Nat.mod_self]
  have : ∑ j ∈ Finset.range L, (((f ((j + 1) % (L + 1))).2 : ℤ) - (f j).2) =
      ∑ j ∈ Finset.range L, (((f (j + 1)).2 : ℤ) - (f j).2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [this, Finset.sum_range_sub (fun j => ((f j).2 : ℤ)) L]
  ring

/-- `dx` of step `j` of the ring: from `C(j)` to `C((j+1) mod 2N)`. -/
def stepDx (k j : ℕ) : ℤ := cycDx (2 * 2 ^ k) (cycle k j).1 (cycle k ((j + 1) % (2 * 4 ^ k))).1

/-- `dy` of step `j` of the ring. -/
def stepDy (k j : ℕ) : ℤ := ((cycle k ((j + 1) % (2 * 4 ^ k))).2 : ℤ) - (cycle k j).2

/-- The reversed ring: `j ↦ C(2N-1-j)`. -/
def revCycle (k j : ℕ) : ℕ × ℕ := cycle k (2 * 4 ^ k - 1 - j)

/-- `dx` of step `j` of the reversed ring. -/
def revDx (k j : ℕ) : ℤ :=
  cycDx (2 * 2 ^ k) (revCycle k j).1 (revCycle k ((j + 1) % (2 * 4 ^ k))).1

/-- `dy` of step `j` of the reversed ring. -/
def revDy (k j : ℕ) : ℤ := ((revCycle k ((j + 1) % (2 * 4 ^ k))).2 : ℤ) - (revCycle k j).2

theorem three_le (k : ℕ) (hk : 1 ≤ k) : 3 ≤ 2 * 2 ^ k := by
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

/-- W4: for `k ≥ 1` the sum of `dx` over the `2N` steps of the ring is `2n`. -/
theorem winding_dx (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (2 * 4 ^ k), stepDx k j = ((2 * 2 ^ k : ℕ) : ℤ) := by
  have hS := four_pow_pos k
  have hs := two_pow_pos' k
  have hm := three_le k hk
  obtain ⟨L, hL⟩ : ∃ L, 2 * 4 ^ k = L + 1 := ⟨2 * 4 ^ k - 1, by omega⟩
  unfold stepDx
  rw [hL, cyclic_sum_dx (cycle k) (2 * 2 ^ k) L hm
    (fun j hj => (cycle_mapsTo k j (by omega)).1) (fun j hj => cycle_adjacent k j (by omega))]
  have hL' : L = 2 * 4 ^ k - 1 := by omega
  rw [hL', cycle_close_left, cycle_start]
  have h1 : cycDx (2 * 2 ^ k) (2 * 2 ^ k - 1) 0 = 1 := by
    unfold cycDx
    rw [if_pos]
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  simp only [h1]
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- W4: the sum of `dy` over the `2N` steps of the ring is `0` (every `k`). -/
theorem winding_dy (k : ℕ) : ∑ j ∈ Finset.range (2 * 4 ^ k), stepDy k j = 0 := by
  have hS := four_pow_pos k
  obtain ⟨L, hL⟩ : ∃ L, 2 * 4 ^ k = L + 1 := ⟨2 * 4 ^ k - 1, by omega⟩
  unfold stepDy
  rw [hL]
  exact cyclic_sum_dy (cycle k) L

/-- W4, reversed: for `k ≥ 1` the reversed ring has `dx` sum `-2n`. -/
theorem winding_dx_reverse (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (2 * 4 ^ k), revDx k j = -((2 * 2 ^ k : ℕ) : ℤ) := by
  have hS := four_pow_pos k
  have hs := two_pow_pos' k
  have hm := three_le k hk
  obtain ⟨L, hL⟩ : ∃ L, 2 * 4 ^ k = L + 1 := ⟨2 * 4 ^ k - 1, by omega⟩
  have hb : ∀ j, j ≤ L → (revCycle k j).1 < 2 * 2 ^ k :=
    fun j hj => (cycle_mapsTo k _ (by omega)).1
  have hadj : ∀ j, j < L → GridAdjacent (revCycle k j) (revCycle k (j + 1)) := by
    intro j hj
    unfold revCycle
    have he : 2 * 4 ^ k - 1 - j = (2 * 4 ^ k - 1 - (j + 1)) + 1 := by omega
    rw [he]
    exact gridAdjacent_symm _ _ (cycle_adjacent k _ (by omega))
  unfold revDx
  rw [hL, cyclic_sum_dx (revCycle k) (2 * 2 ^ k) L hm hb hadj]
  have hL' : L = 2 * 4 ^ k - 1 := by omega
  have e1 : revCycle k L = (0, 0) := by
    unfold revCycle
    rw [hL', Nat.sub_self, cycle_start]
  have e0 : revCycle k 0 = (2 * 2 ^ k - 1, 0) := by
    unfold revCycle
    rw [Nat.sub_zero, cycle_close_left]
  rw [e1, e0]
  have h1 : cycDx (2 * 2 ^ k) 0 (2 * 2 ^ k - 1) = -1 := by
    unfold cycDx
    rw [if_neg (by rw [Nat.mod_eq_of_lt (by omega)]; omega), if_pos]
    rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
  simp only [h1]
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- W4, reversed: the reversed ring has `dy` sum `0`. -/
theorem winding_dy_reverse (k : ℕ) : ∑ j ∈ Finset.range (2 * 4 ^ k), revDy k j = 0 := by
  have hS := four_pow_pos k
  obtain ⟨L, hL⟩ : ∃ L, 2 * 4 ^ k = L + 1 := ⟨2 * 4 ^ k - 1, by omega⟩
  unfold revDy
  rw [hL]
  exact cyclic_sum_dy (revCycle k) L

/-- W4, winding numbers: `(Σ dx) / (2n) = 1` and `Σ dy = 0` for the ring; `-1` and `0` for the
reversed ring. -/
theorem winding_number (k : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.range (2 * 4 ^ k), stepDx k j) / ((2 * 2 ^ k : ℕ) : ℤ) = 1 ∧
    ∑ j ∈ Finset.range (2 * 4 ^ k), stepDy k j = 0 ∧
    (∑ j ∈ Finset.range (2 * 4 ^ k), revDx k j) / ((2 * 2 ^ k : ℕ) : ℤ) = -1 ∧
    ∑ j ∈ Finset.range (2 * 4 ^ k), revDy k j = 0 := by
  have hs := two_pow_pos' k
  have hne : ((2 * 2 ^ k : ℕ) : ℤ) ≠ 0 := by positivity
  refine ⟨?_, winding_dy k, ?_, winding_dy_reverse k⟩
  · rw [winding_dx k hk, Int.ediv_self hne]
  · rw [winding_dx_reverse k hk, Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self hne]

#print axioms cycle_bijOn
#print axioms mirror_mirror
#print axioms cycle_reverse
#print axioms cycle_join_left
#print axioms cycle_join_right
#print axioms cycle_close_left
#print axioms cycle_start
#print axioms cycle_adjacent
#print axioms cycle_step
#print axioms cycle_hamiltonian
#print axioms cycDx_welldefined
#print axioms cycDx_two_ambiguous
#print axioms cycDx_of_step
#print axioms cyclic_sum_dx
#print axioms cyclic_sum_dy
#print axioms winding_dx
#print axioms winding_dy
#print axioms winding_dx_reverse
#print axioms winding_dy_reverse
#print axioms winding_number

end Winding
