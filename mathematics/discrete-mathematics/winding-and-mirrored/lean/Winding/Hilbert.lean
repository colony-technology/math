import Mathlib.Data.Set.Function
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Ring

/-! # The Unifier: Section 6, the Hilbert angular coordinate

`hilbertH k d` is Definition 6.1 written on the natural numbers. For `d = q * 4^k + r`
with `q < 4`, `r < 4^k` and `(x, y) = H_k(r)`, `s = 2^k`:
`q = 0 ↦ (y, x)`, `q = 1 ↦ (x, y + s)`, `q = 2 ↦ (x + s, y + s)`,
`q = 3 ↦ (2s - 1 - y, s - 1 - x)`. The recursion reads `q = d / 4^k` and `r = d % 4^k`.
Off the domain `d < 4^k` the value is irrelevant; every statement is restricted to it.

T17 (`hilbert_bijOn`), T18 (`hilbert_locality`, `hilbert_chebyshev`) and T19
(`hilbert_quarters`, `hilbert_start`, `hilbert_end`) are proved for every `k` by
induction on `k`, with the endpoint invariant `H_k(0) = (0,0)`,
`H_k(4^k - 1) = (2^k - 1, 0)` carried through the induction for the quarter seams. -/

namespace Unifier

/-- The four maps of Definition 6.1, with `s = 2^k`. -/
def hilbertQuarter (s q : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if q = 0 then (p.2, p.1)
  else if q = 1 then (p.1, p.2 + s)
  else if q = 2 then (p.1 + s, p.2 + s)
  else (2 * s - 1 - p.2, s - 1 - p.1)

theorem hilbertQuarter_zero (s : ℕ) (p : ℕ × ℕ) : hilbertQuarter s 0 p = (p.2, p.1) := by
  simp [hilbertQuarter]

theorem hilbertQuarter_one (s : ℕ) (p : ℕ × ℕ) :
    hilbertQuarter s 1 p = (p.1, p.2 + s) := by
  simp [hilbertQuarter]

theorem hilbertQuarter_two (s : ℕ) (p : ℕ × ℕ) :
    hilbertQuarter s 2 p = (p.1 + s, p.2 + s) := by
  simp [hilbertQuarter]

theorem hilbertQuarter_three (s : ℕ) (p : ℕ × ℕ) :
    hilbertQuarter s 3 p = (2 * s - 1 - p.2, s - 1 - p.1) := by
  simp [hilbertQuarter]

/-- Definition 6.1: the Hilbert coordinate `H_k`. -/
def hilbertH : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | k + 1, d => hilbertQuarter (2 ^ k) (d / 4 ^ k) (hilbertH k (d % 4 ^ k))

/-- The `2^k` by `2^k` grid. -/
def hilbertGrid (k : ℕ) : Set (ℕ × ℕ) := {p | p.1 < 2 ^ k ∧ p.2 < 2 ^ k}

/-- Two cells differ by exactly 1 in exactly one coordinate. -/
def GridAdjacent (p p' : ℕ × ℕ) : Prop :=
  (p.1 = p'.1 ∧ (p.2 + 1 = p'.2 ∨ p'.2 + 1 = p.2)) ∨
  (p.2 = p'.2 ∧ (p.1 + 1 = p'.1 ∨ p'.1 + 1 = p.1))

theorem four_pow_pos (k : ℕ) : 0 < 4 ^ k := Nat.pow_pos (by decide : 0 < 4)

theorem two_pow_pos' (k : ℕ) : 0 < 2 ^ k := Nat.pow_pos (by decide : 0 < 2)

/-- Reading the quarter and the remainder of `q * 4^k + r`. -/
theorem hilbertH_succ (k q r : ℕ) (hr : r < 4 ^ k) :
    hilbertH (k + 1) (q * 4 ^ k + r) = hilbertQuarter (2 ^ k) q (hilbertH k r) := by
  have h := (Nat.div_mod_unique (four_pow_pos k)).2
    (⟨by ring, hr⟩ : r + 4 ^ k * q = q * 4 ^ k + r ∧ r < 4 ^ k)
  show hilbertQuarter (2 ^ k) ((q * 4 ^ k + r) / 4 ^ k)
      (hilbertH k ((q * 4 ^ k + r) % 4 ^ k)) = _
  rw [h.1, h.2]

/-- Every index below `4^(k+1)` is `q * 4^k + r` with `q < 4` and `r < 4^k`. -/
theorem hilbert_index_split (k d : ℕ) (hd : d < 4 ^ (k + 1)) :
    ∃ q r, q < 4 ∧ r < 4 ^ k ∧ d = q * 4 ^ k + r := by
  refine ⟨d / 4 ^ k, d % 4 ^ k, ?_, Nat.mod_lt d (four_pow_pos k), ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (four_pow_pos k)]
    rw [pow_succ] at hd
    omega
  · exact (Nat.div_add_mod' d (4 ^ k)).symm

theorem pow_succ_two (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by ring

theorem pow_succ_four (k : ℕ) : 4 ^ (k + 1) = 4 * 4 ^ k := by ring

theorem quarter_cases (q : ℕ) (hq : q < 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
  omega

/-- The quarter maps send the `s`-grid into the `2s`-grid. -/
theorem hilbertQuarter_maps (s q : ℕ) (hq : q < 4) (p : ℕ × ℕ) (ha : p.1 < s) (hb : p.2 < s) :
    (hilbertQuarter s q p).1 < 2 * s ∧ (hilbertQuarter s q p).2 < 2 * s := by
  obtain ⟨a, b⟩ := p
  rcases quarter_cases q hq with h | h | h | h <;> subst h <;>
    simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true] at ha hb ⊢ <;> omega

/-- The quarter maps are jointly injective on the `s`-grid. -/
theorem hilbertQuarter_inj (s q q' : ℕ) (hq : q < 4) (hq' : q' < 4)
    (p p' : ℕ × ℕ) (ha : p.1 < s) (hb : p.2 < s) (ha' : p'.1 < s) (hb' : p'.2 < s)
    (h : hilbertQuarter s q p = hilbertQuarter s q' p') :
    q = q' ∧ p = p' := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only [Prod.mk.injEq] at ha hb ha' hb' ⊢
  rcases quarter_cases q hq with h1 | h1 | h1 | h1 <;>
  rcases quarter_cases q' hq' with h2 | h2 | h2 | h2 <;>
  subst h1 h2 <;>
  simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Prod.mk.injEq] at h <;>
  omega

/-- The quarter maps preserve adjacency on the `s`-grid. -/
theorem hilbertQuarter_adj (s q : ℕ) (hq : q < 4) (p p' : ℕ × ℕ)
    (ha : p.1 < s) (hb : p.2 < s) (ha' : p'.1 < s) (hb' : p'.2 < s)
    (h : GridAdjacent p p') :
    GridAdjacent (hilbertQuarter s q p) (hilbertQuarter s q p') := by
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := p'
  simp only at ha hb ha' hb'
  unfold GridAdjacent at h ⊢
  rcases quarter_cases q hq with h1 | h1 | h1 | h1 <;> subst h1 <;>
    simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true] at h ⊢ <;> omega

/-- T17, maps-to part: `H_k` sends `{0, ..., 4^k - 1}` into the grid. -/
theorem hilbert_mapsTo (k : ℕ) :
    ∀ d, d < 4 ^ k → (hilbertH k d).1 < 2 ^ k ∧ (hilbertH k d).2 < 2 ^ k := by
  induction k with
  | zero => intro d _; simp [hilbertH]
  | succ k ih =>
    intro d hd
    obtain ⟨q, r, hq, hr, rfl⟩ := hilbert_index_split k d hd
    rw [hilbertH_succ k q r hr, pow_succ_two]
    obtain ⟨h1, h2⟩ := ih r hr
    exact hilbertQuarter_maps (2 ^ k) q hq _ h1 h2

/-- T19, endpoints: `H_k(0) = (0, 0)`. -/
theorem hilbert_start (k : ℕ) : hilbertH k 0 = (0, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := hilbertH_succ k 0 0 (four_pow_pos k)
    simp only [Nat.zero_mul, Nat.add_zero] at h
    rw [h, ih]
    simp [hilbertQuarter]

/-- T19, endpoints: `H_k(4^k - 1) = (2^k - 1, 0)`. -/
theorem hilbert_end (k : ℕ) : hilbertH k (4 ^ k - 1) = (2 ^ k - 1, 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hS := four_pow_pos k
    have hs := two_pow_pos' k
    have hidx : 4 ^ (k + 1) - 1 = 3 * 4 ^ k + (4 ^ k - 1) := by
      rw [pow_succ_four]; omega
    rw [hidx, hilbertH_succ k 3 (4 ^ k - 1) (by omega), ih, pow_succ_two]
    simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Prod.mk.injEq]
    omega

/-- T17, injective part. -/
theorem hilbert_injOn (k : ℕ) :
    ∀ d d', d < 4 ^ k → d' < 4 ^ k → hilbertH k d = hilbertH k d' → d = d' := by
  induction k with
  | zero => intro d d' hd hd' _; rw [pow_zero] at hd hd'; omega
  | succ k ih =>
    intro d d' hd hd' h
    obtain ⟨q, r, hq, hr, rfl⟩ := hilbert_index_split k d hd
    obtain ⟨q', r', hq', hr', rfl⟩ := hilbert_index_split k d' hd'
    rw [hilbertH_succ k q r hr, hilbertH_succ k q' r' hr'] at h
    obtain ⟨h1, h2⟩ := hilbert_mapsTo k r hr
    obtain ⟨h1', h2'⟩ := hilbert_mapsTo k r' hr'
    obtain ⟨hqq, hpp⟩ := hilbertQuarter_inj (2 ^ k) q q' hq hq' _ _ h1 h2 h1' h2' h
    have hrr : r = r' := ih r r' hr hr' hpp
    rw [hqq, hrr]

/-- T17, onto part: every cell of the grid is reached. -/
theorem hilbert_surjOn (k : ℕ) :
    ∀ x y, x < 2 ^ k → y < 2 ^ k → ∃ d, d < 4 ^ k ∧ hilbertH k d = (x, y) := by
  induction k with
  | zero =>
    intro x y hx hy
    rw [pow_zero] at hx hy
    refine ⟨0, by rw [pow_zero]; omega, ?_⟩
    show ((0 : ℕ), (0 : ℕ)) = (x, y)
    rw [Prod.mk.injEq]
    omega
  | succ k ih =>
    intro x y hx hy
    rw [pow_succ_two] at hx hy
    have hs := two_pow_pos' k
    have hS : 4 ^ (k + 1) = 4 * 4 ^ k := pow_succ_four k
    by_cases hxs : x < 2 ^ k <;> by_cases hys : y < 2 ^ k
    · obtain ⟨r, hr, hH⟩ := ih y x hys hxs
      refine ⟨0 * 4 ^ k + r, by omega, ?_⟩
      rw [hilbertH_succ k 0 r hr, hH]
      simp [hilbertQuarter]
    · obtain ⟨r, hr, hH⟩ := ih x (y - 2 ^ k) hxs (by omega)
      refine ⟨1 * 4 ^ k + r, by omega, ?_⟩
      rw [hilbertH_succ k 1 r hr, hH]
      simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Prod.mk.injEq]
      omega
    · obtain ⟨r, hr, hH⟩ := ih (2 ^ k - 1 - y) (2 * 2 ^ k - 1 - x) (by omega) (by omega)
      refine ⟨3 * 4 ^ k + r, by omega, ?_⟩
      rw [hilbertH_succ k 3 r hr, hH]
      simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Prod.mk.injEq]
      omega
    · obtain ⟨r, hr, hH⟩ := ih (x - 2 ^ k) (y - 2 ^ k) (by omega) (by omega)
      refine ⟨2 * 4 ^ k + r, by omega, ?_⟩
      rw [hilbertH_succ k 2 r hr, hH]
      simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Prod.mk.injEq]
      omega

/-- T17: for every `k`, `H_k` is a bijection from `{0, ..., 4^k - 1}` onto the
`2^k` by `2^k` grid. -/
theorem hilbert_bijOn (k : ℕ) :
    Set.BijOn (hilbertH k) {d | d < 4 ^ k} (hilbertGrid k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact hilbert_mapsTo k d hd
  · intro d hd d' hd' h
    exact hilbert_injOn k d d' hd hd' h
  · intro p hp
    obtain ⟨d, hd, hH⟩ := hilbert_surjOn k p.1 p.2 hp.1 hp.2
    exact ⟨d, hd, hH⟩

/-- T18: for every `k` and every `d` with `d + 1 < 4^k`, `H_k(d)` and `H_k(d+1)` differ by
exactly 1 in exactly one coordinate. -/
theorem hilbert_locality (k : ℕ) :
    ∀ d, d + 1 < 4 ^ k → GridAdjacent (hilbertH k d) (hilbertH k (d + 1)) := by
  induction k with
  | zero => intro d hd; rw [pow_zero] at hd; omega
  | succ k ih =>
    intro d hd
    have hs := two_pow_pos' k
    have hS := four_pow_pos k
    obtain ⟨q, r, hq, hr, rfl⟩ := hilbert_index_split k d (by omega)
    by_cases hlast : r + 1 < 4 ^ k
    · -- inside one quarter: the quarter map preserves adjacency
      have he : q * 4 ^ k + r + 1 = q * 4 ^ k + (r + 1) := Nat.add_assoc _ _ _
      rw [he, hilbertH_succ k q r hr, hilbertH_succ k q (r + 1) hlast]
      obtain ⟨h1, h2⟩ := hilbert_mapsTo k r hr
      obtain ⟨h1', h2'⟩ := hilbert_mapsTo k (r + 1) hlast
      exact hilbertQuarter_adj (2 ^ k) q hq _ _ h1 h2 h1' h2' (ih r hlast)
    · -- the seam between quarter q and quarter q + 1: the endpoint invariant
      have hr' : r = 4 ^ k - 1 := by omega
      subst hr'
      rw [pow_succ_four] at hd
      have hq3 : q < 3 := by
        rcases quarter_cases q hq with h | h | h | h <;> subst h <;> omega
      have he : q * 4 ^ k + (4 ^ k - 1) + 1 = (q + 1) * 4 ^ k + 0 := by
        rcases quarter_cases q hq with h | h | h | h <;> subst h <;> omega
      rw [he, hilbertH_succ k q _ (by omega), hilbertH_succ k (q + 1) 0 hS,
        hilbert_end, hilbert_start]
      unfold GridAdjacent
      rcases quarter_cases q hq with h | h | h | h <;> subst h <;>
        simp only [hilbertQuarter_zero, hilbertQuarter_one, hilbertQuarter_two, hilbertQuarter_three,
          true_and, and_true, true_or, or_true, Nat.reduceAdd] <;> omega

/-- T18, Chebyshev form: consecutive cells are at Chebyshev distance 1. -/
theorem hilbert_chebyshev (k d : ℕ) (hd : d + 1 < 4 ^ k) :
    max |((hilbertH k d).1 : ℤ) - (hilbertH k (d + 1)).1|
        |((hilbertH k d).2 : ℤ) - (hilbertH k (d + 1)).2| = 1 := by
  have h := hilbert_locality k d hd
  unfold GridAdjacent at h
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> omega

/-- T19: the four quarters of `H_(k+1)` are the images of `H_k` under the four maps of
Definition 6.1. -/
theorem hilbert_quarters (k r : ℕ) (hr : r < 4 ^ k) :
    hilbertH (k + 1) (0 * 4 ^ k + r) = ((hilbertH k r).2, (hilbertH k r).1) ∧
    hilbertH (k + 1) (1 * 4 ^ k + r) = ((hilbertH k r).1, (hilbertH k r).2 + 2 ^ k) ∧
    hilbertH (k + 1) (2 * 4 ^ k + r) =
      ((hilbertH k r).1 + 2 ^ k, (hilbertH k r).2 + 2 ^ k) ∧
    hilbertH (k + 1) (3 * 4 ^ k + r) =
      (2 * 2 ^ k - 1 - (hilbertH k r).2, 2 ^ k - 1 - (hilbertH k r).1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hilbertH_succ k _ r hr] <;> simp [hilbertQuarter]

#print axioms hilbertH_succ
#print axioms hilbert_index_split
#print axioms hilbertQuarter_maps
#print axioms hilbertQuarter_inj
#print axioms hilbertQuarter_adj
#print axioms hilbert_mapsTo
#print axioms hilbert_injOn
#print axioms hilbert_surjOn
#print axioms hilbert_bijOn
#print axioms hilbert_locality
#print axioms hilbert_chebyshev
#print axioms hilbert_quarters
#print axioms hilbert_start
#print axioms hilbert_end

end Unifier
