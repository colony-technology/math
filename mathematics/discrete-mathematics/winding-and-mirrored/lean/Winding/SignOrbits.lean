import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! # Winding and Mirrored, W9: sign mirrors on division modulo an odd prime

`p` an odd prime, `D = {(a, b) ∈ (Z/p)² : b ≠ 0}`. The four maps `(a, b) ↦ (±a, ±b)` are
`signMap g` for `g : Bool × Bool` (`true` = change that sign); they compose as `Bool × Bool`
under `xor`, the Klein four-group `C2 × C2`. The orbit of `x` is the finset of its four images;
the orbits of `D` are the finset `orbits p` of these finsets. -/

namespace Winding

open Finset

/-- A prime is nonzero, so `ZMod p` is a finite type. -/
instance neZero_of_fact_prime (p : ℕ) [Fact p.Prime] : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- The four sign maps `(a, b) ↦ (±a, ±b)`. -/
def signMap {p : ℕ} (g : Bool × Bool) (x : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (if g.1 then -x.1 else x.1, if g.2 then -x.2 else x.2)

theorem signMap_id {p : ℕ} (x : ZMod p × ZMod p) : signMap (false, false) x = x := by
  simp [signMap]

/-- The sign maps compose as `Bool × Bool` under `xor`. -/
theorem signMap_comp {p : ℕ} (g h : Bool × Bool) (x : ZMod p × ZMod p) :
    signMap g (signMap h x) = signMap (xor g.1 h.1, xor g.2 h.2) x := by
  obtain ⟨g1, g2⟩ := g
  obtain ⟨h1, h2⟩ := h
  cases g1 <;> cases g2 <;> cases h1 <;> cases h2 <;> simp [signMap]

/-- W9(a): `a/b` is carried to `-(a/b)` by either single sign change and to `a/b` by both. -/
theorem signMap_div {p : ℕ} [Fact p.Prime] (x : ZMod p × ZMod p) :
    (signMap (true, false) x).1 / (signMap (true, false) x).2 = -(x.1 / x.2) ∧
    (signMap (false, true) x).1 / (signMap (false, true) x).2 = -(x.1 / x.2) ∧
    (signMap (true, true) x).1 / (signMap (true, true) x).2 = x.1 / x.2 := by
  simp only [signMap, if_true, Bool.false_eq_true, if_false]
  exact ⟨neg_div _ _, div_neg _, neg_div_neg_eq _ _⟩

section Orbits

variable (p : ℕ) [Fact p.Prime]

/-- `D = {(a, b) : b ≠ 0}`. -/
def divDomain : Finset (ZMod p × ZMod p) := univ.filter (fun x => x.2 ≠ 0)

variable {p}

/-- The orbit of `x`: its images under the four sign maps. -/
def signOrbit (x : ZMod p × ZMod p) : Finset (ZMod p × ZMod p) :=
  univ.image (fun g : Bool × Bool => signMap g x)

variable (p)

/-- The set of orbits of `D`. -/
def signOrbits : Finset (Finset (ZMod p × ZMod p)) := (divDomain p).image signOrbit

/-- The representatives: `0 ≤ a ≤ (p-1)/2`, `1 ≤ b ≤ (p-1)/2` as integers. -/
def signReps : Finset (ZMod p × ZMod p) :=
  univ.filter (fun x => x.1.val ≤ (p - 1) / 2 ∧ 1 ≤ x.2.val ∧ x.2.val ≤ (p - 1) / 2)

variable {p}

theorem mem_divDomain (x : ZMod p × ZMod p) : x ∈ divDomain p ↔ x.2 ≠ 0 := by
  simp [divDomain]

theorem signMap_mem (g : Bool × Bool) (x : ZMod p × ZMod p) (hx : x ∈ divDomain p) :
    signMap g x ∈ divDomain p := by
  rw [mem_divDomain] at hx ⊢
  obtain ⟨g1, g2⟩ := g
  cases g2 <;> simp [signMap, hx]

theorem mem_signOrbit (x y : ZMod p × ZMod p) : y ∈ signOrbit x ↔ ∃ g, signMap g x = y := by
  simp [signOrbit]

theorem mem_signOrbit_self (x : ZMod p × ZMod p) : x ∈ signOrbit x :=
  (mem_signOrbit x x).2 ⟨(false, false), signMap_id x⟩

/-- The orbits partition: the orbit of any image of `x` is the orbit of `x`. -/
theorem signOrbit_signMap (g : Bool × Bool) (x : ZMod p × ZMod p) :
    signOrbit (signMap g x) = signOrbit x := by
  ext y
  rw [mem_signOrbit, mem_signOrbit]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨(xor h.1 g.1, xor h.2 g.2), (signMap_comp h g x).symm⟩
  · rintro ⟨h, rfl⟩
    refine ⟨(xor h.1 g.1, xor h.2 g.2), ?_⟩
    rw [signMap_comp]
    congr 1
    obtain ⟨h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := g
    cases h1 <;> cases h2 <;> cases g1 <;> cases g2 <;> rfl

theorem signOrbit_eq_of_mem (x y : ZMod p × ZMod p) (h : y ∈ signOrbit x) :
    signOrbit y = signOrbit x := by
  obtain ⟨g, rfl⟩ := (mem_signOrbit x y).1 h
  exact signOrbit_signMap g x

theorem prime_odd (hp2 : p ≠ 2) : p % 2 = 1 :=
  (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2

theorem val_neg_of_ne_zero (x : ZMod p) (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, if_neg hx]

theorem val_pos_of_ne_zero (x : ZMod p) (hx : x ≠ 0) : 1 ≤ x.val := by
  have : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).1 h)
  omega

/-- For `x ≠ 0` exactly one of `x`, `-x` has value at most `(p-1)/2`. -/
theorem half_unique (hp2 : p ≠ 2) (x : ZMod p) (hx : x ≠ 0) (h : x.val ≤ (p - 1) / 2) :
    ¬ (-x).val ≤ (p - 1) / 2 := by
  have h1 := prime_odd hp2
  have h2 := ZMod.val_lt x
  have h3 := val_pos_of_ne_zero x hx
  rw [val_neg_of_ne_zero x hx]
  omega

theorem half_exists (hp2 : p ≠ 2) (x : ZMod p) (h : ¬ x.val ≤ (p - 1) / 2) :
    (-x).val ≤ (p - 1) / 2 := by
  have h1 := prime_odd hp2
  have h2 := ZMod.val_lt x
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [val_neg_of_ne_zero x hx]
  omega

theorem neg_ne_self_of_ne_zero (hp2 : p ≠ 2) (x : ZMod p) (hx : x ≠ 0) : -x ≠ x := by
  intro h
  have h1 := prime_odd hp2
  have h2 := ZMod.val_lt x
  have := congrArg ZMod.val h
  rw [val_neg_of_ne_zero x hx] at this
  omega

theorem mem_signReps (x : ZMod p × ZMod p) :
    x ∈ signReps p ↔ x.1.val ≤ (p - 1) / 2 ∧ 1 ≤ x.2.val ∧ x.2.val ≤ (p - 1) / 2 := by
  simp [signReps]

theorem signReps_subset : signReps p ⊆ divDomain p := by
  intro x hx
  rw [mem_signReps] at hx
  rw [mem_divDomain]
  intro h
  rw [h, ZMod.val_zero] at hx
  omega

/-- The representative chosen for `x`. -/
def canon (x : ZMod p × ZMod p) : ZMod p × ZMod p :=
  signMap (decide ((p - 1) / 2 < x.1.val), decide ((p - 1) / 2 < x.2.val)) x

theorem canon_mem (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (hx : x ∈ divDomain p) :
    canon x ∈ signReps p := by
  rw [mem_divDomain] at hx
  have h1 := prime_odd hp2
  have hb := val_pos_of_ne_zero x.2 hx
  have hbl := ZMod.val_lt x.2
  rw [mem_signReps]
  unfold canon signMap
  simp only [decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · split_ifs with h
    · exact half_exists hp2 x.1 (by omega)
    · omega
  · split_ifs with h
    · rw [val_neg_of_ne_zero x.2 hx]
      omega
    · omega

/-- Two representatives in one orbit are equal. -/
theorem signReps_unique (hp2 : p ≠ 2) (r r' : ZMod p × ZMod p) (hr : r ∈ signReps p)
    (hr' : r' ∈ signReps p) (h : r' ∈ signOrbit r) : r' = r := by
  obtain ⟨⟨g1, g2⟩, rfl⟩ := (mem_signOrbit r r').1 h
  rw [mem_signReps] at hr hr'
  have hb0 : r.2 ≠ 0 := by
    intro h0
    rw [h0, ZMod.val_zero] at hr
    omega
  cases g2
  · cases g1
    · exact signMap_id r
    · simp only [signMap, if_true, Bool.false_eq_true, if_false] at hr' ⊢
      by_cases ha : r.1 = 0
      · exact Prod.ext (by simp [ha]) rfl
      · exact absurd hr'.1 (half_unique hp2 r.1 ha hr.1)
  · simp only [signMap, if_true] at hr'
    exact absurd hr'.2.2 (half_unique hp2 r.2 hb0 hr.2.2)

/-- W9(b), the representatives: every element of `D` has exactly one representative in its
orbit. -/
theorem signReps_represent (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (hx : x ∈ divDomain p) :
    ∃! r, r ∈ signReps p ∧ r ∈ signOrbit x := by
  refine ⟨canon x, ⟨canon_mem hp2 x hx, (mem_signOrbit _ _).2 ⟨_, rfl⟩⟩, ?_⟩
  rintro r ⟨hr, hrx⟩
  have e1 : signOrbit (canon x) = signOrbit x := signOrbit_signMap _ x
  exact signReps_unique hp2 _ _ (canon_mem hp2 x hx) hr (by rw [e1]; exact hrx)

theorem signOrbits_eq (hp2 : p ≠ 2) : signOrbits p = (signReps p).image signOrbit := by
  ext O
  simp only [signOrbits, mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨canon x, canon_mem hp2 x hx, signOrbit_signMap _ x⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, signReps_subset hr, rfl⟩

theorem signOrbit_injOn (hp2 : p ≠ 2) : Set.InjOn (signOrbit (p := p))
    ((signReps p : Finset (ZMod p × ZMod p)) : Set (ZMod p × ZMod p)) := by
  intro r hr r' hr' h
  have : r' ∈ signOrbit r := by
    rw [h]
    exact mem_signOrbit_self r'
  exact (signReps_unique hp2 r r' hr hr' this).symm

/-- The orbit of `(a, b)` with `a ≠ 0`, `b ≠ 0` has 4 elements. -/
theorem card_signOrbit_four (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (ha : x.1 ≠ 0) (hb : x.2 ≠ 0) :
    (signOrbit x).card = 4 := by
  have ha' := neg_ne_self_of_ne_zero hp2 x.1 ha
  have hb' := neg_ne_self_of_ne_zero hp2 x.2 hb
  have ha'' : x.1 ≠ -x.1 := fun h => ha' h.symm
  have hb'' : x.2 ≠ -x.2 := fun h => hb' h.symm
  unfold signOrbit
  rw [card_image_of_injective]
  · rfl
  · rintro ⟨g1, g2⟩ ⟨h1, h2⟩ heq
    simp only [signMap, Prod.mk.injEq] at heq
    cases g1 <;> cases g2 <;> cases h1 <;> cases h2 <;> simp_all

/-- The orbit of `(0, b)` with `b ≠ 0` has 2 elements. -/
theorem card_signOrbit_two (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (ha : x.1 = 0) (hb : x.2 ≠ 0) :
    (signOrbit x).card = 2 := by
  have hb' := neg_ne_self_of_ne_zero hp2 x.2 hb
  obtain ⟨a, b⟩ := x
  simp only at ha hb hb'
  subst ha
  have e : signOrbit ((0 : ZMod p), b) = {((0 : ZMod p), b), ((0 : ZMod p), -b)} := by
    ext y
    rw [mem_signOrbit]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨g1, g2⟩, rfl⟩
      cases g1 <;> cases g2 <;> simp [signMap]
    · rintro (rfl | rfl)
      · exact ⟨(false, false), by simp [signMap]⟩
      · exact ⟨(false, true), by simp [signMap]⟩
  rw [e, card_pair]
  intro h
  exact hb' (Prod.ext_iff.1 h).2.symm

theorem card_signOrbit_eq_four_iff (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (hx : x ∈ divDomain p) :
    (signOrbit x).card = 4 ↔ x.1 ≠ 0 := by
  rw [mem_divDomain] at hx
  constructor
  · intro h ha
    rw [card_signOrbit_two hp2 x ha hx] at h
    omega
  · intro ha
    exact card_signOrbit_four hp2 x ha hx

theorem card_signOrbit_eq_two_iff (hp2 : p ≠ 2) (x : ZMod p × ZMod p) (hx : x ∈ divDomain p) :
    (signOrbit x).card = 2 ↔ x.1 = 0 := by
  rw [mem_divDomain] at hx
  constructor
  · intro h
    by_contra ha
    rw [card_signOrbit_four hp2 x ha hx] at h
    omega
  · intro ha
    exact card_signOrbit_two hp2 x ha hx

theorem card_signReps : (signReps p).card = ((p - 1) / 2 + 1) * ((p - 1) / 2) := by
  have hlt : (p - 1) / 2 < p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have e : signReps p = ((range ((p - 1) / 2 + 1)) ×ˢ (Icc 1 ((p - 1) / 2))).image
      (fun ij : ℕ × ℕ => (((ij.1 : ℕ) : ZMod p), ((ij.2 : ℕ) : ZMod p))) := by
    ext x
    rw [mem_signReps, mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨(x.1.val, x.2.val), ?_, ?_⟩
      · rw [mem_product, mem_range, mem_Icc]
        exact ⟨by omega, h2, h3⟩
      · simp only [ZMod.natCast_zmod_val]
    · rintro ⟨⟨i, j⟩, hij, rfl⟩
      rw [mem_product, mem_range, mem_Icc] at hij
      simp only
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)]
      exact ⟨by omega, hij.2.1, hij.2.2⟩
  rw [e, card_image_of_injOn, card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel]
  rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
  simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio, coe_Icc, Set.mem_Icc] at hij hij'
  simp only [Prod.mk.injEq] at h
  have h1 := congrArg ZMod.val h.1
  have h2 := congrArg ZMod.val h.2
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1 h2
  rw [h1, h2]

theorem card_signReps_zero :
    ((signReps p).filter (fun r => r.1 = 0)).card = (p - 1) / 2 := by
  have hlt : (p - 1) / 2 < p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have e : (signReps p).filter (fun r => r.1 = 0) =
      (Icc 1 ((p - 1) / 2)).image (fun j : ℕ => ((0 : ZMod p), ((j : ℕ) : ZMod p))) := by
    ext x
    rw [mem_filter, mem_signReps, mem_image]
    constructor
    · rintro ⟨⟨_, h2, h3⟩, h0⟩
      refine ⟨x.2.val, mem_Icc.2 ⟨h2, h3⟩, ?_⟩
      rw [ZMod.natCast_zmod_val, ← h0]
    · rintro ⟨j, hj, rfl⟩
      rw [mem_Icc] at hj
      simp only [ZMod.val_zero, zero_le, true_and, and_true]
      rw [ZMod.val_natCast_of_lt (by omega)]
      exact hj
  rw [e, card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
  intro j hj j' hj' h
  simp only [coe_Icc, Set.mem_Icc] at hj hj'
  simp only [Prod.mk.injEq, true_and] at h
  have h2 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h2

theorem card_divDomain : (divDomain p).card = p * (p - 1) := by
  have e : divDomain p = (univ : Finset (ZMod p)) ×ˢ (univ.erase 0) := by
    ext x
    simp [divDomain, mem_product]
  rw [e, card_product, card_univ, ZMod.card, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

/-- W9(b): `|D| = p(p-1)`; the orbits have size 4 or 2; `(p-1)²/4` of them have size 4
(those with `a ≠ 0`), `(p-1)/2` have size 2 (those with `a = 0`), and there are `(p²-1)/4` in all;
the representatives are counted by `((p+1)/2)((p-1)/2)`. -/
theorem sign_orbits (hp2 : p ≠ 2) :
    (divDomain p).card = p * (p - 1) ∧
    (∀ O ∈ signOrbits p, O.card = 4 ∨ O.card = 2) ∧
    ((signOrbits p).filter (fun O => O.card = 4)).card = (p - 1) ^ 2 / 4 ∧
    ((signOrbits p).filter (fun O => O.card = 2)).card = (p - 1) / 2 ∧
    (signOrbits p).card = (p ^ 2 - 1) / 4 ∧
    (signReps p).card = ((p + 1) / 2) * ((p - 1) / 2) := by
  have hodd := prime_odd hp2
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hm1 : (p - 1) / 2 = m := by omega
  have hm2 : (p + 1) / 2 = m + 1 := by omega
  have hsq1 : (p - 1) ^ 2 / 4 = m * m := by
    have : (p - 1) ^ 2 = 4 * (m * m) := by
      rw [show p - 1 = 2 * m by omega]
      ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hsq2 : (p ^ 2 - 1) / 4 = (m + 1) * m := by
    have : p ^ 2 - 1 = 4 * ((m + 1) * m) := by
      rw [hm]
      ring_nf
      omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hR := card_signReps (p := p)
  have hR0 := card_signReps_zero (p := p)
  rw [hm1] at hR hR0
  have hsplit := card_filter_add_card_filter_not (s := signReps p) (fun r => r.1 = 0)
  have hR1 : ((signReps p).filter (fun r => ¬ r.1 = 0)).card = m * m := by
    have : (m + 1) * m = m * m + m := by ring
    omega
  have hinj := signOrbit_injOn (p := p) hp2
  refine ⟨card_divDomain, ?_, ?_, ?_, ?_, ?_⟩
  · intro O hO
    rw [signOrbits, mem_image] at hO
    obtain ⟨x, hx, rfl⟩ := hO
    by_cases ha : x.1 = 0
    · exact Or.inr ((card_signOrbit_eq_two_iff hp2 x hx).2 ha)
    · exact Or.inl ((card_signOrbit_eq_four_iff hp2 x hx).2 ha)
  · rw [signOrbits_eq hp2, filter_image, hsq1, ← hR1]
    rw [filter_congr (fun r hr => card_signOrbit_eq_four_iff hp2 r (signReps_subset hr))]
    exact card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))
  · rw [signOrbits_eq hp2, filter_image, hm1, ← hR0]
    rw [filter_congr (fun r hr => card_signOrbit_eq_two_iff hp2 r (signReps_subset hr))]
    exact card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))
  · rw [signOrbits_eq hp2, card_image_of_injOn hinj, hR, hsq2]
  · rw [hR, hm1, hm2]

end Orbits

instance fact_prime_97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- W9(c), by (b) at `p = 97`: 9,312 pairs, 2,352 orbits, 2,304 of size 4 and 48 of size 2. -/
theorem sign_orbits_97 :
    (divDomain 97).card = 9312 ∧
    (signOrbits 97).card = 2352 ∧
    ((signOrbits 97).filter (fun O => O.card = 4)).card = 2304 ∧
    ((signOrbits 97).filter (fun O => O.card = 2)).card = 48 := by
  obtain ⟨h1, _, h3, h4, h5, _⟩ := sign_orbits (p := 97) (by norm_num)
  exact ⟨h1.trans (by norm_num), h5.trans (by norm_num), h3.trans (by norm_num),
    h4.trans (by norm_num)⟩

#print axioms signMap_comp
#print axioms signMap_div
#print axioms signMap_mem
#print axioms signOrbit_signMap
#print axioms signReps_represent
#print axioms signOrbits_eq
#print axioms card_signOrbit_four
#print axioms card_signOrbit_two
#print axioms card_signReps
#print axioms card_divDomain
#print axioms sign_orbits
#print axioms sign_orbits_97

end Winding
