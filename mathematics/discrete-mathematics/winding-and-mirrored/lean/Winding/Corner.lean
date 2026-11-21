import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Winding and Mirrored, W10: an odd corner is never neutral

A finite multigraph without loops: a finite type `E` of edges, each with two distinct ends
`fst e` and `snd e` (multiple edges allowed). A choice of directions is `o : E → Bool`:
`o e = false` puts the head (north end) of the magnet at `fst e` and the tail at `snd e`,
`o e = true` the reverse. The charge of `v` is (edges with head `v`) − (edges with tail `v`). -/

namespace Winding

open Finset

/-- A finite multigraph without loops. -/
structure Multigraph (V E : Type*) where
  fst : E → V
  snd : E → V
  noLoop : ∀ e, fst e ≠ snd e

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

/-- The head (north end) of edge `e` under the choice of directions `o`. -/
def Multigraph.head (G : Multigraph V E) (o : E → Bool) (e : E) : V :=
  if o e then G.snd e else G.fst e

/-- The tail (south end) of edge `e` under the choice of directions `o`. -/
def Multigraph.tail (G : Multigraph V E) (o : E → Bool) (e : E) : V :=
  if o e then G.fst e else G.snd e

/-- The degree of `v`: the number of edge ends at `v`. It does not depend on directions. -/
def Multigraph.degree (G : Multigraph V E) (v : V) : ℕ :=
  #{e | G.fst e = v} + #{e | G.snd e = v}

/-- The charge `q(v) = #(heads at v) - #(tails at v)`. -/
def Multigraph.charge (G : Multigraph V E) (o : E → Bool) (v : V) : ℤ :=
  (#{e | G.head o e = v} : ℤ) - #{e | G.tail o e = v}

namespace Multigraph

variable (G : Multigraph V E)

/-- The degree is the number of edges incident to `v` (no loops, so no edge counts twice). -/
theorem degree_eq_incident (v : V) : G.degree v = #{e | G.fst e = v ∨ G.snd e = v} := by
  unfold degree
  rw [← card_union_of_disjoint, filter_or]
  rw [disjoint_filter]
  intro e _ h1 h2
  exact G.noLoop e (h1.trans h2.symm)

/-- For every choice of directions, `deg v = #(heads at v) + #(tails at v)`. -/
theorem degree_eq_head_tail (o : E → Bool) (v : V) :
    G.degree v = #{e | G.head o e = v} + #{e | G.tail o e = v} := by
  unfold degree
  simp only [card_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  unfold head tail
  cases o e <;> simp [add_comm]

/-- W10(a): `q(v)` has the parity of `deg v`, for every choice of directions. -/
theorem charge_parity (o : E → Bool) (v : V) : G.charge o v % 2 = (G.degree v : ℤ) % 2 := by
  rw [degree_eq_head_tail G o v, charge]
  push_cast
  omega

/-- W10(a): a vertex of odd degree has nonzero charge, for every choice of directions. -/
theorem charge_ne_zero_of_odd (o : E → Bool) (v : V) (h : G.degree v % 2 = 1) :
    G.charge o v ≠ 0 := by
  intro h0
  have := charge_parity G o v
  rw [h0] at this
  omega

/-- W10(b): the charges sum to `0`. -/
theorem charge_sum [Fintype V] (o : E → Bool) : ∑ v, G.charge o v = 0 := by
  unfold charge
  rw [sum_sub_distrib]
  have h1 : ∑ v, (#{e | G.head o e = v} : ℤ) = Fintype.card E := by
    rw [← Nat.cast_sum, ← card_univ,
      card_eq_sum_card_fiberwise (f := G.head o) (t := univ) (fun _ _ => mem_univ _)]
  have h2 : ∑ v, (#{e | G.tail o e = v} : ℤ) = Fintype.card E := by
    rw [← Nat.cast_sum, ← card_univ,
      card_eq_sum_card_fiberwise (f := G.tail o) (t := univ) (fun _ _ => mem_univ _)]
  rw [h1, h2, sub_self]

/-- W10(c): at a vertex of degree 3 the charge is `3`, `1`, `-1` or `-3`. -/
theorem charge_degree_three (o : E → Bool) (v : V) (h : G.degree v = 3) :
    G.charge o v = 3 ∨ G.charge o v = 1 ∨ G.charge o v = -1 ∨ G.charge o v = -3 := by
  rw [degree_eq_head_tail G o v] at h
  unfold charge
  omega

/-- The directions that put the heads of the edges in `S` at `v` and the tails of the other
edges at `v` (for edges incident to `v`). -/
def pointing (v : V) (S : Finset E) (e : E) : Bool :=
  if e ∈ S then decide (G.snd e = v) else decide (G.fst e = v)

theorem head_pointing (v : V) (S : Finset E) (hS : ∀ e ∈ S, G.fst e = v ∨ G.snd e = v)
    (e : E) : G.head (G.pointing v S) e = v ↔ e ∈ S := by
  have hl := G.noLoop e
  unfold head pointing
  by_cases he : e ∈ S
  · have := hS e he
    by_cases h2 : G.snd e = v
    · simp [he, h2]
    · simp [he, h2]
      tauto
  · by_cases h1 : G.fst e = v
    · simp only [he, if_false, h1, decide_true, if_true, iff_false]
      intro h
      exact hl (h1.trans h.symm)
    · simp [he, h1]

theorem tail_pointing (v : V) (S : Finset E) (e : E) :
    G.tail (G.pointing v S) e = v ↔ e ∉ S ∧ (G.fst e = v ∨ G.snd e = v) := by
  have hl := G.noLoop e
  unfold tail pointing
  by_cases he : e ∈ S
  · by_cases h2 : G.snd e = v
    · simp only [he, if_true, h2, decide_true, not_true_eq_false, false_and, iff_false]
      intro h
      exact hl (h.trans h2.symm)
    · simp [he, h2]
  · by_cases h1 : G.fst e = v
    · simp [he, h1]
    · simp [he, h1]

/-- W10(c): at a vertex of degree 3 each of the values `3, 1, -1, -3` is the charge for some
choice of directions. -/
theorem charge_degree_three_attained (v : V) (h : G.degree v = 3) (t : ℤ)
    (ht : t = 3 ∨ t = 1 ∨ t = -1 ∨ t = -3) : ∃ o : E → Bool, G.charge o v = t := by
  classical
  set I : Finset E := univ.filter (fun e => G.fst e = v ∨ G.snd e = v) with hI
  have hIc : #I = 3 := by rw [hI, ← degree_eq_incident, h]
  -- the number of heads at `v`
  obtain ⟨h0, hh0, rfl⟩ : ∃ h0 : ℕ, h0 ≤ 3 ∧ t = 2 * (h0 : ℤ) - 3 := by
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨3, le_refl _, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨0, by norm_num, by norm_num⟩
  obtain ⟨S, hSI, hSc⟩ := exists_subset_card_eq (s := I) (n := h0) (by omega)
  have hS : ∀ e ∈ S, G.fst e = v ∨ G.snd e = v := by
    intro e he
    have := hSI he
    rw [hI, mem_filter] at this
    exact this.2
  refine ⟨G.pointing v S, ?_⟩
  have eh : (univ.filter fun e => G.head (G.pointing v S) e = v) = S := by
    ext e
    rw [mem_filter, head_pointing G v S hS]
    simp
  have et : (univ.filter fun e => G.tail (G.pointing v S) e = v) = I \ S := by
    ext e
    rw [mem_filter, tail_pointing, mem_sdiff, hI, mem_filter]
    simp only [mem_univ, true_and]
    tauto
  unfold charge
  rw [eh, et, card_sdiff_of_subset hSI, hIc, hSc]
  push_cast [show h0 ≤ 3 from hh0]
  ring

theorem head_iff (o : E → Bool) (e : E) (v : V) :
    G.head o e = v ↔ (G.fst e = v ∨ G.snd e = v) ∧ G.head o e = v := by
  unfold head
  constructor
  · intro h
    refine ⟨?_, h⟩
    cases hoe : o e <;> simp only [hoe, Bool.false_eq_true, ↓reduceIte] at h
    · exact Or.inl h
    · exact Or.inr h
  · exact fun h => h.2

theorem tail_iff (o : E → Bool) (e : E) (v : V) :
    G.tail o e = v ↔ (G.fst e = v ∨ G.snd e = v) ∧ G.head o e ≠ v := by
  have hl := G.noLoop e
  unfold head tail
  cases o e
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro rfl
      exact ⟨Or.inr rfl, hl⟩
    · rintro ⟨h | h, hne⟩
      · exact absurd h hne
      · exact h
  · simp only [↓reduceIte]
    constructor
    · rintro rfl
      exact ⟨Or.inl rfl, fun h => hl h.symm⟩
    · rintro ⟨h | h, hne⟩
      · exact h
      · exact absurd h hne

/-- At a vertex `v`, the charge counts the incident edges pointing in minus those pointing out:
it depends only on the directions of the edges at `v`. -/
theorem charge_local (o : E → Bool) (v : V) :
    G.charge o v = (#{e | (G.fst e = v ∨ G.snd e = v) ∧ G.head o e = v} : ℤ) -
      #{e | (G.fst e = v ∨ G.snd e = v) ∧ G.head o e ≠ v} := by
  unfold charge
  rw [filter_congr (fun e _ => head_iff G o e v), filter_congr (fun e _ => tail_iff G o e v)]

end Multigraph

/-- The charge at a corner of three edges, as a function of the choice `c i = true` (edge `i`
points into the corner) or `false` (it points out). -/
def cornerCharge (c : Fin 3 → Bool) : ℤ := (#{i | c i = true} : ℤ) - #{i | c i = false}

/-- W10(c): of the 8 choices of directions at a corner of three edges, the charges `3, 1, -1, -3`
occur 1, 3, 3 and 1 times. -/
theorem cornerCharge_counts :
    #{c : Fin 3 → Bool | cornerCharge c = 3} = 1 ∧
    #{c : Fin 3 → Bool | cornerCharge c = 1} = 3 ∧
    #{c : Fin 3 → Bool | cornerCharge c = -1} = 3 ∧
    #{c : Fin 3 → Bool | cornerCharge c = -3} = 1 ∧
    Fintype.card (Fin 3 → Bool) = 8 := by
  decide

namespace Multigraph

variable (G : Multigraph V E)

/-- Counting incident edges with a property along an enumeration of the incident edges. -/
theorem card_incident_enum (v : V) (e : Fin 3 → E) (he : Function.Injective e)
    (hI : ∀ x, (G.fst x = v ∨ G.snd x = v) ↔ ∃ i, e i = x) (p : E → Prop) [DecidablePred p] :
    #{x | (G.fst x = v ∨ G.snd x = v) ∧ p x} = #{i : Fin 3 | p (e i)} := by
  have hc := card_image_of_injective (univ.filter fun i : Fin 3 => p (e i)) he
  rw [← hc]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_image, hI]
  constructor
  · rintro ⟨⟨i, rfl⟩, hp⟩
    exact ⟨i, hp, rfl⟩
  · rintro ⟨i, hp, rfl⟩
    exact ⟨⟨i, rfl⟩, hp⟩

/-- W10(c): at a vertex of degree 3, the charge is the corner charge of its three edges. -/
theorem charge_eq_cornerCharge (o : E → Bool) (v : V) (h : G.degree v = 3) :
    ∃ e : Fin 3 → E, Function.Injective e ∧
      (∀ x, (G.fst x = v ∨ G.snd x = v) ↔ ∃ i, e i = x) ∧
      G.charge o v = cornerCharge (fun i => decide (G.head o (e i) = v)) := by
  rw [degree_eq_incident] at h
  let eqv := Finset.equivFinOfCardEq h
  have hinj : Function.Injective (fun i => (eqv.symm i).1) :=
    Subtype.val_injective.comp eqv.symm.injective
  have hI : ∀ x, (G.fst x = v ∨ G.snd x = v) ↔ ∃ i, (fun i => (eqv.symm i).1) i = x := by
    intro x
    constructor
    · intro hx
      refine ⟨eqv ⟨x, ?_⟩, ?_⟩
      · simpa using hx
      · simp
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp (eqv.symm i).2).2
  refine ⟨fun i => (eqv.symm i).1, hinj, hI, ?_⟩
  have h1 := G.card_incident_enum v _ hinj hI (fun x => G.head o x = v)
  have h2 := G.card_incident_enum v _ hinj hI (fun x => G.head o x ≠ v)
  rw [charge_local, h1, h2]
  unfold cornerCharge
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]

end Multigraph

#print axioms Multigraph.degree_eq_incident
#print axioms Multigraph.degree_eq_head_tail
#print axioms Multigraph.charge_parity
#print axioms Multigraph.charge_ne_zero_of_odd
#print axioms Multigraph.charge_sum
#print axioms Multigraph.charge_degree_three
#print axioms Multigraph.charge_degree_three_attained
#print axioms Multigraph.charge_local
#print axioms cornerCharge_counts
#print axioms Multigraph.card_incident_enum
#print axioms Multigraph.charge_eq_cornerCharge

end Winding
