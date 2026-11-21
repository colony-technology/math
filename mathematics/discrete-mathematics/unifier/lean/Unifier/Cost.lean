import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Prod
import Mathlib.Logic.Equiv.Set

/-! # The Unifier: T21, the minimal trit cost and independent product -/

universe u v w w'

namespace Unifier

def tritCost {X : Type u} {Y : Type v} (f : X → Y)
    [Fintype (Set.range f)] : ℕ :=
  Nat.clog 3 (Fintype.card (Set.range f))

theorem trit_cost_key_card (L : ℕ) :
    Fintype.card (Fin L → Fin 3) = 3 ^ L := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem range_card_le_of_factorization {X : Type u} {Y : Type v}
    {M : Type w} (f : X → Y) [Fintype (Set.range f)] [Fintype M]
    (dec : X → M) (enc : M → Y)
    (h : ∀ x, f x = enc (dec x)) :
    Fintype.card (Set.range f) ≤ Fintype.card M := by
  classical
  let g : Set.range f → M := fun y => dec (Classical.choose y.property)
  have hg : Function.Injective g := by
    intro y z he
    apply Subtype.ext
    calc
      y.val = f (Classical.choose y.property) :=
        (Classical.choose_spec y.property).symm
      _ = enc (dec (Classical.choose y.property)) := h _
      _ = enc (dec (Classical.choose z.property)) := congrArg enc he
      _ = f (Classical.choose z.property) := (h _).symm
      _ = z.val := Classical.choose_spec z.property
  exact Fintype.card_le_of_injective g hg

theorem trit_cost_factorization {X : Type u} {Y : Type v}
    (f : X → Y) [Fintype (Set.range f)]
    (hpos : 0 < Fintype.card (Set.range f)) :
    ∃ (dec : X → (Fin (tritCost f) → Fin 3))
      (enc : (Fin (tritCost f) → Fin 3) → Y),
      ∀ x, f x = enc (dec x) := by
  classical
  have hle : Fintype.card (Set.range f) ≤
      Fintype.card (Fin (tritCost f) → Fin 3) := by
    rw [trit_cost_key_card]
    exact Nat.le_pow_clog (by decide : 1 < 3) _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  haveI : Nonempty (Set.range f) := Fintype.card_pos_iff.mp hpos
  refine ⟨(fun x => e ⟨f x, ⟨x, rfl⟩⟩),
      (fun key => (Function.invFun (⇑e) key).val), ?_⟩
  intro x
  have hleft := Function.leftInverse_invFun e.injective
    (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)
  exact congrArg Subtype.val hleft.symm

theorem trit_cost_minimal {X : Type u} {Y : Type v}
    (f : X → Y) [Fintype (Set.range f)] (L : ℕ)
    (dec : X → (Fin L → Fin 3))
    (enc : (Fin L → Fin 3) → Y)
    (h : ∀ x, f x = enc (dec x)) :
    tritCost f ≤ L := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 3)).2
  have hc := range_card_le_of_factorization f dec enc h
  simpa [trit_cost_key_card] using hc

theorem clog3_mul_upper (m n : ℕ) :
    Nat.clog 3 (m * n) ≤ Nat.clog 3 m + Nat.clog 3 n := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 3)).2
  calc
    m * n ≤ (3 ^ Nat.clog 3 m) * (3 ^ Nat.clog 3 n) :=
      Nat.mul_le_mul
        (Nat.le_pow_clog (by decide : 1 < 3) m)
        (Nat.le_pow_clog (by decide : 1 < 3) n)
    _ = 3 ^ (Nat.clog 3 m + Nat.clog 3 n) := (pow_add _ _ _).symm

theorem clog3_pow_lt_three_mul (m : ℕ) (hm : 0 < m) :
    3 ^ (Nat.clog 3 m) < 3 * m := by
  by_cases ha0 : Nat.clog 3 m = 0
  · rw [ha0]
    simp
    omega
  · have ha : 0 < Nat.clog 3 m := Nat.pos_of_ne_zero ha0
    have hprev : 3 ^ (Nat.clog 3 m - 1) < m :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 3)).1
        (Nat.sub_one_lt ha0)
    have heq : 3 ^ Nat.clog 3 m = 3 * 3 ^ (Nat.clog 3 m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ha]
      simp [pow_add, Nat.mul_comm]
    rw [heq]
    exact Nat.mul_lt_mul_of_pos_left hprev (by decide : 0 < 3)

theorem clog3_mul_lower (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.clog 3 m + Nat.clog 3 n ≤ Nat.clog 3 (m * n) + 1 := by
  let a := Nat.clog 3 m
  let b := Nat.clog 3 n
  let c := Nat.clog 3 (m * n)
  have ha : 3 ^ a < 3 * m := clog3_pow_lt_three_mul m hm
  have hb : 3 ^ b < 3 * n := clog3_pow_lt_three_mul n hn
  have hbpos : 0 < 3 ^ b := by positivity
  have hmp : 0 < 3 * m := by omega
  have hprod : 3 ^ a * 3 ^ b < (3 * m) * (3 * n) := by
    calc
      3 ^ a * 3 ^ b < (3 * m) * 3 ^ b :=
        Nat.mul_lt_mul_of_pos_right ha hbpos
      _ < (3 * m) * (3 * n) :=
        Nat.mul_lt_mul_of_pos_left hb hmp
  have hpow : 3 ^ (a + b) < 3 ^ (c + 2) := by
    calc
      3 ^ (a + b) = 3 ^ a * 3 ^ b := pow_add _ _ _
      _ < (3 * m) * (3 * n) := hprod
      _ = 9 * (m * n) := by ring
      _ ≤ 9 * (3 ^ c) :=
        Nat.mul_le_mul_left 9 (Nat.le_pow_clog (by decide : 1 < 3) (m * n))
      _ = 3 ^ (c + 2) := by
        rw [pow_add]
        ring
  have hlt : a + b < c + 2 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).1 hpow
  omega

/-- The range of the independent product is the product of the two ranges. -/
def independentRangeEquiv
    {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type w'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂) :
    Set.range (Prod.map f₁ f₂) ≃ Set.range f₁ × Set.range f₂ where
  toFun p :=
    (⟨p.1.1, by
        obtain ⟨⟨a, b⟩, h⟩ := p.2
        exact ⟨a, congrArg Prod.fst h⟩⟩,
     ⟨p.1.2, by
        obtain ⟨⟨a, b⟩, h⟩ := p.2
        exact ⟨b, congrArg Prod.snd h⟩⟩)
  invFun q :=
    ⟨(q.1.1, q.2.1), by
      obtain ⟨a, ha⟩ := q.1.2
      obtain ⟨b, hb⟩ := q.2.2
      exact ⟨(a, b), Prod.ext ha hb⟩⟩
  left_inv p := Subtype.ext rfl
  right_inv q := Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

theorem independent_range_card
    {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type w'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    [Fintype (Set.range f₁)] [Fintype (Set.range f₂)]
    [Fintype (Set.range (Prod.map f₁ f₂))] :
    Fintype.card (Set.range (Prod.map f₁ f₂)) =
      Fintype.card (Set.range f₁) * Fintype.card (Set.range f₂) := by
  rw [Fintype.card_congr (independentRangeEquiv f₁ f₂), Fintype.card_prod]

/-- T21(c): `cost (f₁ × f₂) ≤ cost f₁ + cost f₂ ≤ cost (f₁ × f₂) + 1` for the independent
product `Prod.map f₁ f₂ : X₁ × X₂ → Y₁ × Y₂`, `(x₁, x₂) ↦ (f₁ x₁, f₂ x₂)`, when both ranges
are finite and nonempty. -/
theorem independent_product_tritCost
    {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type w'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    [Fintype (Set.range f₁)] [Fintype (Set.range f₂)]
    [Fintype (Set.range (Prod.map f₁ f₂))]
    (h₁ : 0 < Fintype.card (Set.range f₁))
    (h₂ : 0 < Fintype.card (Set.range f₂)) :
    tritCost (Prod.map f₁ f₂) ≤ tritCost f₁ + tritCost f₂ ∧
    tritCost f₁ + tritCost f₂ ≤ tritCost (Prod.map f₁ f₂) + 1 := by
  unfold tritCost
  rw [independent_range_card f₁ f₂]
  exact ⟨clog3_mul_upper _ _, clog3_mul_lower _ _ h₁ h₂⟩

/-- Remark beside T21(c): for the pairing `x ↦ (f₁ x, f₂ x)` on one common domain the
second inequality fails. With `X = Fin 9` and `f₁ = f₂ = id` each cost is 2 and the
pairing has cost 2, so `cost f₁ + cost f₂ ≤ cost pairing + 1` would read `4 ≤ 3`. -/
theorem correlated_pairing_counterexample :
    tritCost (fun x : Fin 9 => x) = 2 ∧
    tritCost (fun x : Fin 9 => (x, x)) = 2 ∧
    ¬ (tritCost (fun x : Fin 9 => x) + tritCost (fun x : Fin 9 => x) ≤
        tritCost (fun x : Fin 9 => (x, x)) + 1) := by
  have h9 : Nat.clog 3 9 = 2 := Nat.clog_pow 3 2 (by decide)
  have hid : tritCost (fun x : Fin 9 => x) = 2 := by
    unfold tritCost
    rw [Set.card_range_of_injective (fun a b h => h), Fintype.card_fin, h9]
  have hpair : tritCost (fun x : Fin 9 => (x, x)) = 2 := by
    unfold tritCost
    rw [Set.card_range_of_injective (fun a b h => congrArg Prod.fst h),
      Fintype.card_fin, h9]
  refine ⟨hid, hpair, ?_⟩
  rw [hid, hpair]
  omega

#print axioms tritCost
#print axioms trit_cost_key_card
#print axioms range_card_le_of_factorization
#print axioms trit_cost_factorization
#print axioms trit_cost_minimal
#print axioms clog3_mul_upper
#print axioms clog3_pow_lt_three_mul
#print axioms clog3_mul_lower
#print axioms independent_range_card
#print axioms independent_product_tritCost
#print axioms correlated_pairing_counterexample

end Unifier
