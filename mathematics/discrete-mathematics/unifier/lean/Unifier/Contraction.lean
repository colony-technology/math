import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

/-! # The Unifier: Section 2, exact state contraction -/

universe u v w

namespace Unifier

structure ExactContraction (X : Type u) (B : Type v) where
  boundary : X → B
  equiv : X → X → Prop
  sound : ∀ x y, boundary x = boundary y → equiv x y

def observationSetoid {X : Type u} {I : Type v}
    {V : I → Type w} (O : (i : I) → X → V i) : Setoid X where
  r x y := ∀ i, O i x = O i y
  iseqv := ⟨
    (by intro x i; rfl),
    (by intro x y h i; exact (h i).symm),
    (by intro x y z h₁ h₂ i; exact (h₁ i).trans (h₂ i))⟩

def retainedBoundary {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) : Prop :=
  ∀ x y, b x = b y → s.r x y

def exactBoundary {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) : Prop :=
  ∀ x y, (s.r x y ↔ b x = b y)

theorem quotient_projection_exact {X : Type u}
    (s : Setoid X) (x y : X) :
    (Quotient.mk s x = Quotient.mk s y) ↔ s.r x y := by
  exact ⟨Quotient.exact, Quotient.sound⟩

theorem quotient_projection_surjective {X : Type u}
    (s : Setoid X) :
    Function.Surjective (Quotient.mk s) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

noncomputable def factorBoundary {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B)
    (_hb : retainedBoundary s b) :
    Set.range b → Quotient s :=
  fun z => Quotient.mk s (Classical.choose z.property)

theorem factorBoundary_spec {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) (hb : retainedBoundary s b) (x : X) :
    factorBoundary s b hb ⟨b x, ⟨x, rfl⟩⟩ = Quotient.mk s x := by
  apply Quotient.sound
  apply hb
  exact Classical.choose_spec (show b x ∈ Set.range b from ⟨x, rfl⟩)

theorem factorBoundary_unique {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) (hb : retainedBoundary s b)
    (r : Set.range b → Quotient s)
    (hr : ∀ x, r ⟨b x, ⟨x, rfl⟩⟩ = Quotient.mk s x) :
    r = factorBoundary s b hb := by
  funext z
  rcases z.property with ⟨x, hx⟩
  have hz : z = ⟨b x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  rw [hz, hr x, factorBoundary_spec]

theorem factorBoundary_surjective {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) (hb : retainedBoundary s b) :
    Function.Surjective (factorBoundary s b hb) := by
  intro q
  obtain ⟨x, rfl⟩ := quotient_projection_surjective s q
  exact ⟨⟨b x, ⟨x, rfl⟩⟩, factorBoundary_spec s b hb x⟩

theorem quotient_finite {X : Type u} {B : Type v} [Finite B]
    (s : Setoid X) (b : X → B) (hb : retainedBoundary s b) :
    Finite (Quotient s) := by
  exact Finite.of_surjective
    (factorBoundary s b hb) (factorBoundary_surjective s b hb)

theorem quotient_card_le {X : Type u} {B : Type v} [Fintype B]
    (s : Setoid X) [Fintype (Quotient s)]
    (b : X → B) (hb : retainedBoundary s b) :
    Fintype.card (Quotient s) ≤ Fintype.card B := by
  classical
  have hsurj := factorBoundary_surjective s b hb
  calc
    Fintype.card (Quotient s) ≤ Fintype.card (Set.range b) :=
      Fintype.card_le_of_surjective _ hsurj
    _ ≤ Fintype.card B := Fintype.card_subtype_le _

noncomputable def exactBoundaryEquiv {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B)
    (he : exactBoundary s b) (hs : Function.Surjective b) :
    B ≃ Quotient s :=
  Equiv.ofBijective
    (fun y : B => Quotient.mk s (Classical.choose (hs y)))
    ⟨(by
      intro y z h
      have hr : s.r (Classical.choose (hs y)) (Classical.choose (hs z)) :=
        Quotient.exact h
      have hbe := (he _ _).mp hr
      calc
        y = b (Classical.choose (hs y)) := (Classical.choose_spec (hs y)).symm
        _ = b (Classical.choose (hs z)) := hbe
        _ = z := Classical.choose_spec (hs z)),
     (by
      intro q
      obtain ⟨x, rfl⟩ := quotient_projection_surjective s q
      refine ⟨b x, ?_⟩
      apply Quotient.sound
      exact (he _ _).mpr (Classical.choose_spec (hs (b x))))⟩

theorem exactBoundaryEquiv_spec {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B)
    (he : exactBoundary s b) (hs : Function.Surjective b) (x : X) :
    exactBoundaryEquiv s b he hs (b x) = Quotient.mk s x := by
  apply Quotient.sound
  exact (he _ _).mpr (Classical.choose_spec (hs (b x)))

theorem exactBoundaryEquiv_unique {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B)
    (he : exactBoundary s b) (hs : Function.Surjective b)
    (e : B ≃ Quotient s)
    (h : ∀ x, e (b x) = Quotient.mk s x) :
    e = exactBoundaryEquiv s b he hs := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact (h x).trans (exactBoundaryEquiv_spec s b he hs x).symm

#print axioms observationSetoid
#print axioms quotient_projection_exact
#print axioms quotient_projection_surjective
#print axioms factorBoundary_spec
#print axioms factorBoundary_unique
#print axioms factorBoundary_surjective
#print axioms quotient_finite
#print axioms quotient_card_le
#print axioms exactBoundaryEquiv_spec
#print axioms exactBoundaryEquiv_unique

end Unifier
