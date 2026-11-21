import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Defs

/-! # The Unifier: Section 7, universal exact factorization -/

universe u v

namespace Unifier

structure Factorization {X : Type u} {Y : Type v} (f : X → Y) where
  Q : Type v
  K : Type v
  dec : X → Q
  tau : Q ≃ K
  enc : K → Y
  dec_surjective : Function.Surjective dec
  enc_injective : Function.Injective enc
  reconstruct : ∀ x, f x = enc (tau (dec x))

noncomputable def canonicalFactorization {X : Type u} {Y : Type v}
    (f : X → Y) : Factorization f where
  Q := Set.range f
  K := Set.range f
  dec := fun x => ⟨f x, ⟨x, rfl⟩⟩
  tau := Equiv.refl _
  enc := Subtype.val
  dec_surjective := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩
  enc_injective := Subtype.val_injective
  reconstruct := by intro x; rfl

theorem unifier_exists {X : Type u} {Y : Type v} (f : X → Y) :
    Nonempty (Factorization f) :=
  ⟨canonicalFactorization f⟩

noncomputable def factorDecMap {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) : F.Q → G.Q :=
  fun q => G.dec (Classical.choose (F.dec_surjective q))

theorem factorDecMap_spec {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) (x : X) :
    factorDecMap F G (F.dec x) = G.dec x := by
  unfold factorDecMap
  have hc := Classical.choose_spec (F.dec_surjective (F.dec x))
  apply G.tau.injective
  apply G.enc_injective
  calc
    G.enc (G.tau (G.dec (Classical.choose (F.dec_surjective (F.dec x))))) =
        f (Classical.choose (F.dec_surjective (F.dec x))) :=
      (G.reconstruct _).symm
    _ = F.enc (F.tau (F.dec (Classical.choose (F.dec_surjective (F.dec x))))) :=
      F.reconstruct _
    _ = F.enc (F.tau (F.dec x)) := by rw [hc]
    _ = f x := (F.reconstruct x).symm
    _ = G.enc (G.tau (G.dec x)) := G.reconstruct x

theorem factorDecMap_injective {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) :
    Function.Injective (factorDecMap F G) := by
  intro q r h
  obtain ⟨x, rfl⟩ := F.dec_surjective q
  obtain ⟨y, rfl⟩ := F.dec_surjective r
  have hdec : G.dec x = G.dec y := by
    simpa only [factorDecMap_spec] using h
  apply F.tau.injective
  apply F.enc_injective
  calc
    F.enc (F.tau (F.dec x)) = f x := (F.reconstruct x).symm
    _ = G.enc (G.tau (G.dec x)) := G.reconstruct x
    _ = G.enc (G.tau (G.dec y)) := by rw [hdec]
    _ = f y := (G.reconstruct y).symm
    _ = F.enc (F.tau (F.dec y)) := F.reconstruct y

theorem factorDecMap_surjective {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) :
    Function.Surjective (factorDecMap F G) := by
  intro q
  obtain ⟨x, rfl⟩ := G.dec_surjective q
  exact ⟨F.dec x, factorDecMap_spec F G x⟩

noncomputable def factorAlpha {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) : F.Q ≃ G.Q :=
  Equiv.ofBijective (factorDecMap F G)
    ⟨factorDecMap_injective F G, factorDecMap_surjective F G⟩

noncomputable def factorPhi {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) : F.K ≃ G.K :=
  F.tau.symm.trans ((factorAlpha F G).trans G.tau)

def FactorIsomorphism {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f)
    (α : F.Q ≃ G.Q) (φ : F.K ≃ G.K) : Prop :=
  (∀ x, α (F.dec x) = G.dec x) ∧
  (∀ q, φ (F.tau q) = G.tau (α q)) ∧
  (∀ k, G.enc (φ k) = F.enc k)

theorem canonical_iso {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) :
    FactorIsomorphism F G (factorAlpha F G) (factorPhi F G) := by
  constructor
  · exact factorDecMap_spec F G
  constructor
  · intro q
    simp [factorPhi]
  · intro k
    obtain ⟨x, hx⟩ := F.dec_surjective (F.tau.symm k)
    have hk : F.tau (F.dec x) = k := by rw [hx]; simp
    calc
      G.enc (factorPhi F G k) =
          G.enc (G.tau (factorAlpha F G (F.tau.symm k))) := by
            simp [factorPhi]
      _ = G.enc (G.tau (G.dec x)) := by
        rw [← hx]
        change G.enc (G.tau (factorDecMap F G (F.dec x))) = _
        rw [factorDecMap_spec]
      _ = f x := (G.reconstruct x).symm
      _ = F.enc (F.tau (F.dec x)) := F.reconstruct x
      _ = F.enc k := by rw [hk]

theorem unique_iso {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f)
    (α : F.Q ≃ G.Q) (φ : F.K ≃ G.K)
    (h : FactorIsomorphism F G α φ) :
    α = factorAlpha F G ∧ φ = factorPhi F G := by
  have ha : α = factorAlpha F G := by
    apply Equiv.ext
    intro q
    obtain ⟨x, rfl⟩ := F.dec_surjective q
    exact (h.1 x).trans (factorDecMap_spec F G x).symm
  refine ⟨ha, ?_⟩
  apply Equiv.ext
  intro k
  have ht : φ (F.tau (F.tau.symm k)) =
      G.tau (α (F.tau.symm k)) := h.2.1 (F.tau.symm k)
  have hc : φ k = G.tau (α (F.tau.symm k)) := by simpa using ht
  rw [hc, ha]
  simp [factorPhi]

theorem unifier_unique_factorization {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) :
    ∃! p : (F.Q ≃ G.Q) × (F.K ≃ G.K),
      FactorIsomorphism F G p.1 p.2 := by
  refine ⟨⟨factorAlpha F G, factorPhi F G⟩, canonical_iso F G, ?_⟩
  intro p hp
  rcases p with ⟨α, φ⟩
  obtain ⟨rfl, rfl⟩ := unique_iso F G α φ hp
  rfl

#print axioms unifier_exists
#print axioms factorDecMap_spec
#print axioms factorDecMap_injective
#print axioms factorDecMap_surjective
#print axioms canonical_iso
#print axioms unique_iso
#print axioms unifier_unique_factorization

end Unifier
