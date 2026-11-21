import LeanPapers.ThreeBitRecovery

namespace ThreeBitCyclic

def flipTriple (s : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (!s.1, !s.2.1, !s.2.2)

def stateFromZ (s : Bool × Bool × Bool) : State :=
  ⟨!s.1,!s.2.1,!s.2.2,false⟩

theorem flipTriple_involutive (s : Bool × Bool × Bool) :
    flipTriple (flipTriple s) = s := by
  rcases s with ⟨a,b,d⟩
  cases a <;> cases b <;> cases d <;> decide

theorem flipTriple_injective : Function.Injective flipTriple := by
  intro s t h
  have hh := congrArg flipTriple h
  simpa [flipTriple_involutive] using hh

theorem step_true_true (z : Bool × Bool × Bool) :
    step true true (stateFromZ z) = stateFromZ (linearStep z) := by
  rcases z with ⟨a,b,d⟩
  cases a <;> cases b <;> cases d <;> rfl

theorem bit_allOnes {w : Nat} (hw : 0 < w) (i : Nat) :
    bit hw (allOnes w) i = true := rfl

theorem runSeed_allOnes {w : Nat} (hw : 0 < w)
    (z : Bool × Bool × Bool) (i : Nat) :
    runSeed hw (allOnes w) (allOnes w) (flipTriple z) i =
      stateFromZ ((linearStep^[i]) z) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change step true true (runSeed hw (allOnes w) (allOnes w)
        (flipTriple z) i) = stateFromZ ((linearStep^[i+1]) z)
      rw [ih, step_true_true, Function.iterate_succ_apply']

theorem closes_allOnes_iff {w : Nat} (hw : 0 < w)
    (z : Bool × Bool × Bool) :
    closes hw (allOnes w) (allOnes w) (flipTriple z) ↔
      (linearStep^[w]) z = z := by
  have h : closes hw (allOnes w) (allOnes w) (flipTriple z) ↔
      flipTriple ((linearStep^[w]) z) = flipTriple z := by
    change ((runSeed hw (allOnes w) (allOnes w) (flipTriple z) w).a =
      (flipTriple z).1 ∧
      (runSeed hw (allOnes w) (allOnes w) (flipTriple z) w).b =
      (flipTriple z).2.1 ∧
      (runSeed hw (allOnes w) (allOnes w) (flipTriple z) w).d =
      (flipTriple z).2.2) ↔ _
    rw [runSeed_allOnes]
    simp [stateFromZ, flipTriple, Prod.mk.injEq]
  rw [h]
  constructor
  · intro heq
    exact flipTriple_injective heq
  · intro heq
    rw [heq]

theorem candidate_zero_is_allOnes {w : Nat} (hw : 0 < w) :
    candidate hw (allOnes w) (allOnes w)
      (flipTriple zeroTriple) = allOnes w := by
  funext j
  change (runSeed hw (allOnes w) (allOnes w)
    (flipTriple zeroTriple) j.val).a = true
  rw [runSeed_allOnes]
  have hf : linearStep zeroTriple = zeroTriple := rfl
  rw [Function.iterate_fixed hf]
  rfl

/-- An accepted seed necessarily recovers its own three boundary coordinates. -/
theorem candidate_seed_coordinates {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) (s : Bool × Bool × Bool) :
    candidate (by omega : 0 < w) c target s ⟨0,by omega⟩ = s.1 ∧
    candidate (by omega : 0 < w) c target s ⟨1,by omega⟩ = s.2.1 ∧
    candidate (by omega : 0 < w) c target s ⟨2,by omega⟩ = s.2.2 := by
  simp [candidate, runSeed, step]

theorem candidate_seed_injective {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) :
    Function.Injective (candidate (by omega : 0 < w) c target) := by
  intro s t h
  have hs := candidate_seed_coordinates hw c target s
  have ht := candidate_seed_coordinates hw c target t
  have h0 := congrArg (fun x : Word w => x ⟨0,by omega⟩) h
  have h1 := congrArg (fun x : Word w => x ⟨1,by omega⟩) h
  have h2 := congrArg (fun x : Word w => x ⟨2,by omega⟩) h
  apply Prod.ext
  · exact hs.1.symm.trans (h0.trans ht.1)
  · apply Prod.ext
    · exact hs.2.1.symm.trans (h1.trans ht.2.1)
    · exact hs.2.2.symm.trans (h2.trans ht.2.2)

/-- Every full-period boundary seed closes and gives a distinct preimage. -/
theorem allOnes_eight_if_seven_divides {w : Nat}
    (hw : 4 ≤ w) (h7 : 7 ∣ w) :
    Fintype.card {x : Word w //
      output (by omega : 0 < w) x (allOnes w) = allOnes w} = 8 := by
  have hp : 0 < w := by omega
  classical
  let construct : (Bool × Bool × Bool) →
      {x : Word w // output hp x (allOnes w) = allOnes w} :=
    fun z => ⟨candidate hp (allOnes w) (allOnes w) (flipTriple z),
      candidate_sound hw _ _ _ ((closes_allOnes_iff hp z).2
        ((linearStep_fixed_iff z w).2 (Or.inl h7)))⟩
  have hinj : Function.Injective construct := by
    intro s t h
    have hh := congrArg (fun x :
      {x : Word w // output hp x (allOnes w) = allOnes w} => x.val) h
    have hseed := candidate_seed_injective hw (allOnes w) (allOnes w) hh
    exact flipTriple_injective hseed
  have hlow := Fintype.card_le_of_injective construct hinj
  have hh : Fintype.card (Bool × Bool × Bool) = 8 := by decide
  have hhigh := fiber_card_le_eight hw (allOnes w) (allOnes w)
  omega

theorem allOnes_is_preimage {w : Nat} (hw : 4 ≤ w) :
    output (by omega : 0 < w) (allOnes w) (allOnes w) =
      allOnes w := by
  have hp : 0 < w := by omega
  have hz : (linearStep^[w]) zeroTriple = zeroTriple :=
    Function.iterate_fixed (by rfl) w
  have hc := (closes_allOnes_iff hp zeroTriple).2 hz
  have ho := candidate_sound hw (allOnes w) (allOnes w)
    (flipTriple zeroTriple) hc
  simpa [candidate_zero_is_allOnes hp] using ho

/-- The unique preimage at every width not divisible by seven is all ones. -/
theorem allOnes_unique_if_not_seven {w : Nat}
    (hw : 4 ≤ w) (h7 : ¬7 ∣ w)
    (x : Word w)
    (hx : output (by omega : 0 < w) x (allOnes w) = allOnes w) :
    x = allOnes w := by
  have hp : 0 < w := by omega
  have hcomplete := candidate_complete hw x (allOnes w) (allOnes w) hx
  let z := flipTriple (seedOf hp x)
  have hseed : flipTriple z = seedOf hp x := by
    simp [z,flipTriple_involutive]
  have hc : closes hp (allOnes w) (allOnes w) (flipTriple z) := by
    rw [hseed]
    exact hcomplete.1
  have hfix : (linearStep^[w]) z = z :=
    (closes_allOnes_iff hp z).mp hc
  have hz : z = zeroTriple :=
    ((linearStep_fixed_iff z w).mp hfix).resolve_left h7
  calc
    x = candidate hp (allOnes w) (allOnes w) (seedOf hp x) :=
      hcomplete.2.symm
    _ = candidate hp (allOnes w) (allOnes w) (flipTriple zeroTriple) := by
      rw [← hz, hseed]
    _ = allOnes w := candidate_zero_is_allOnes hp

/-- The paper's exact extremal family, for every width at least four. -/
theorem allOnes_fiber_card_exact {w : Nat} (hw : 4 ≤ w) :
    Fintype.card {x : Word w //
      output (by omega : 0 < w) x (allOnes w) = allOnes w} =
      (if 7 ∣ w then 8 else 1) := by
  split_ifs with h7
  · exact allOnes_eight_if_seven_divides hw h7
  · classical
    have he : output (by omega : 0 < w) (allOnes w) (allOnes w) =
      allOnes w := allOnes_is_preimage hw
    let eqv : {x : Word w //
      output (by omega : 0 < w) x (allOnes w) = allOnes w} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨allOnes w, he⟩
        left_inv := by
          intro x
          apply Subtype.ext
          exact (allOnes_unique_if_not_seven hw h7 x.val x.property).symm
        right_inv := by intro x; cases x; rfl }
    simpa using (Fintype.card_congr eqv)

#print axioms flipTriple_involutive
#print axioms runSeed_allOnes
#print axioms closes_allOnes_iff
#print axioms candidate_seed_injective
#print axioms allOnes_eight_if_seven_divides
#print axioms allOnes_unique_if_not_seven
#print axioms allOnes_fiber_card_exact

#print axioms flipTriple_injective
#print axioms step_true_true
#print axioms bit_allOnes
#print axioms candidate_zero_is_allOnes
#print axioms candidate_seed_coordinates
#print axioms allOnes_is_preimage

end ThreeBitCyclic
