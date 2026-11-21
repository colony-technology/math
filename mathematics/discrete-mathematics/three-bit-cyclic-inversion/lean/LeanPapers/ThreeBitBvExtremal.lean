import LeanPapers.ThreeBitExtremal
import Mathlib.Data.Fintype.BigOperators

namespace ThreeBitCyclic

local instance bitVecFintype' (w : Nat) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) (bitVecEquivFin w).symm

theorem word_card (w : Nat) : Fintype.card (Word w) = 2 ^ w := by
  simpa [Word, Fintype.card_bool] using
    (Fintype.card_pi_const Bool w)

theorem bitVec_card (w : Nat) : Fintype.card (BitVec w) = 2 ^ w := by
  simpa using (Fintype.card_congr (bitVecEquivFin w))

noncomputable def bitVecWordEquiv (w : Nat) : BitVec w ≃ Word w :=
  Equiv.ofBijective fromBitVec
    ((Fintype.bijective_iff_injective_and_card fromBitVec).2
      ⟨fromBitVec_injective, (bitVec_card w).trans (word_card w).symm⟩)

theorem fromBitVec_allOnes {w : Nat} :
    fromBitVec (BitVec.allOnes w) = allOnes w := by
  funext j
  simp [fromBitVec,BitVec.getLsb,BitVec.getLsbD_allOnes,j.isLt,allOnes]

theorem paperMap_zero_constant {w : Nat} (x c : BitVec w) :
    paperMap x c (0#w) = rotatedXor x + (x &&& c) := by
  simp [paperMap,rotatedXor]

theorem paperMap_allOnes_iff_output {w : Nat} (hw : 4 ≤ w)
    (x : BitVec w) :
    paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w ↔
    output (by omega : 0 < w) (fromBitVec x) (allOnes w) = allOnes w := by
  have hb : fromBitVec
        (paperMap x (BitVec.allOnes w) (0#w)) =
        output (by omega : 0 < w) (fromBitVec x) (allOnes w) := by
    rw [paperMap_zero_constant, inner_add_bridge hw,fromBitVec_allOnes]
  constructor
  · intro hx
    have heq := congrArg fromBitVec hx
    rw [hb,fromBitVec_allOnes] at heq
    exact heq
  · intro hx
    apply fromBitVec_injective
    rw [hb,fromBitVec_allOnes]
    exact hx

/-- Theorem 2, exactly as published, on the fixed-width modular map. -/
theorem paperMap_allOnes_fiber_exact {w : Nat} (hw : 4 ≤ w) :
    Fintype.card {x : BitVec w //
      paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w} =
      (if 7 ∣ w then 8 else 1) := by
  let e : {x : BitVec w //
      paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w} ≃
      {x : Word w // output (by omega : 0 < w) x (allOnes w) = allOnes w} :=
    Equiv.subtypeEquiv (bitVecWordEquiv w) (by
      intro x
      exact paperMap_allOnes_iff_output hw x)
  have hc := Fintype.card_congr e
  exact hc.trans (allOnes_fiber_card_exact hw)

/-- Theorem 2 also identifies the only preimage outside multiples of seven. -/
theorem paperMap_allOnes_unique_if_not_seven {w : Nat}
    (hw : 4 ≤ w) (h7 : ¬7 ∣ w) (x : BitVec w)
    (hx : paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w) :
    x = BitVec.allOnes w := by
  apply fromBitVec_injective
  rw [fromBitVec_allOnes]
  exact allOnes_unique_if_not_seven hw h7 (fromBitVec x)
    ((paperMap_allOnes_iff_output hw x).mp hx)

#print axioms word_card
#print axioms bitVec_card
#print axioms paperMap_allOnes_iff_output
#print axioms paperMap_allOnes_fiber_exact
#print axioms paperMap_allOnes_unique_if_not_seven

#print axioms fromBitVec_allOnes
#print axioms paperMap_zero_constant

end ThreeBitCyclic
