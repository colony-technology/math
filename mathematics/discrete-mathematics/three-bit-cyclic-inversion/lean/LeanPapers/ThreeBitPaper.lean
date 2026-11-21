import LeanPapers.ThreeBitCore
import Init.Data.BitVec

namespace ThreeBitCyclic

/-- The exact word representation used by the paper: least-significant bit first. -/
def fromBitVec {w : Nat} (x : BitVec w) : Word w := fun i => x.getLsb i

/-- The paper's map, now defined using fixed-width modular BitVec arithmetic. -/
def paperMap {w : Nat} (x c k : BitVec w) : BitVec w :=
  (x.rotateRight 1 ^^^ x.rotateRight 3) + (x &&& c) + k

theorem bit_fromBitVec_lt {w : Nat} (hw : 0 < w)
    (x : BitVec w) (i : Nat) (hi : i < w) :
    bit hw (fromBitVec x) i = x.getLsbD i := by
  simp [bit, fromBitVec, BitVec.getLsb, BitVec.getLsbD, Nat.mod_eq_of_lt hi]

theorem bit_fromBitVec_mod {w : Nat} (hw : 0 < w)
    (x : BitVec w) (i : Nat) :
    bit hw (fromBitVec x) i = x.getLsbD (i % w) := by
  simp [bit, fromBitVec, BitVec.getLsb, BitVec.getLsbD]

theorem rotate_bit_mod {w : Nat} (hw : 0 < w) (x : BitVec w)
    (r i : Nat) (hr : r < w) (hi : i < w) :
    (x.rotateRight r).getLsbD i = x.getLsbD ((i + r) % w) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  split_ifs with h
  · have hs : i + r < w := by omega
    rw [Nat.mod_eq_of_lt hs]
    congr 1
    omega
  · have hs : w ≤ i + r := by omega
    have ht : i + r - w < w := by omega
    rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt ht]
    simp only [decide_eq_true hi, Bool.true_and]
    congr 1
    omega

theorem rotate_bit_bridge {w : Nat} (hw : 0 < w) (x : BitVec w)
    (r i : Nat) (hr : r < w) (hi : i < w) :
    (x.rotateRight r).getLsbD i = bit hw (fromBitVec x) (i + r) := by
  rw [rotate_bit_mod hw x r i hr hi, bit_fromBitVec_mod]

theorem maj_atLeastTwo (a b c : Bool) :
    maj a b c = a.atLeastTwo b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xor3_reassociate (a b c : Bool) :
    xor3 a b c = a.xor (b.xor c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem fixedCarry_bitvec {w : Nat} (hw : 0 < w)
    (a b : BitVec w) (i : Nat) (hi : i ≤ w) :
    fixedCarry hw (fromBitVec a) (fromBitVec b) i =
      BitVec.carry i a b false := by
  induction i with
  | zero => simp [fixedCarry, BitVec.carry_zero]
  | succ i ih =>
    have hlt : i < w := by omega
    rw [fixedCarry, BitVec.carry_succ, bit_fromBitVec_lt hw a i hlt,
      bit_fromBitVec_lt hw b i hlt, ih (by omega), maj_atLeastTwo]

theorem bitvec_add_bridge {w : Nat} (hw : 0 < w)
    (a b : BitVec w) :
    fromBitVec (a + b) = fixedAdd hw (fromBitVec a) (fromBitVec b) := by
  funext j
  have h := BitVec.getLsbD_add j.isLt a b
  have hc := fixedCarry_bitvec hw a b j.val (Nat.le_of_lt j.isLt)
  change (a + b).getLsbD j.val =
    xor3 (bit hw (fromBitVec a) j.val) (bit hw (fromBitVec b) j.val)
      (fixedCarry hw (fromBitVec a) (fromBitVec b) j.val)
  rw [h, bit_fromBitVec_lt hw a j.val j.isLt,
    bit_fromBitVec_lt hw b j.val j.isLt, hc]
  exact (xor3_reassociate _ _ _).symm

theorem bitvec_and_bridge {w : Nat} (a b : BitVec w) :
    fromBitVec (a &&& b) =
      (fun j => (fromBitVec a j) && (fromBitVec b j) : Word w) := by
  funext j
  exact BitVec.getLsbD_and

theorem bitvec_xor_bridge {w : Nat} (a b : BitVec w) :
    fromBitVec (a ^^^ b) =
      (fun j => (fromBitVec a j).xor (fromBitVec b j) : Word w) := by
  funext j
  exact BitVec.getLsbD_xor

/-- The two rotated word bits, in the exact order used by the manuscript. -/
def rotatedXor {w : Nat} (x : BitVec w) : BitVec w :=
  x.rotateRight 1 ^^^ x.rotateRight 3

theorem rotatedXor_bit {w : Nat} (hw : 4 ≤ w) (x : BitVec w)
    (i : Nat) (hi : i < w) :
    (rotatedXor x).getLsbD i =
      (bit (by omega : 0 < w) (fromBitVec x) (i + 1)).xor
        (bit (by omega : 0 < w) (fromBitVec x) (i + 3)) := by
  have hp : 0 < w := by omega
  simp only [rotatedXor, BitVec.getLsbD_xor]
  rw [rotate_bit_bridge hp x 1 i (by omega) hi,
    rotate_bit_bridge hp x 3 i (by omega) hi]

theorem masked_bit {w : Nat} (hw : 0 < w)
    (x c : BitVec w) (i : Nat) (hi : i < w) :
    (x &&& c).getLsbD i =
      (bit hw (fromBitVec x) i && bit hw (fromBitVec c) i) := by
  simpa only [bit_fromBitVec_lt hw x i hi, bit_fromBitVec_lt hw c i hi] using
    (BitVec.getLsbD_and (x := x) (y := c) (i := i))

theorem innerCarry_bitvec {w : Nat} (hw : 4 ≤ w)
    (x c : BitVec w) (i : Nat) (hi : i ≤ w) :
    carry (by omega : 0 < w) (fromBitVec x) (fromBitVec c) i =
      BitVec.carry i (rotatedXor x) (x &&& c) false := by
  induction i with
  | zero => simp [carry, BitVec.carry_zero]
  | succ i ih =>
    have hlt : i < w := by omega
    rw [carry, BitVec.carry_succ, rotatedXor_bit hw x i hlt,
      masked_bit (by omega : 0 < w) x c i hlt,
      ih (by omega), maj_atLeastTwo]

theorem inner_add_bridge {w : Nat} (hw : 4 ≤ w)
    (x c : BitVec w) :
    fromBitVec (rotatedXor x + (x &&& c)) =
      output (by omega : 0 < w) (fromBitVec x) (fromBitVec c) := by
  have hp : 0 < w := by omega
  funext j
  have h := BitVec.getLsbD_add j.isLt (rotatedXor x) (x &&& c)
  have hc := innerCarry_bitvec hw x c j.val (Nat.le_of_lt j.isLt)
  change (rotatedXor x + (x &&& c)).getLsbD j.val =
    xor3 ((bit hp (fromBitVec x) (j.val + 1)).xor
      (bit hp (fromBitVec x) (j.val + 3)))
      (bit hp (fromBitVec x) j.val && bit hp (fromBitVec c) j.val)
      (carry hp (fromBitVec x) (fromBitVec c) j.val)
  rw [h, rotatedXor_bit hw x j.val j.isLt,
    masked_bit hp x c j.val j.isLt, hc]
  exact (xor3_reassociate _ _ _).symm

/-- Equality of the paper's BitVec map and the independently defined recurrence circuit. -/
theorem paperMap_forward {w : Nat} (hw : 4 ≤ w)
    (x c k : BitVec w) :
    fromBitVec (paperMap x c k) =
      forward (by omega : 0 < w) (fromBitVec x) (fromBitVec c)
        (fromBitVec k) := by
  have hp : 0 < w := by omega
  change fromBitVec ((rotatedXor x + (x &&& c)) + k) = _
  rw [bitvec_add_bridge hp, inner_add_bridge hw]
  rfl

theorem fromBitVec_injective {w : Nat} :
    Function.Injective (fromBitVec (w := w)) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h' := congrArg (fun z : Word w => z ⟨i,hi⟩) h
  exact h'

/-- Theorem 1, directly on the paper's exact fixed-width arithmetic map. -/
theorem paperMap_three_bit_boundary {w : Nat} (hw : 4 ≤ w)
    (x y c k target : BitVec w)
    (hx : paperMap x c k = target)
    (hy : paperMap y c k = target)
    (h0 : x.getLsbD 0 = y.getLsbD 0)
    (h1 : x.getLsbD 1 = y.getLsbD 1)
    (h2 : x.getLsbD 2 = y.getLsbD 2) :
    x = y := by
  have hp : 0 < w := by omega
  have hfx : forward hp (fromBitVec x) (fromBitVec c) (fromBitVec k) =
      fromBitVec target := by
    rw [← paperMap_forward hw]
    exact congrArg fromBitVec hx
  have hfy : forward hp (fromBitVec y) (fromBitVec c) (fromBitVec k) =
      fromBitVec target := by
    rw [← paperMap_forward hw]
    exact congrArg fromBitVec hy
  apply fromBitVec_injective
  apply full_three_bit_boundary hw (fromBitVec x) (fromBitVec y)
    (fromBitVec c) (fromBitVec k) (fromBitVec target) hfx hfy
  · simpa [bit_fromBitVec_lt hp x 0 (by omega),
      bit_fromBitVec_lt hp y 0 (by omega)] using h0
  · simpa [bit_fromBitVec_lt hp x 1 (by omega),
      bit_fromBitVec_lt hp y 1 (by omega)] using h1
  · simpa [bit_fromBitVec_lt hp x 2 (by omega),
      bit_fromBitVec_lt hp y 2 (by omega)] using h2

def bitVecEquivFin (w : Nat) : BitVec w ≃ Fin (2 ^ w) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv := BitVec.ofFin_toFin
  right_inv := BitVec.toFin_ofFin

local instance bitVecFintype (w : Nat) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) (bitVecEquivFin w).symm

/-- Theorem 1: every fiber of the exact published map has cardinality at most eight. -/
theorem paperMap_fiber_card_le_eight {w : Nat} (hw : 4 ≤ w)
    (c k target : BitVec w) :
    Fintype.card {x : BitVec w // paperMap x c k = target} ≤ 8 := by
  classical
  let encode : {x : BitVec w // paperMap x c k = target} →
      Bool × Bool × Bool :=
    fun z => (z.val.getLsbD 0,z.val.getLsbD 1,z.val.getLsbD 2)
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    apply paperMap_three_bit_boundary hw x.val y.val c k target x.property
      y.property
    · exact congrArg (fun t : Bool × Bool × Bool => t.1) h
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.1) h
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.2) h
  have hc := Fintype.card_le_of_injective encode hinj
  have h8 : Fintype.card (Bool × Bool × Bool) = 8 := by decide
  simpa [h8] using hc

#print axioms rotatedXor_bit
#print axioms innerCarry_bitvec
#print axioms inner_add_bridge
#print axioms paperMap_forward
#print axioms paperMap_three_bit_boundary
#print axioms paperMap_fiber_card_le_eight

#print axioms rotate_bit_bridge
#print axioms bitvec_add_bridge
#print axioms bitvec_and_bridge
#print axioms bitvec_xor_bridge
#print axioms bit_fromBitVec_lt
#print axioms bit_fromBitVec_mod
#print axioms rotate_bit_mod
#print axioms maj_atLeastTwo
#print axioms xor3_reassociate
#print axioms fixedCarry_bitvec
#print axioms masked_bit
#print axioms fromBitVec_injective

end ThreeBitCyclic
