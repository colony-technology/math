import LeanPapers.ThreeBitBvExtremal

namespace ThreeBitCyclic

/-- The paper's larger-rotation family with a boundary of r bits. -/
def carryR {w : Nat} (hw : 0 < w) (r : Nat) (x c : Word w) : Nat → Bool
  | 0 => false
  | i + 1 => maj ((bit hw x (i+1)).xor (bit hw x (i+r)))
      (bit hw x i && bit hw c i) (carryR hw r x c i)

def outAtR {w : Nat} (hw : 0 < w) (r : Nat) (x c : Word w)
    (i : Nat) : Bool :=
  xor3 ((bit hw x (i+1)).xor (bit hw x (i+r)))
    (bit hw x i && bit hw c i) (carryR hw r x c i)

def outputR {w : Nat} (hw : 0 < w) (r : Nat) (x c : Word w) : Word w :=
  fun i => outAtR hw r x c i.val

private theorem xor_forced_injective (a b e f m u : Bool)
    (h : xor3 (b.xor e) (a && m) u =
         xor3 (b.xor f) (a && m) u) : e = f := by
  cases a <;> cases b <;> cases e <;> cases f <;>
    cases m <;> cases u <;> simp [xor3] at h ⊢

/-- Proposition 1: all w bits are forced by the first r and an output word. -/
theorem larger_rotation_boundary {w : Nat} (hw : 0 < w)
    (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (x y c target : Word w)
    (hx : outputR hw r x c = target)
    (hy : outputR hw r y c = target)
    (hseed : ∀ j : Nat, j < r → bit hw x j = bit hw y j) :
    x = y := by
  have hout : outputR hw r x c = outputR hw r y c :=
    hx.trans hy.symm
  have hstates : ∀ n : Nat, n ≤ w-r →
      (∀ j : Nat, j < n+r → bit hw x j = bit hw y j) ∧
      carryR hw r x c n = carryR hw r y c n := by
    intro n
    induction n with
    | zero =>
        intro hn
        constructor
        · intro j hj
          exact hseed j (by omega)
        · rfl
    | succ n ih =>
        intro hn
        have hn' : n ≤ w-r := by omega
        have hnlt : n+r < w := by omega
        have hlow := (ih hn').1
        have hcarry := (ih hn').2
        have hn0 : n < n+r := by omega
        have hn1 : n+1 < n+r := by omega
        have houtput : outAtR hw r x c n = outAtR hw r y c n := by
          have h := congrArg (fun z : Word w => z ⟨n, by omega⟩) hout
          simpa [outputR] using h
        have hnext : bit hw x (n+r) = bit hw y (n+r) := by
          apply xor_forced_injective
            (bit hw x n) (bit hw x (n+1))
            (bit hw x (n+r)) (bit hw y (n+r))
            (bit hw c n) (carryR hw r x c n)
          simpa [outAtR, hlow n hn0, hlow (n+1) hn1, hcarry]
            using houtput
        constructor
        · intro j hj
          by_cases h : j < n+r
          · exact hlow j h
          · have heq : j = n+r := by omega
            subst j
            exact hnext
        · simp only [carryR]
          rw [hlow n hn0, hlow (n+1) hn1, hnext, hcarry]
  have hfinal := (hstates (w-r) (by omega)).1
  funext j
  have h := hfinal j.val (by omega : j.val < (w-r)+r)
  simpa [bit, Nat.mod_eq_of_lt j.isLt] using h

/-- Actual fixed-width arithmetic map for general rotation r. -/
def paperMapR {w : Nat} (r : Nat) (x c k : BitVec w) : BitVec w :=
  (x.rotateRight 1 ^^^ x.rotateRight r) + (x &&& c) + k

def rotatedXorR {w : Nat} (r : Nat) (x : BitVec w) : BitVec w :=
  x.rotateRight 1 ^^^ x.rotateRight r

theorem rotatedXorR_bit {w : Nat} (hw : 0 < w)
    (r : Nat) (hr1 : 1 < w) (hrr : r < w)
    (x : BitVec w) (i : Nat) (hi : i < w) :
    (rotatedXorR r x).getLsbD i =
       (bit hw (fromBitVec x) (i+1)).xor
          (bit hw (fromBitVec x) (i+r)) := by
  simp only [rotatedXorR, BitVec.getLsbD_xor]
  rw [rotate_bit_bridge hw x 1 i hr1 hi,
      rotate_bit_bridge hw x r i hrr hi]

theorem innerCarryR_bitvec {w : Nat} (hw : 0 < w)
    (r : Nat) (hr1 : 1 < w) (hrr : r < w)
    (x c : BitVec w) (i : Nat) (hi : i ≤ w) :
    carryR hw r (fromBitVec x) (fromBitVec c) i =
      BitVec.carry i (rotatedXorR r x) (x &&& c) false := by
  induction i with
  | zero => simp [carryR, BitVec.carry_zero]
  | succ i ih =>
    have hlt : i < w := by omega
    rw [carryR, BitVec.carry_succ,
      rotatedXorR_bit hw r hr1 hrr x i hlt,
      masked_bit hw x c i hlt, ih (by omega), maj_atLeastTwo]

theorem inner_addR_bridge {w : Nat} (hw : 0 < w)
    (r : Nat) (hr1 : 1 < w) (hrr : r < w) (x c : BitVec w) :
    fromBitVec (rotatedXorR r x + (x &&& c)) =
      outputR hw r (fromBitVec x) (fromBitVec c) := by
  funext j
  have h := BitVec.getLsbD_add j.isLt (rotatedXorR r x) (x &&& c)
  have hc := innerCarryR_bitvec hw r hr1 hrr x c j.val
    (Nat.le_of_lt j.isLt)
  change (rotatedXorR r x + (x &&& c)).getLsbD j.val =
    xor3 ((bit hw (fromBitVec x) (j.val+1)).xor
      (bit hw (fromBitVec x) (j.val+r)))
      (bit hw (fromBitVec x) j.val && bit hw (fromBitVec c) j.val)
      (carryR hw r (fromBitVec x) (fromBitVec c) j.val)
  rw [h, rotatedXorR_bit hw r hr1 hrr x j.val j.isLt,
    masked_bit hw x c j.val j.isLt, hc]
  exact (xor3_reassociate _ _ _).symm

theorem paperMapR_forward {w : Nat} (hw : 0 < w)
    (r : Nat) (hr1 : 1 < w) (hrr : r < w)
    (x c k : BitVec w) :
    fromBitVec (paperMapR r x c k) =
      fixedAdd hw (outputR hw r (fromBitVec x) (fromBitVec c))
        (fromBitVec k) := by
  change fromBitVec ((rotatedXorR r x + (x &&& c)) + k) = _
  rw [bitvec_add_bridge hw, inner_addR_bridge hw r hr1 hrr]

theorem paperMapR_boundary {w : Nat} (hw : 0 < w)
    (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (x y c k target : BitVec w)
    (hx : paperMapR r x c k = target)
    (hy : paperMapR r y c k = target)
    (hseed : ∀ j : Nat, j < r → x.getLsbD j = y.getLsbD j) :
    x = y := by
  have hr1 : 1 < w := by omega
  have hfx := congrArg fromBitVec (hx.trans hy.symm)
  rw [paperMapR_forward hw r hr1 hrw,
      paperMapR_forward hw r hr1 hrw] at hfx
  have hinner : outputR hw r (fromBitVec x) (fromBitVec c) =
      outputR hw r (fromBitVec y) (fromBitVec c) :=
    fixedAdd_injective hw _ _ (fromBitVec k) hfx
  apply fromBitVec_injective
  apply larger_rotation_boundary hw r hr2 hrw
    (fromBitVec x) (fromBitVec y) (fromBitVec c)
    (outputR hw r (fromBitVec x) (fromBitVec c)) rfl hinner.symm
  intro j hj
  have hjw : j < w := by omega
  simpa [bit_fromBitVec_lt hw x j hjw,
    bit_fromBitVec_lt hw y j hjw] using hseed j hj

local instance bitVecFintypeR (w : Nat) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) (bitVecEquivFin w).symm

/-- Proposition (larger cyclic boundary): at most 2^r full-map preimages. -/
theorem paperMapR_fiber_card_le {w : Nat}
    (hw : 0 < w) (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (c k target : BitVec w) :
    Fintype.card {x : BitVec w // paperMapR r x c k = target} ≤ 2 ^ r := by
  classical
  let encode : {x : BitVec w // paperMapR r x c k = target} →
      (Fin r → Bool) := fun z j => z.val.getLsbD j.val
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    apply paperMapR_boundary hw r hr2 hrw
      x.val y.val c k target x.property y.property
    intro j hj
    have heq := congrArg (fun z : Fin r → Bool => z ⟨j,hj⟩) h
    exact heq
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_pi_const, Fintype.card_bool] using hcard

#print axioms larger_rotation_boundary
#print axioms inner_addR_bridge
#print axioms paperMapR_forward
#print axioms paperMapR_boundary
#print axioms paperMapR_fiber_card_le

#print axioms xor_forced_injective
#print axioms rotatedXorR_bit
#print axioms innerCarryR_bitvec

end ThreeBitCyclic
