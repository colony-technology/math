import LeanPapers.ThreeBitCompletion

namespace ThreeBitCyclic

/-- The r-coordinate shift register with one arithmetic carry bit. -/
structure RState (r : Nat) where
  cells : Fin r → Bool
  carry : Bool

theorem RState.ext {r : Nat} {a b : RState r}
    (hc : a.cells = b.cells) (hu : a.carry = b.carry) : a = b := by
  cases a with
  | mk aa au =>
    cases b with
    | mk ba bu =>
      cases hc
      cases hu
      rfl

/-- One local step; the register shifts and the unique new input bit appends. -/
def stepR (r : Nat) (hr : 2 ≤ r) (mask target : Bool)
    (s : RState r) : RState r :=
  let b := s.cells ⟨0,by omega⟩ && mask
  let q := xor3 target b s.carry
  let newBit := (s.cells ⟨1,by omega⟩).xor q
  { cells := fun j =>
      if h : j.val + 1 < r then s.cells ⟨j.val+1,h⟩ else newBit
    carry := maj q b s.carry }

def originalStateR {w : Nat} (hw : 0 < w) (r : Nat)
    (x c : Word w) (i : Nat) : RState r :=
  { cells := fun j => bit hw x (i+j.val)
    carry := carryR hw r x c i }

private theorem xor3_involutive (a b u : Bool) :
    xor3 (xor3 a b u) b u = a := by
  cases a <;> cases b <;> cases u <;> rfl

theorem stepR_original {w : Nat} (hw : 0 < w) (r : Nat)
    (hr : 2 ≤ r) (x c : Word w) (i : Nat) :
    stepR r hr (bit hw c i) (outAtR hw r x c i)
      (originalStateR hw r x c i) =
    originalStateR hw r x c (i+1) := by
  have hq :
    xor3 (outAtR hw r x c i)
      (bit hw x i && bit hw c i) (carryR hw r x c i) =
        (bit hw x (i+1)).xor (bit hw x (i+r)) := by
    simpa [outAtR] using
      (xor3_involutive ((bit hw x (i+1)).xor (bit hw x (i+r)))
        (bit hw x i && bit hw c i) (carryR hw r x c i))
  apply RState.ext
  · funext j
    change (if h : j.val+1<r then
      bit hw x (i+(j.val+1)) else
      (bit hw x (i+1)).xor
        (xor3 (outAtR hw r x c i)
          (bit hw x i && bit hw c i) (carryR hw r x c i))) =
        bit hw x ((i+1)+j.val)
    split_ifs with h
    · congr 1; omega
    · have hj : j.val+1=r := by omega
      rw [hq]
      have hi : (i+1)+j.val = i+r := by omega
      rw [hi]
      cases (bit hw x (i+1)) <;> cases (bit hw x (i+r)) <;> rfl
  · change maj (xor3 (outAtR hw r x c i)
      (bit hw x i && bit hw c i) (carryR hw r x c i))
      (bit hw x i && bit hw c i) (carryR hw r x c i) =
        carryR hw r x c (i+1)
    rw [hq]
    rfl

/-- Computable packing of little-endian bits into a fixed-width modular word. -/
def toBitVec {w : Nat} (x : Word w) : BitVec w :=
  BitVec.ofNat w (Nat.ofBits x)

theorem fromBitVec_toBitVec {w : Nat} (x : Word w) :
    fromBitVec (toBitVec x) = x := by
  funext i
  change (BitVec.ofNat w (Nat.ofBits x)).getLsbD i.val = x i
  rw [BitVec.getLsbD_ofNat, Nat.testBit_ofBits]
  simp [i.isLt]

theorem toBitVec_fromBitVec {w : Nat} (x : BitVec w) :
    toBitVec (fromBitVec x) = x :=
  fromBitVec_injective (fromBitVec_toBitVec (fromBitVec x))

/-- An r-bit initial boundary, indexed from the least significant bit. -/
def seedOfR {w : Nat} (hw : 0 < w) (r : Nat) (x : Word w) :
    Fin r → Bool := fun j => bit hw x j.val

/-- Exactly one shift-register transition is executed at each successor. -/
def runSeedR {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (c target : Word w)
    (seed : Fin r → Bool) : Nat → RState r
  | 0 => ⟨seed,false⟩
  | i + 1 => stepR r hr (bit hw c i) (bit hw target i)
      (runSeedR hw r hr c target seed i)

/-- Recover the first w bits along one deterministic boundary path. -/
def candidateR {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (c target : Word w)
    (seed : Fin r → Bool) : Word w :=
  fun j => (runSeedR hw r hr c target seed j.val).cells ⟨0,by omega⟩

def closesR {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (c target : Word w)
    (seed : Fin r → Bool) : Prop :=
  (runSeedR hw r hr c target seed w).cells = seed

/-- Every true inverse path is the exact deterministic r-bit recurrence path. -/
theorem runSeedR_complete {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (x c target : Word w)
    (hx : outputR hw r x c = target) :
    ∀ i : Nat, i ≤ w →
      runSeedR hw r hr c target (seedOfR hw r x) i =
        originalStateR hw r x c i := by
  intro i
  induction i with
  | zero =>
      intro _
      apply RState.ext
      · funext j
        simp [runSeedR, originalStateR, seedOfR]
      · rfl
  | succ i ih =>
      intro hi
      have hlt : i < w := by omega
      have ht : outAtR hw r x c i = bit hw target i := by
        have h := congrArg (fun z : Word w => z ⟨i,hlt⟩) hx
        simpa [outputR,bit,Nat.mod_eq_of_lt hlt] using h
      calc
        runSeedR hw r hr c target (seedOfR hw r x) (i+1) =
          stepR r hr (bit hw c i) (bit hw target i)
            (runSeedR hw r hr c target (seedOfR hw r x) i) := rfl
        _ = stepR r hr (bit hw c i) (outAtR hw r x c i)
            (originalStateR hw r x c i) := by rw [ht, ih (by omega)]
        _ = originalStateR hw r x c (i+1) :=
          stepR_original hw r hr x c i

/-- Every preimage closes cyclically and is recovered from its first r bits. -/
theorem candidateR_complete {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (hrw : r < w)
    (x c target : Word w) (hx : outputR hw r x c = target) :
    closesR hw r hr c target (seedOfR hw r x) ∧
    candidateR hw r hr c target (seedOfR hw r x) = x := by
  have hrun := runSeedR_complete hw r hr x c target hx
  constructor
  · funext j
    have hh := congrArg (fun st : RState r => st.cells j)
      (hrun w (by omega))
    have hjw : j.val < w := by omega
    have hperiod : bit hw x (w + j.val) = bit hw x j.val := by
      simp [bit,Nat.add_mod,Nat.mod_eq_of_lt hjw]
    simpa [closesR,originalStateR,seedOfR,hperiod] using hh
  · funext j
    have hh := congrArg (fun st : RState r => st.cells ⟨0,by omega⟩)
      (hrun j.val (Nat.le_of_lt j.isLt))
    simpa [candidateR,originalStateR,bit,Nat.mod_eq_of_lt j.isLt]
      using hh

theorem paperMapR_target_sub {w : Nat} (r : Nat)
    (x c k target : BitVec w) :
    paperMapR r x c k = target ↔
      rotatedXorR r x + (x &&& c) = target - k := by
  constructor
  · intro h
    have hh := congrArg (fun z : BitVec w => z - k) h
    simpa only [paperMapR,rotatedXorR,BitVec.add_sub_cancel] using hh
  · intro h
    have hh := congrArg (fun z : BitVec w => z + k) h
    simpa only [paperMapR,rotatedXorR,BitVec.sub_add_cancel] using hh

theorem paperMapR_output_target {w : Nat}
    (hw : 0 < w) (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (x c k target : BitVec w) (hx : paperMapR r x c k = target) :
    outputR hw r (fromBitVec x) (fromBitVec c) =
      fromBitVec (target - k) := by
  have hh := congrArg fromBitVec
    ((paperMapR_target_sub r x c k target).mp hx)
  rw [inner_addR_bridge hw r (by omega) hrw] at hh
  exact hh

def closesRBool {w : Nat} (hw : 0 < w) (r : Nat) (hr : 2 ≤ r)
    (c target : Word w) (seed : Fin r → Bool) : Bool :=
  decide (List.ofFn (runSeedR hw r hr c target seed w).cells =
      List.ofFn seed)

theorem closesRBool_true_iff {w : Nat} (hw : 0 < w)
    (r : Nat) (hr : 2 ≤ r) (c target : Word w)
    (seed : Fin r → Bool) :
    closesRBool hw r hr c target seed = true ↔
      closesR hw r hr c target seed := by
  simp only [closesRBool, decide_eq_true_eq, closesR]
  constructor
  · intro h
    exact List.ofFn_injective h
  · intro h
    rw [h]

/-- Enumerate 2^r seeds. Each seed makes w deterministic updates,
and a final direct equality check validates the candidate. -/
def recoverR {w : Nat}
    (hw : 0 < w) (r : Nat) (hr : 2 ≤ r)
    (c k target : BitVec w) : Finset (BitVec w) :=
  let cWord := fromBitVec c
  let tWord := fromBitVec (target - k)
  let propose := fun seed : Fin r → Bool =>
    toBitVec (candidateR hw r hr cWord tWord seed)
  ((Finset.univ : Finset (Fin r → Bool)).filter
    (fun seed => (closesRBool hw r hr cWord tWord seed &&
      decide (paperMapR r (propose seed) c k = target)) = true)).image propose

/-- The exact inverse for every rotation 2 ≤ r < w. -/
theorem recoverR_exact {w : Nat}
    (hw : 0 < w) (r : Nat) (hr : 2 ≤ r) (hrw : r < w)
    (c k target x : BitVec w) :
    x ∈ recoverR hw r hr c k target ↔ paperMapR r x c k = target := by
  classical
  simp only [recoverR, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq,
    closesRBool_true_iff]
  constructor
  · rintro ⟨s, ⟨hc,hvalid⟩, heq⟩
    rw [← heq]
    exact hvalid
  · intro hx
    let cWord := fromBitVec c
    let tWord := fromBitVec (target - k)
    let xWord := fromBitVec x
    let s := seedOfR hw r xWord
    have houtput : outputR hw r xWord cWord = tWord :=
      paperMapR_output_target hw r hr hrw x c k target hx
    have hcomplete := candidateR_complete hw r hr hrw xWord cWord tWord houtput
    have hpack : toBitVec (candidateR hw r hr cWord tWord s) = x := by
      rw [hcomplete.2, toBitVec_fromBitVec]
    refine ⟨s, ⟨hcomplete.1, ?_⟩, hpack⟩
    change paperMapR r (toBitVec (candidateR hw r hr cWord tWord s)) c k = target
    rw [hpack]
    exact hx

/-- The propagation-loop update budget over every r-bit boundary seed. -/
def generalLocalUpdates (r w : Nat) : Nat :=
  Fintype.card (Fin r → Bool) * w

theorem general_r_w_local_updates (r w : Nat) :
    generalLocalUpdates r w = 2 ^ r * w := by
  simp [generalLocalUpdates,Fintype.card_pi_const,Fintype.card_bool]

#print axioms fromBitVec_toBitVec
#print axioms stepR_original
#print axioms runSeedR_complete
#print axioms candidateR_complete
#print axioms paperMapR_output_target
#print axioms recoverR_exact
#print axioms general_r_w_local_updates

#print axioms stepR_original
#print axioms RState.ext
#print axioms xor3_involutive
#print axioms toBitVec_fromBitVec
#print axioms paperMapR_target_sub
#print axioms closesRBool_true_iff

end ThreeBitCyclic
