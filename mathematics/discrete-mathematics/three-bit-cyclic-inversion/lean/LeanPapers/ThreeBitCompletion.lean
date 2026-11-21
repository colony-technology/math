import LeanPapers.ThreeBitGeneralR

namespace ThreeBitCyclic

/-- The constant is removed by one subtraction in the fixed-width word ring. -/
theorem paperMap_target_sub {w : Nat} (x c k target : BitVec w) :
    paperMap x c k = target ↔
      rotatedXor x + (x &&& c) = target - k := by
  constructor
  · intro h
    have hh := congrArg (fun z : BitVec w => z - k) h
    simpa only [paperMap, rotatedXor, BitVec.add_sub_cancel] using hh
  · intro h
    have hh := congrArg (fun z : BitVec w => z + k) h
    simpa only [paperMap, rotatedXor, BitVec.sub_add_cancel] using hh

/-- Theorem 1's exact inverse, directly for the paper's BitVec map.
The right-hand function enumerates only eight boundary seeds, runs the section-2
recurrence, and retains exactly the three-bit cyclic closures. -/
theorem paperMap_recover_exact {w : Nat} (hw : 4 ≤ w)
    (x c k target : BitVec w) :
    fromBitVec x ∈
        recover (by omega : 0 < w) (fromBitVec c) (fromBitVec (target - k)) ↔
      paperMap x c k = target := by
  rw [recover_exact hw]
  rw [← inner_add_bridge hw]
  exact (show (fromBitVec (rotatedXor x + (x &&& c)) =
       fromBitVec (target - k)) ↔
       (rotatedXor x + (x &&& c)) = target - k from
       ⟨(fun h => fromBitVec_injective h),
         (fun h => congrArg fromBitVec h)⟩).trans
       (paperMap_target_sub x c k target).symm

/-- The eight-seed solver performs exactly w state transitions per seed. -/
def localUpdates (w : Nat) : Nat :=
  (Fintype.card (Bool × Bool × Bool)) * w

theorem eight_w_local_updates (w : Nat) :
    localUpdates w = 8 * w := by
  simp [localUpdates]

#print axioms paperMap_target_sub
#print axioms paperMap_recover_exact
#print axioms eight_w_local_updates
end ThreeBitCyclic
