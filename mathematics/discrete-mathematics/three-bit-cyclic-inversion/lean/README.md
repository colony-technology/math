# Lean 4 formalization

**lmtlssss🜐 · 21 November 2026**

Every numbered result of the paper is proved in Lean 4.35.0 with Mathlib v4.35.0. The map is the paper's map on `BitVec w`:

```lean
def paperMap {w : Nat} (x c k : BitVec w) : BitVec w :=
  (x.rotateRight 1 ^^^ x.rotateRight 3) + (x &&& c) + k
```

| Paper | Lean theorems |
| --- | --- |
| Theorem 1, the three-bit boundary, the complete inverse, at most eight preimages, 8w updates | `paperMap_three_bit_boundary`, `paperMap_recover_exact`, `paperMap_fiber_card_le_eight`, `eight_w_local_updates` |
| Theorem 2, eight preimages when seven divides w and one otherwise, for every w >= 4 | `paperMap_allOnes_fiber_exact`, `paperMap_allOnes_unique_if_not_seven` |
| Proposition, the r-bit boundary for 2 <= r < w | `paperMapR_boundary`, `recoverR_exact`, `paperMapR_fiber_card_le`, `general_r_w_local_updates` |

`paperMap_forward` and `paperMapR_forward` tie the `BitVec` maps to the bit-level recurrence used in the proofs. Theorem 2 is proved for all widths from the seven-cycle of the recurrence, with no enumeration of widths.

The ten files contain 85 theorems. None uses `sorry`, `native_decide` or an added axiom. `#print axioms` on each of the twelve theorems named above reports `propext`, `Classical.choice` and `Quot.sound`.

The count 8w is the number of recurrence state updates. Conversion, the three closure checks and writing the output are separate work, as the paper states.

## Rebuild

```sh
lake exe cache get
lake build LeanPapers.ThreeBit
```

A build from deleted outputs on 21 November 2026 completed 808 jobs with exit status 0.

## Statements as compiled

### `ThreeBitCyclic.paperMap_forward`

`LeanPapers/ThreeBitPaper.lean`, line 139

```lean
theorem paperMap_forward {w : Nat} (hw : 4 ≤ w)
    (x c k : BitVec w) :
    fromBitVec (paperMap x c k) =
      forward (by omega : 0 < w) (fromBitVec x) (fromBitVec c)
        (fromBitVec k)
```

```text
info: LeanPapers/ThreeBitPaper.lean:217:0: 'ThreeBitCyclic.paperMap_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMap_three_bit_boundary`

`LeanPapers/ThreeBitPaper.lean`, line 158

```lean
theorem paperMap_three_bit_boundary {w : Nat} (hw : 4 ≤ w)
    (x y c k target : BitVec w)
    (hx : paperMap x c k = target)
    (hy : paperMap y c k = target)
    (h0 : x.getLsbD 0 = y.getLsbD 0)
    (h1 : x.getLsbD 1 = y.getLsbD 1)
    (h2 : x.getLsbD 2 = y.getLsbD 2) :
    x = y
```

```text
info: LeanPapers/ThreeBitPaper.lean:218:0: 'ThreeBitCyclic.paperMap_three_bit_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMap_fiber_card_le_eight`

`LeanPapers/ThreeBitPaper.lean`, line 195

```lean
theorem paperMap_fiber_card_le_eight {w : Nat} (hw : 4 ≤ w)
    (c k target : BitVec w) :
    Fintype.card {x : BitVec w // paperMap x c k = target} ≤ 8
```

```text
info: LeanPapers/ThreeBitPaper.lean:219:0: 'ThreeBitCyclic.paperMap_fiber_card_le_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMap_recover_exact`

`LeanPapers/ThreeBitCompletion.lean`, line 20

```lean
theorem paperMap_recover_exact {w : Nat} (hw : 4 ≤ w)
    (x c k target : BitVec w) :
    fromBitVec x ∈
        recover (by omega : 0 < w) (fromBitVec c) (fromBitVec (target - k)) ↔
      paperMap x c k = target
```

```text
info: LeanPapers/ThreeBitCompletion.lean:43:0: 'ThreeBitCyclic.paperMap_recover_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.eight_w_local_updates`

`LeanPapers/ThreeBitCompletion.lean`, line 38

```lean
theorem eight_w_local_updates (w : Nat) :
    localUpdates w = 8 * w
```

```text
info: LeanPapers/ThreeBitCompletion.lean:44:0: 'ThreeBitCyclic.eight_w_local_updates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMap_allOnes_fiber_exact`

`LeanPapers/ThreeBitBvExtremal.lean`, line 49

```lean
theorem paperMap_allOnes_fiber_exact {w : Nat} (hw : 4 ≤ w) :
    Fintype.card {x : BitVec w //
      paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w} =
      (if 7 ∣ w then 8 else 1)
```

```text
info: LeanPapers/ThreeBitBvExtremal.lean:75:0: 'ThreeBitCyclic.paperMap_allOnes_fiber_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMap_allOnes_unique_if_not_seven`

`LeanPapers/ThreeBitBvExtremal.lean`, line 63

```lean
theorem paperMap_allOnes_unique_if_not_seven {w : Nat}
    (hw : 4 ≤ w) (h7 : ¬7 ∣ w) (x : BitVec w)
    (hx : paperMap x (BitVec.allOnes w) (0#w) = BitVec.allOnes w) :
    x = BitVec.allOnes w
```

```text
info: LeanPapers/ThreeBitBvExtremal.lean:76:0: 'ThreeBitCyclic.paperMap_allOnes_unique_if_not_seven' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMapR_forward`

`LeanPapers/ThreeBitGeneralR.lean`, line 125

```lean
theorem paperMapR_forward {w : Nat} (hw : 0 < w)
    (r : Nat) (hr1 : 1 < w) (hrr : r < w)
    (x c k : BitVec w) :
    fromBitVec (paperMapR r x c k) =
      fixedAdd hw (outputR hw r (fromBitVec x) (fromBitVec c))
        (fromBitVec k)
```

```text
info: LeanPapers/ThreeBitGeneralR.lean:181:0: 'ThreeBitCyclic.paperMapR_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMapR_boundary`

`LeanPapers/ThreeBitGeneralR.lean`, line 134

```lean
theorem paperMapR_boundary {w : Nat} (hw : 0 < w)
    (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (x y c k target : BitVec w)
    (hx : paperMapR r x c k = target)
    (hy : paperMapR r y c k = target)
    (hseed : ∀ j : Nat, j < r → x.getLsbD j = y.getLsbD j) :
    x = y
```

```text
info: LeanPapers/ThreeBitGeneralR.lean:182:0: 'ThreeBitCyclic.paperMapR_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.paperMapR_fiber_card_le`

`LeanPapers/ThreeBitGeneralR.lean`, line 161

```lean
theorem paperMapR_fiber_card_le {w : Nat}
    (hw : 0 < w) (r : Nat) (hr2 : 2 ≤ r) (hrw : r < w)
    (c k target : BitVec w) :
    Fintype.card {x : BitVec w // paperMapR r x c k = target} ≤ 2 ^ r
```

```text
info: LeanPapers/ThreeBitGeneralR.lean:183:0: 'ThreeBitCyclic.paperMapR_fiber_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.recoverR_exact`

`LeanPapers/ThreeBitGeneralRecovery.lean`, line 215

```lean
theorem recoverR_exact {w : Nat}
    (hw : 0 < w) (r : Nat) (hr : 2 ≤ r) (hrw : r < w)
    (c k target x : BitVec w) :
    x ∈ recoverR hw r hr c k target ↔ paperMapR r x c k = target
```

```text
info: LeanPapers/ThreeBitGeneralRecovery.lean:255:0: 'ThreeBitCyclic.recoverR_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ThreeBitCyclic.general_r_w_local_updates`

`LeanPapers/ThreeBitGeneralRecovery.lean`, line 246

```lean
theorem general_r_w_local_updates (r w : Nat) :
    generalLocalUpdates r w = 2 ^ r * w
```

```text
info: LeanPapers/ThreeBitGeneralRecovery.lean:256:0: 'ThreeBitCyclic.general_r_w_local_updates' depends on axioms: [propext, Classical.choice, Quot.sound]
```
