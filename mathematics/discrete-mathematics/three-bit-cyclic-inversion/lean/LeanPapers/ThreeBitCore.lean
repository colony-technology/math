import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
A three-bit boundary for cyclic Boolean-modular inversion.
The bits of q+b are computed by the full-adder recurrence from the
published verifier (inverse.py), with discarded final carry.
-/

namespace ThreeBitCyclic

abbrev Word (w : Nat) := Fin w → Bool

def bit {w : Nat} (hw : 0 < w) (x : Word w) (i : Nat) : Bool :=
  x ⟨i % w, Nat.mod_lt i hw⟩

def xor3 (a b c : Bool) : Bool := (a.xor b).xor c

def maj (a b c : Bool) : Bool :=
  ((a && b) || (a && c)) || (b && c)

def carry {w : Nat} (hw : 0 < w) (x c : Word w) : Nat → Bool
  | 0 => false
  | i + 1 =>
    maj ((bit hw x (i + 1)).xor (bit hw x (i + 3)))
      (bit hw x i && bit hw c i) (carry hw x c i)

def outAt {w : Nat} (hw : 0 < w) (x c : Word w) (i : Nat) : Bool :=
  xor3 ((bit hw x (i + 1)).xor (bit hw x (i + 3)))
    (bit hw x i && bit hw c i) (carry hw x c i)

def output {w : Nat} (hw : 0 < w) (x c : Word w) : Word w :=
  fun i => outAt hw x c i.val

structure State where
  a : Bool
  b : Bool
  d : Bool
  u : Bool
  deriving DecidableEq

def stateAt {w : Nat} (hw : 0 < w) (x c : Word w) (i : Nat) : State :=
  ⟨bit hw x i, bit hw x (i + 1), bit hw x (i + 2), carry hw x c i⟩

def step (mask target : Bool) (s : State) : State :=
  let b₀ := s.a && mask
  let q := xor3 target b₀ s.u
  ⟨s.b, s.d, s.b.xor q, maj q b₀ s.u⟩

private theorem step_correct (a b d e m u : Bool) :
    step m (xor3 (b.xor e) (a && m) u) ⟨a, b, d, u⟩ =
      ⟨b, d, e, maj (b.xor e) (a && m) u⟩ := by
  cases a <;> cases b <;> cases d <;> cases e <;>
    cases m <;> cases u <;> rfl

theorem state_succ {w : Nat} (hw : 0 < w) (x c : Word w) (i : Nat) :
    stateAt hw x c (i + 1) =
      step (bit hw c i) (outAt hw x c i) (stateAt hw x c i) := by
  apply Eq.symm
  simpa [stateAt, outAt, carry, Nat.add_assoc] using
    (step_correct (bit hw x i) (bit hw x (i + 1))
      (bit hw x (i + 2)) (bit hw x (i + 3))
      (bit hw c i) (carry hw x c i))

theorem state_eq_of_three_bits {w : Nat} (hw : 0 < w)
    (x y c : Word w)
    (houtput : output hw x c = output hw y c)
    (h0 : bit hw x 0 = bit hw y 0)
    (h1 : bit hw x 1 = bit hw y 1)
    (h2 : bit hw x 2 = bit hw y 2) :
    ∀ i : Nat, i ≤ w → stateAt hw x c i = stateAt hw y c i := by
  intro i
  induction i with
  | zero =>
      intro _
      simp [stateAt, carry, h0, h1, h2]
  | succ i ih =>
      intro hi
      have hi' : i < w := Nat.lt_of_succ_le hi
      have htarget : outAt hw x c i = outAt hw y c i := by
        have h := congrArg (fun z : Word w => z ⟨i, hi'⟩) houtput
        simpa [output] using h
      calc
        stateAt hw x c (i + 1) =
          step (bit hw c i) (outAt hw x c i) (stateAt hw x c i) :=
            state_succ hw x c i
        _ = step (bit hw c i) (outAt hw y c i) (stateAt hw y c i) := by
          rw [htarget, ih (Nat.le_of_lt hi')]
        _ = stateAt hw y c (i + 1) := (state_succ hw y c i).symm

theorem three_bit_boundary {w : Nat} (hw : 4 ≤ w)
    (x y c target : Word w)
    (hx : output (by omega : 0 < w) x c = target)
    (hy : output (by omega : 0 < w) y c = target)
    (h0 : bit (by omega : 0 < w) x 0 = bit (by omega : 0 < w) y 0)
    (h1 : bit (by omega : 0 < w) x 1 = bit (by omega : 0 < w) y 1)
    (h2 : bit (by omega : 0 < w) x 2 = bit (by omega : 0 < w) y 2) :
    x = y := by
  have hp : 0 < w := by omega
  have hstates := state_eq_of_three_bits hp x y c (hx.trans hy.symm) h0 h1 h2
  funext j
  have h := congrArg State.a (hstates j.val (Nat.le_of_lt j.isLt))
  simpa [stateAt, bit, Nat.mod_eq_of_lt j.isLt] using h

theorem fiber_card_le_eight {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) :
    Fintype.card {x : Word w // output (by omega : 0 < w) x c = target} ≤ 8 := by
  classical
  have hp : 0 < w := by omega
  let encode : {x : Word w // output hp x c = target} → Bool × Bool × Bool :=
    fun z => (bit hp z.val 0, bit hp z.val 1, bit hp z.val 2)
  have hinj : Function.Injective encode := by
    intro x y heq
    apply Subtype.ext
    apply three_bit_boundary hw x.val y.val c target x.property y.property
    · exact congrArg (fun t : Bool × Bool × Bool => t.1) heq
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.1) heq
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.2) heq
  have hcard := Fintype.card_le_of_injective encode hinj
  have h8 : Fintype.card (Bool × Bool × Bool) = 8 := by decide
  simpa [h8] using hcard

/-! A second ripple adder handles the fixed additive constant k. -/

def fixedCarry {w : Nat} (hw : 0 < w) (z k : Word w) : Nat → Bool
  | 0 => false
  | i + 1 => maj (bit hw z i) (bit hw k i) (fixedCarry hw z k i)

def fixedAdd {w : Nat} (hw : 0 < w) (z k : Word w) : Word w :=
  fun j => xor3 (bit hw z j.val) (bit hw k j.val) (fixedCarry hw z k j.val)

private theorem xor3_left_cancel (a d b u : Bool)
    (h : xor3 a b u = xor3 d b u) : a = d := by
  cases a <;> cases d <;> cases b <;> cases u <;>
    simp [xor3] at h ⊢

theorem fixedAdd_injective {w : Nat} (hw : 0 < w)
    (z y k : Word w) (heq : fixedAdd hw z k = fixedAdd hw y k) :
    z = y := by
  have hc : ∀ i : Nat, i ≤ w →
      fixedCarry hw z k i = fixedCarry hw y k i := by
    intro i
    induction i with
    | zero =>
        intro _
        rfl
    | succ i ih =>
        intro hi
        have hi' : i < w := Nat.lt_of_succ_le hi
        have hcarry := ih (Nat.le_of_lt hi')
        have hout : xor3 (bit hw z i) (bit hw k i) (fixedCarry hw z k i) =
            xor3 (bit hw y i) (bit hw k i) (fixedCarry hw y k i) := by
          have h := congrArg (fun f : Word w => f ⟨i, hi'⟩) heq
          simpa [fixedAdd] using h
        have hbit : bit hw z i = bit hw y i :=
          xor3_left_cancel _ _ _ _ (by simpa [hcarry] using hout)
        simpa [fixedCarry, hbit, hcarry]
  funext j
  have hcarry := hc j.val (Nat.le_of_lt j.isLt)
  have hout := congrArg (fun f : Word w => f j) heq
  have hbit : bit hw z j.val = bit hw y j.val :=
    xor3_left_cancel _ _ _ _ (by simpa [fixedAdd, hcarry] using hout)
  simpa [bit, Nat.mod_eq_of_lt j.isLt] using hbit

/-- The exact two-stage bit-level forward circuit, including arbitrary k. -/
def forward {w : Nat} (hw : 0 < w) (x c k : Word w) : Word w :=
  fixedAdd hw (output hw x c) k

theorem full_three_bit_boundary {w : Nat} (hw : 4 ≤ w)
    (x y c k target : Word w)
    (hx : forward (by omega : 0 < w) x c k = target)
    (hy : forward (by omega : 0 < w) y c k = target)
    (h0 : bit (by omega : 0 < w) x 0 = bit (by omega : 0 < w) y 0)
    (h1 : bit (by omega : 0 < w) x 1 = bit (by omega : 0 < w) y 1)
    (h2 : bit (by omega : 0 < w) x 2 = bit (by omega : 0 < w) y 2) :
    x = y := by
  have hp : 0 < w := by omega
  have hinner : output hp x c = output hp y c :=
    fixedAdd_injective hp _ _ k (hx.trans hy.symm)
  exact three_bit_boundary hw x y c (output hp x c)
    rfl hinner.symm h0 h1 h2

theorem full_fiber_card_le_eight {w : Nat} (hw : 4 ≤ w)
    (c k target : Word w) :
    Fintype.card {x : Word w //
      forward (by omega : 0 < w) x c k = target} ≤ 8 := by
  classical
  have hp : 0 < w := by omega
  let encode : {x : Word w // forward hp x c k = target} →
      Bool × Bool × Bool :=
    fun z => (bit hp z.val 0, bit hp z.val 1, bit hp z.val 2)
  have hinj : Function.Injective encode := by
    intro x y heq
    apply Subtype.ext
    apply full_three_bit_boundary hw x.val y.val c k target
      x.property y.property
    · exact congrArg (fun t : Bool × Bool × Bool => t.1) heq
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.1) heq
    · exact congrArg (fun t : Bool × Bool × Bool => t.2.2) heq
  have hcard := Fintype.card_le_of_injective encode hinj
  have h8 : Fintype.card (Bool × Bool × Bool) = 8 := by decide
  simpa [h8] using hcard

/-- The period-seven state transition in the extremal family. -/
def linearStep (s : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (s.2.1, s.2.2, s.1.xor s.2.1)

theorem linearStep_period_seven (s : Bool × Bool × Bool) :
    (linearStep^[7]) s = s := by
  rcases s with ⟨a, b, d⟩
  cases a <;> cases b <;> cases d <;> decide

def allOnes (w : Nat) : Word w := fun _ => true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem example_seven_exact :
    Fintype.card {x : Word 7 //
      output (by decide : 0 < 7) x (allOnes 7) = allOnes 7} = 8 := by
  decide

#print axioms step_correct
#print axioms state_succ
#print axioms state_eq_of_three_bits
#print axioms three_bit_boundary
#print axioms fiber_card_le_eight
#print axioms xor3_left_cancel
#print axioms fixedAdd_injective
#print axioms full_three_bit_boundary
#print axioms full_fiber_card_le_eight
#print axioms linearStep_period_seven
#print axioms example_seven_exact

end ThreeBitCyclic
