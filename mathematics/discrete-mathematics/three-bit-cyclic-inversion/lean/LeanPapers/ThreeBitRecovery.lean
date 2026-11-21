import LeanPapers.ThreeBitCycle

namespace ThreeBitCyclic

/-- The section-2 recurrence, with exactly one local transition per call. -/
def runSeed {w : Nat} (hw : 0 < w) (c target : Word w)
    (seed : Bool × Bool × Bool) : Nat → State
  | 0 => ⟨seed.1, seed.2.1, seed.2.2, false⟩
  | i + 1 => step (bit hw c i) (bit hw target i)
      (runSeed hw c target seed i)

def candidate {w : Nat} (hw : 0 < w) (c target : Word w)
    (seed : Bool × Bool × Bool) : Word w :=
  fun j => (runSeed hw c target seed j.val).a

/-- The three cyclic closure checks. The final carry is intentionally free. -/
def closes {w : Nat} (hw : 0 < w) (c target : Word w)
    (seed : Bool × Bool × Bool) : Prop :=
  let z := runSeed hw c target seed w
  z.a = seed.1 ∧ z.b = seed.2.1 ∧ z.d = seed.2.2

theorem run_a_succ {w : Nat} (hw : 0 < w) (c target : Word w)
    (s : Bool × Bool × Bool) (i : Nat) :
    (runSeed hw c target s (i+1)).a = (runSeed hw c target s i).b := by
  rfl

theorem run_a_succ_succ {w : Nat} (hw : 0 < w) (c target : Word w)
    (s : Bool × Bool × Bool) (i : Nat) :
    (runSeed hw c target s (i+2)).a = (runSeed hw c target s i).d := by
  rfl

theorem run_a_succ_succ_succ {w : Nat} (hw : 0 < w) (c target : Word w)
    (s : Bool × Bool × Bool) (i : Nat) :
    (runSeed hw c target s (i+3)).a =
       (step (bit hw c i) (bit hw target i) (runSeed hw c target s i)).d := by
  rfl

theorem candidate_bit_closed {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) (s : Bool × Bool × Bool)
    (hc : closes (by omega : 0 < w) c target s)
    (i : Nat) (hi : i ≤ w+2) :
    bit (by omega : 0 < w) (candidate (by omega : 0 < w) c target s) i =
      (runSeed (by omega : 0 < w) c target s i).a := by
  have hp : 0 < w := by omega
  rcases (show i < w ∨ i = w ∨ i = w+1 ∨ i = w+2 by omega) with
      hlt | heq | heq | heq
  · simp [bit, candidate, Nat.mod_eq_of_lt hlt]
  · subst i
    change (runSeed hp c target s (w % w)).a =
      (runSeed hp c target s w).a
    rw [Nat.mod_self]
    exact hc.1.symm
  · subst i
    have hm : (w+1)%w = 1 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : 1 < w)]
    change (runSeed hp c target s ((w+1)%w)).a =
      (runSeed hp c target s (w+1)).a
    rw [hm, run_a_succ]
    exact hc.2.1.symm
  · subst i
    have hm : (w+2)%w = 2 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : 2 < w)]
    change (runSeed hp c target s ((w+2)%w)).a =
      (runSeed hp c target s (w+2)).a
    rw [hm, run_a_succ_succ]
    exact hc.2.2.symm

theorem step_forced_parity (m t : Bool) (s : State) :
    xor3 (s.b.xor (step m t s).d) (s.a && m) s.u = t := by
  rcases s with ⟨a,b,d,u⟩
  cases a <;> cases b <;> cases d <;> cases u <;>
    cases m <;> cases t <;> rfl

theorem candidate_outAt {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) (s : Bool × Bool × Bool)
    (hc : closes (by omega : 0 < w) c target s)
    (i : Nat) (hi : i < w)
    (hs : stateAt (by omega : 0 < w)
        (candidate (by omega : 0 < w) c target s) c i =
      runSeed (by omega : 0 < w) c target s i) :
    outAt (by omega : 0 < w)
        (candidate (by omega : 0 < w) c target s) c i =
      bit (by omega : 0 < w) target i := by
  have hp : 0 < w := by omega
  let z := candidate hp c target s
  let r := runSeed hp c target s
  have ha : bit hp z i = (r i).a := by
    have h := congrArg (fun st : State => st.a) hs
    simpa only [stateAt] using h
  have hb : bit hp z (i+1) = (r i).b := by
    have h := congrArg (fun st : State => st.b) hs
    simpa only [stateAt] using h
  have hu : carry hp z c i = (r i).u := by
    have h := congrArg (fun st : State => st.u) hs
    simpa only [stateAt] using h
  have hnext : bit hp z (i+3) =
      (step (bit hp c i) (bit hp target i) (r i)).d := by
    rw [candidate_bit_closed hw c target s hc (i+3) (by omega)]
    exact run_a_succ_succ_succ hp c target s i
  calc
    outAt hp z c i =
      xor3 ((r i).b.xor
         (step (bit hp c i) (bit hp target i) (r i)).d)
          ((r i).a && bit hp c i) (r i).u := by
          simp only [outAt, hb, hnext, ha, hu]
    _ = bit hp target i := step_forced_parity _ _ _

/-- A closed seed reconstructs a legal fiber member, including all carries. -/
theorem candidate_sound {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) (s : Bool × Bool × Bool)
    (hc : closes (by omega : 0 < w) c target s) :
    output (by omega : 0 < w)
      (candidate (by omega : 0 < w) c target s) c = target := by
  have hp : 0 < w := by omega
  let z := candidate hp c target s
  have hstate : ∀ i : Nat, i ≤ w →
      stateAt hp z c i = runSeed hp c target s i := by
    intro i
    induction i with
    | zero =>
        intro _
        simp [z, stateAt, candidate, bit, runSeed, step, carry,
          Nat.mod_eq_of_lt (by omega : 0 < w),
          Nat.mod_eq_of_lt (by omega : 1 < w),
          Nat.mod_eq_of_lt (by omega : 2 < w)]
    | succ i ih =>
        intro hi
        have hlt : i < w := by omega
        have hstep := state_succ hp z c i
        have ho := candidate_outAt hw c target s hc i hlt (ih (by omega))
        calc
          stateAt hp z c (i+1) =
            step (bit hp c i) (outAt hp z c i) (stateAt hp z c i) := hstep
          _ = step (bit hp c i) (bit hp target i) (runSeed hp c target s i) := by
              rw [ho, ih (by omega)]
          _ = runSeed hp c target s (i+1) := rfl
  funext j
  have hh := candidate_outAt hw c target s hc j.val j.isLt
    (hstate j.val (Nat.le_of_lt j.isLt))
  simpa [output, bit, Nat.mod_eq_of_lt j.isLt] using hh

def seedOf {w : Nat} (hw : 0 < w) (x : Word w) :
    Bool × Bool × Bool := (bit hw x 0,bit hw x 1,bit hw x 2)

theorem runSeed_complete {w : Nat} (hw : 4 ≤ w)
    (x c target : Word w)
    (hx : output (by omega : 0 < w) x c = target) :
    ∀ i : Nat, i ≤ w →
      runSeed (by omega : 0 < w) c target
        (seedOf (by omega : 0 < w) x) i =
      stateAt (by omega : 0 < w) x c i := by
  have hp : 0 < w := by omega
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      have hlt : i < w := by omega
      have ho : outAt hp x c i = bit hp target i := by
        have heq := congrArg (fun z : Word w => z ⟨i,hlt⟩) hx
        simpa [output,bit, Nat.mod_eq_of_lt hlt] using heq
      calc
        runSeed hp c target (seedOf hp x) (i+1) =
          step (bit hp c i) (bit hp target i)
            (runSeed hp c target (seedOf hp x) i) := rfl
        _ = step (bit hp c i) (outAt hp x c i)
            (stateAt hp x c i) := by rw [ho, ih (by omega)]
        _ = stateAt hp x c (i+1) := (state_succ hp x c i).symm

theorem candidate_complete {w : Nat} (hw : 4 ≤ w)
    (x c target : Word w)
    (hx : output (by omega : 0 < w) x c = target) :
    closes (by omega : 0 < w) c target
      (seedOf (by omega : 0 < w) x) ∧
    candidate (by omega : 0 < w) c target
      (seedOf (by omega : 0 < w) x) = x := by
  have hp : 0 < w := by omega
  have hrun := runSeed_complete hw x c target hx
  constructor
  · have h := hrun w (by omega)
    change (runSeed hp c target (seedOf hp x) w).a = bit hp x 0 ∧
      (runSeed hp c target (seedOf hp x) w).b = bit hp x 1 ∧
      (runSeed hp c target (seedOf hp x) w).d = bit hp x 2
    have h0 : bit hp x w = bit hp x 0 := by
      simp [bit, Nat.mod_self]
    have h1 : bit hp x (w+1) = bit hp x 1 := by
      simp [bit, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < w)]
    have h2 : bit hp x (w+2) = bit hp x 2 := by
      simp [bit, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < w)]
    have hh := congrArg (fun z : State => (z.a,z.b,z.d)) h
    simpa [stateAt, h0, h1, h2, Prod.mk.injEq] using hh
  · funext j
    have h := congrArg State.a (hrun j.val (Nat.le_of_lt j.isLt))
    simpa [candidate, stateAt, bit, Nat.mod_eq_of_lt j.isLt] using h

/-- Enumerate all eight seeds, retain exactly the closed ones. -/
def recover {w : Nat} (hw : 0 < w) (c target : Word w) : Finset (Word w) := by
  letI : DecidablePred (closes hw c target) := by
    intro s
    unfold closes
    infer_instance
  exact ((Finset.univ : Finset (Bool × Bool × Bool)).filter
    (closes hw c target)).image (candidate hw c target)

/-- Theorem 1, exact inverse: enumerating closed seed paths returns the fiber. -/
theorem recover_exact {w : Nat} (hw : 4 ≤ w)
    (c target : Word w) (x : Word w) :
    x ∈ recover (by omega : 0 < w) c target ↔
      output (by omega : 0 < w) x c = target := by
  have hp : 0 < w := by omega
  classical
  simp only [recover, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨s, hc, rfl⟩
    exact candidate_sound hw c target s hc
  · intro hx
    rcases candidate_complete hw x c target hx with ⟨hc,hx'⟩
    exact ⟨seedOf hp x, hc, hx'⟩

#print axioms candidate_bit_closed
#print axioms candidate_sound
#print axioms candidate_complete
#print axioms recover_exact

#print axioms run_a_succ
#print axioms run_a_succ_succ
#print axioms run_a_succ_succ_succ
#print axioms step_forced_parity
#print axioms candidate_outAt
#print axioms runSeed_complete

end ThreeBitCyclic
