import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 4, ordered Boolean windows and carry table -/

namespace Unifier

inductive Step where
  | orStep : Bool → Step
  | andStep : Bool → Step
  deriving DecidableEq, Repr

def response : List Step → Bool → Bool
  | [], r => r
  | Step.orStep v :: S, r => v || response S r
  | Step.andStep v :: S, r => v && response S r

def windowTrit (S : List Step) : ℕ :=
  (response S true).toNat + (response S false).toNat

def tritCompose (a b : ℕ) : ℕ := if a = 1 then b else a

theorem response_mono (S : List Step) :
    response S false = true → response S true = true := by
  induction S with
  | nil => simp [response]
  | cons step S ih =>
    cases step with
    | orStep v => cases v <;> simp_all [response]
    | andStep v => cases v <;> simp_all [response]

theorem response_fork (S : List Step) (r : Bool) :
    response S r = (response S false || (response S true && r)) := by
  have hm := response_mono S
  cases r <;>
    cases h0 : response S false <;>
    cases h1 : response S true <;>
    simp_all

theorem windowTrit_classes (S : List Step) (r : Bool) :
    (windowTrit S = 0 → response S r = false) ∧
    (windowTrit S = 1 → response S r = r) ∧
    (windowTrit S = 2 → response S r = true) := by
  have hm := response_mono S
  have hf := response_fork S r
  cases h0 : response S false <;> cases h1 : response S true
  · have hr : response S r = false := by simpa [h0, h1] using hf
    simp [windowTrit, h0, h1, hr]
  · have hr : response S r = r := by simpa [h0, h1] using hf
    simp [windowTrit, h0, h1, hr]
  · have hx := hm h0
    rw [h1] at hx
    contradiction
  · have hr : response S r = true := by simpa [h0, h1] using hf
    simp [windowTrit, h0, h1, hr]

theorem response_append (S T : List Step) (r : Bool) :
    response (S ++ T) r = response S (response T r) := by
  induction S with
  | nil => rfl
  | cons step S ih =>
    cases step <;> simp [response, ih]

theorem windowTrit_compose (S T : List Step) :
    windowTrit (S ++ T) = tritCompose (windowTrit S) (windowTrit T) := by
  have hm := response_mono S
  unfold windowTrit tritCompose
  simp only [response_append]
  rw [response_fork S (response T true), response_fork S (response T false)]
  cases h0 : response S false <;>
    cases h1 : response S true <;>
    cases hb0 : response T false <;>
    cases hb1 : response T true <;>
    simp_all

theorem tritCompose_assoc (a b c : ℕ) :
    tritCompose (tritCompose a b) c = tritCompose a (tritCompose b c) := by
  by_cases ha : a = 1
  · subst a
    simp [tritCompose]
  · simp [tritCompose, ha]

theorem tritCompose_left_id (a : ℕ) : tritCompose 1 a = a := by
  simp [tritCompose]

theorem tritCompose_right_id (a : ℕ) :
    (a = 0 ∨ a = 1 ∨ a = 2) → tritCompose a 1 = a := by
  intro ha
  rcases ha with h | h | h <;> subst a <;> decide

def allOr : List Step → Bool
  | [] => false
  | Step.orStep v :: S => v || allOr S
  | Step.andStep _ :: S => allOr S

def allAnd : List Step → Bool
  | [] => true
  | Step.orStep _ :: S => allAnd S
  | Step.andStep v :: S => v && allAnd S

theorem response_normal_and (S : List Step) (r : Bool) :
    response S r = (response S false || (allAnd S && r)) := by
  induction S with
  | nil => cases r <;> decide
  | cons step S ih =>
    cases step with
    | orStep v =>
      cases v <;> simp_all [response, allAnd]
    | andStep v =>
      cases v <;> simp_all [response, allAnd]

theorem response_normal_or (S : List Step) (r : Bool) :
    response S r = (response S true && (allOr S || r)) := by
  induction S with
  | nil => cases r <;> decide
  | cons step S ih =>
    cases step with
    | orStep v =>
      cases v <;> simp_all [response, allOr]
    | andStep v =>
      cases v <;> simp_all [response, allOr]

def oneStage (g p : Bool) : List Step :=
  [Step.orStep g, Step.andStep p]

def oneStageTrit (gp : Bool × Bool) : ℕ :=
  windowTrit (oneStage gp.1 gp.2)

theorem oneStage_three (g p : Bool) :
    oneStageTrit (g, p) = 0 ∨
    oneStageTrit (g, p) = 1 ∨
    oneStageTrit (g, p) = 2 := by
  cases g <;> cases p <;> decide

theorem oneStage_surjective :
    ∀ t : Fin 3, ∃ gp : Bool × Bool, oneStageTrit gp = t.val := by
  intro t
  have ht : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by omega
  rcases ht with h | h | h
  · exact ⟨(false, false), by simp [oneStageTrit, windowTrit, oneStage, response, h]⟩
  · exact ⟨(false, true), by simp [oneStageTrit, windowTrit, oneStage, response, h]⟩
  · exact ⟨(true, false), by simp [oneStageTrit, windowTrit, oneStage, response, h]⟩

theorem oneStage_exact (a b : Bool × Bool) :
    (response (oneStage a.1 a.2) false =
       response (oneStage b.1 b.2) false ∧
     response (oneStage a.1 a.2) true =
       response (oneStage b.1 b.2) true) ↔
       oneStageTrit a = oneStageTrit b := by
  rcases a with ⟨a1, a2⟩
  rcases b with ⟨b1, b2⟩
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> decide

theorem oneStage_no_bool_boundary (b : Bool × Bool → Bool)
    (hb : ∀ u v, b u = b v → oneStageTrit u = oneStageTrit v) : False := by
  have h01 : b (false, false) ≠ b (false, true) := by
    intro h
    have hc := hb (false, false) (false, true) h
    simp [oneStageTrit, windowTrit, oneStage, response] at hc
  have h02 : b (false, false) ≠ b (true, false) := by
    intro h
    have hc := hb (false, false) (true, false) h
    simp [oneStageTrit, windowTrit, oneStage, response] at hc
  have h12 : b (false, true) ≠ b (true, false) := by
    intro h
    have hc := hb (false, true) (true, false) h
    simp [oneStageTrit, windowTrit, oneStage, response] at hc
  cases h0 : b (false, false) <;>
    cases h1 : b (false, true) <;>
    cases h2 : b (true, false) <;>
    simp_all

def bitWindow (a b : Bool) : List Step :=
  oneStage (a && b) (a.xor b)

theorem bitWindow_response (a b r : Bool) :
    response (bitWindow a b) r =
      ((a && b) || ((a.xor b) && r)) := by
  cases a <;> cases b <;> cases r <;> decide

theorem binary_full_adder (a b r : Bool) :
    a.toNat + b.toNat + r.toNat =
      ((a.xor b).xor r).toNat +
        2 * (response (bitWindow a b) r).toNat := by
  cases a <;> cases b <;> cases r <;> decide

def blockWindow : List (Bool × Bool) → List Step
  | [] => []
  | (a, b) :: ps => bitWindow a b ++ blockWindow ps

def blockCarry : List (Bool × Bool) → Bool → Bool
  | [], r => r
  | (a, b) :: ps, r => response (bitWindow a b) (blockCarry ps r)

theorem binary_block_carry (ps : List (Bool × Bool)) (r : Bool) :
    blockCarry ps r = response (blockWindow ps) r := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      simp [blockCarry, blockWindow, response_append, ih]

/-! ### NOTE-2 additions -/

theorem oneStageTrit_lt (gp : Bool × Bool) : oneStageTrit gp < 3 := by
  obtain ⟨g, p⟩ := gp
  cases g <;> cases p <;> decide

/-- T11: the exact contraction of the one-stage window `[or g, and p]` on the four states
`(g, p)`: states are equivalent when their responses at `R = false` and at `R = true` agree. -/
def oneStageSetoid : Setoid (Bool × Bool) where
  r a b :=
    response (oneStage a.1 a.2) false = response (oneStage b.1 b.2) false ∧
    response (oneStage a.1 a.2) true = response (oneStage b.1 b.2) true
  iseqv :=
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
     fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

def oneStageRep (t : Fin 3) : Bool × Bool :=
  if t.val = 0 then (false, false) else if t.val = 1 then (false, true) else (true, false)

/-- The classes of the exact contraction are the three trits. -/
def oneStageQuotEquiv : Quotient oneStageSetoid ≃ Fin 3 where
  toFun := Quotient.lift (fun gp => (⟨oneStageTrit gp, oneStageTrit_lt gp⟩ : Fin 3))
    (fun a b h => Fin.ext ((oneStage_exact a b).1 h))
  invFun t := Quotient.mk oneStageSetoid (oneStageRep t)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h gp =>
      apply Quotient.sound
      obtain ⟨g, p⟩ := gp
      cases g <;> cases p <;> exact ⟨rfl, rfl⟩
  right_inv t := by
    match t with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

noncomputable instance : Fintype (Quotient oneStageSetoid) :=
  Fintype.ofEquiv (Fin 3) oneStageQuotEquiv.symm

/-- T11, the count itself (NOTE-2, item 1): the exact contraction has exactly three classes. -/
theorem oneStage_class_count : Fintype.card (Quotient oneStageSetoid) = 3 := by
  rw [Fintype.card_congr oneStageQuotEquiv, Fintype.card_fin]

/-- C5, the trit of a position (NOTE-2, item 2). -/
theorem bitWindow_trit (a b : Bool) :
    windowTrit (bitWindow a b) = a.toNat + b.toNat := by
  cases a <;> cases b <;> rfl

/-- The value of a bit word, least significant bit first: `value [x₀, x₁, ...] = x₀ + 2 x₁ + ...`. -/
def bitsValue : List Bool → ℕ
  | [] => 0
  | x :: xs => x.toNat + 2 * bitsValue xs

/-- `bitsValue xs` is `∑ i < length xs, xs[i] * 2^i` (`getD` reads `xs[i]`). -/
theorem bitsValue_eq_sum (xs : List Bool) :
    bitsValue xs = ∑ i ∈ Finset.range xs.length, (xs.getD i false).toNat * 2 ^ i := by
  induction xs with
  | nil => simp [bitsValue]
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', bitsValue, ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The sum bits of ripple addition, least significant position first. The sum bit of a
position is `a xor b xor c`, where `c`, the carry into it, is the response of the windows of
the positions below it to the carry in (`rippleCarry_eq_blockCarry`). -/
def rippleSum : List (Bool × Bool) → Bool → List Bool
  | [], _ => []
  | (a, b) :: ps, r => ((a.xor b).xor r) :: rippleSum ps (response (bitWindow a b) r)

/-- The carry out of a word, the list read least significant position first. -/
def rippleCarry : List (Bool × Bool) → Bool → Bool
  | [], r => r
  | (a, b) :: ps, r => rippleCarry ps (response (bitWindow a b) r)

theorem blockCarry_append_single (xs : List (Bool × Bool)) (a b r : Bool) :
    blockCarry (xs ++ [(a, b)]) r = blockCarry xs (response (bitWindow a b) r) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨c, d⟩ := p
    simp [blockCarry, ih]

/-- `blockCarry` reads its list most significant position first (the head is the top stage);
`rippleCarry` reads it least significant first. They agree on the reversed list, and both are
the response of the concatenated window (`binary_block_carry`). -/
theorem rippleCarry_eq_blockCarry (ps : List (Bool × Bool)) (r : Bool) :
    rippleCarry ps r = blockCarry ps.reverse r ∧
    rippleCarry ps r = response (blockWindow ps.reverse) r := by
  have h : ∀ r, rippleCarry ps r = blockCarry ps.reverse r := by
    induction ps with
    | nil => intro r; rfl
    | cons p ps ih =>
      intro r
      obtain ⟨a, b⟩ := p
      rw [List.reverse_cons, blockCarry_append_single, ← ih]
      rfl
  exact ⟨h r, (h r).trans (binary_block_carry _ r)⟩

/-- C5, whole words (NOTE-2, item 3): `binary_full_adder` iterated. For a list `ps` of bit
pairs, least significant first,
`value(first components) + value(second components) + r
   = value(sum bits) + 2^(length ps) * carry out`. -/
theorem binary_word_adder (ps : List (Bool × Bool)) (r : Bool) :
    bitsValue (ps.map Prod.fst) + bitsValue (ps.map Prod.snd) + r.toNat =
      bitsValue (rippleSum ps r) + 2 ^ ps.length * (rippleCarry ps r).toNat := by
  induction ps generalizing r with
  | nil => simp [bitsValue, rippleSum, rippleCarry]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have hfa := binary_full_adder a b r
    have hih := ih (response (bitWindow a b) r)
    simp only [List.map_cons, bitsValue, rippleSum, rippleCarry, List.length_cons, pow_succ]
    nlinarith [hfa, hih]

/-! ### The sum bits are the binary digits of the sum -/

theorem bitsValue_lt (xs : List Bool) : bitsValue xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [bitsValue]
  | cons x xs ih =>
    have hx : x.toNat ≤ 1 := by cases x <;> decide
    simp only [bitsValue, List.length_cons, pow_succ]
    omega

theorem rippleSum_length (ps : List (Bool × Bool)) (r : Bool) :
    (rippleSum ps r).length = ps.length := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp [rippleSum, ih]

/-- C5: sum bit `i` is `a_i xor b_i xor c_i`, where `c_i` is the carry out of the positions
below `i` (`ps.take i`), which by `rippleCarry_eq_blockCarry` is the response of their
concatenated window, top position first, to the carry in. -/
theorem rippleSum_getD (ps : List (Bool × Bool)) (r : Bool) (i : ℕ) (hi : i < ps.length) :
    (rippleSum ps r).getD i false =
      (((ps.getD i (false, false)).1.xor (ps.getD i (false, false)).2).xor
        (rippleCarry (ps.take i) r)) := by
  induction ps generalizing r i with
  | nil => simp at hi
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    cases i with
    | zero => simp [rippleSum, rippleCarry]
    | succ i =>
      have hi' : i < ps.length := by simpa using hi
      have h := ih (response (bitWindow a b) r) i hi'
      simpa [rippleSum, rippleCarry] using h

/-- C5: the sum bits are the low `length ps` binary digits of `a + b + c₀`, and the carry out
is the next digit. -/
theorem binary_word_adder_digits (ps : List (Bool × Bool)) (r : Bool) :
    (bitsValue (ps.map Prod.fst) + bitsValue (ps.map Prod.snd) + r.toNat) % 2 ^ ps.length =
        bitsValue (rippleSum ps r) ∧
    (bitsValue (ps.map Prod.fst) + bitsValue (ps.map Prod.snd) + r.toNat) / 2 ^ ps.length =
        (rippleCarry ps r).toNat := by
  have h := binary_word_adder ps r
  have hlt : bitsValue (rippleSum ps r) < 2 ^ ps.length := by
    have h' := bitsValue_lt (rippleSum ps r)
    rwa [rippleSum_length] at h'
  have hpos : 0 < 2 ^ ps.length := Nat.pow_pos (by decide)
  rw [h]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

#print axioms bitsValue_lt
#print axioms rippleSum_length
#print axioms rippleSum_getD
#print axioms binary_word_adder_digits
#print axioms oneStage_class_count
#print axioms bitWindow_trit
#print axioms bitsValue_eq_sum
#print axioms rippleCarry_eq_blockCarry
#print axioms binary_word_adder

#print axioms bitWindow_response
#print axioms binary_full_adder
#print axioms binary_block_carry
#print axioms oneStage_no_bool_boundary
#print axioms response_mono
#print axioms response_fork
#print axioms windowTrit_classes
#print axioms response_append
#print axioms windowTrit_compose
#print axioms tritCompose_assoc
#print axioms tritCompose_left_id
#print axioms tritCompose_right_id
#print axioms response_normal_and
#print axioms response_normal_or
#print axioms oneStage_three
#print axioms oneStage_surjective
#print axioms oneStage_exact

end Unifier
