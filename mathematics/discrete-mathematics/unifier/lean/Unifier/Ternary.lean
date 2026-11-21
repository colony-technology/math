import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 3, native product and retained trit -/

namespace Unifier

def nativeTensor (a b : ℕ) : ℕ := 2 * a * b

theorem nativeTensor_one : nativeTensor 1 1 = 2 := by
  decide

theorem nativeTensor_bit_xor (a b : Bool) :
    a.toNat + b.toNat = (a.xor b).toNat + nativeTensor a.toNat b.toNat := by
  cases a <;> cases b <;> decide

theorem nativeTensor_square (a b : ℕ) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + nativeTensor a b := by
  unfold nativeTensor
  calc
    (a + b) ^ 2 = a * a + a * b + b * a + b * b := by
      simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
      omega
    _ = a ^ 2 + b ^ 2 + 2 * a * b := by
      rw [Nat.mul_comm b a]
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
      omega

theorem nativeTensor_half (a b : ℕ) :
    nativeTensor a b / 2 = a * b := by
  have h : (2 * (a * b)) / 2 = a * b := by omega
  simpa [nativeTensor, Nat.mul_assoc] using h

abbrev LegalRails := {p : Bool × Bool // p ≠ (false, true)}
abbrev TritFork := LegalRails

def railsToTrit (p : LegalRails) : Fin 3 :=
  ⟨p.val.1.toNat + p.val.2.toNat, by
    rcases p with ⟨⟨s, w⟩, h⟩
    cases s <;> cases w <;> simp_all⟩

def tritToRails (t : Fin 3) : LegalRails :=
  ⟨(decide (1 ≤ t.val), decide (2 ≤ t.val)), by
    intro h
    have hs : ¬ (1 ≤ t.val) := by
      have he := congrArg Prod.fst h
      simpa using he
    have hw : 2 ≤ t.val := by
      have he := congrArg Prod.snd h
      simpa using he
    omega⟩

theorem tritToRails_left (t : Fin 3) :
    railsToTrit (tritToRails t) = t := by
  apply Fin.ext
  have ht : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by omega
  rcases ht with h | h | h <;>
    simp [railsToTrit, tritToRails, h]

theorem tritToRails_right (p : LegalRails) :
    tritToRails (railsToTrit p) = p := by
  rcases p with ⟨⟨s, w⟩, h⟩
  cases s <;> cases w
  · rfl
  · exact False.elim (h rfl)
  · rfl
  · rfl

def tritForkEquiv : LegalRails ≃ Fin 3 where
  toFun := railsToTrit
  invFun := tritToRails
  left_inv := tritToRails_right
  right_inv := tritToRails_left

theorem trit_no_forbidden_corner (t : Fin 3) :
    (tritToRails t).val ≠ (false, true) :=
  (tritToRails t).property

#print axioms nativeTensor_one
#print axioms nativeTensor_bit_xor
#print axioms nativeTensor_square
#print axioms nativeTensor_half
#print axioms tritToRails_left
#print axioms tritToRails_right
#print axioms trit_no_forbidden_corner

end Unifier
