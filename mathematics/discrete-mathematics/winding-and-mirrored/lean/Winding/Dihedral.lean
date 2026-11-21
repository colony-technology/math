import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Winding and Mirrored, W8: twelve sectors

On `Z/12`, `r(x) = x + 1` and `s(x) = -x`, as permutations of `ZMod 12`. -/

namespace Winding

/-- `r(x) = x + 1` on `Z/12`. -/
def rot12 : Equiv.Perm (ZMod 12) := Equiv.addRight 1

/-- `s(x) = -x` on `Z/12`. -/
def refl12 : Equiv.Perm (ZMod 12) := Equiv.neg (ZMod 12)

theorem rot12_pow_apply (a : ℕ) (x : ZMod 12) : (rot12 ^ a) x = x + a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [rot12, Equiv.coe_addRight, Nat.cast_succ]
    ring

theorem refl12_apply (x : ZMod 12) : refl12 x = -x := rfl

/-- W8: `r` has order 12. -/
theorem rot12_order : orderOf rot12 = 12 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · ext x
    rw [rot12_pow_apply, Equiv.Perm.one_apply]
    have : ((12 : ℕ) : ZMod 12) = 0 := ZMod.natCast_self 12
    rw [this, add_zero]
  · intro m hm hm0 h
    have h0 := Equiv.congr_fun h 0
    rw [rot12_pow_apply, Equiv.Perm.one_apply, zero_add, ZMod.natCast_eq_zero_iff] at h0
    obtain ⟨c, hc⟩ := h0
    omega

/-- W8: `s` has order 2. -/
theorem refl12_order : orderOf refl12 = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · ext x
    rw [sq, Equiv.Perm.mul_apply, refl12_apply, refl12_apply, neg_neg, Equiv.Perm.one_apply]
  · intro m hm hm0 h
    have hm1 : m = 1 := by omega
    subst hm1
    have h1 := Equiv.congr_fun h 1
    rw [pow_one, refl12_apply, Equiv.Perm.one_apply] at h1
    exact absurd h1 (by decide)

/-- W8: `s r s = r⁻¹`. -/
theorem refl_rot_refl : refl12 * rot12 * refl12 = rot12⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  ext x
  simp only [Equiv.Perm.mul_apply, refl12_apply, rot12, Equiv.coe_addRight, Equiv.Perm.one_apply]
  ring

/-- The map `(a, b) ↦ r^a s^b` for `a < 12`, `b < 2`. -/
def dihedral12 (ab : Fin 12 × Fin 2) : Equiv.Perm (ZMod 12) := rot12 ^ (ab.1 : ℕ) * refl12 ^ (ab.2 : ℕ)

/-- W8: the 24 maps `r^a s^b` (`a < 12`, `b < 2`) are pairwise distinct. -/
theorem dihedral12_injective : Function.Injective dihedral12 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := Equiv.congr_fun h 0
  have h1 := Equiv.congr_fun h 1
  simp only [dihedral12, Equiv.Perm.mul_apply, rot12_pow_apply] at h0 h1
  have hz : ∀ c : Fin 2, (refl12 ^ (c : ℕ)) 0 = 0 := by
    intro c
    fin_cases c
    · rfl
    · simp [refl12_apply]
  rw [hz, hz, zero_add, zero_add] at h0
  have ha : (a : ℕ) = (a' : ℕ) := by
    have := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (a' : ℕ) 12).1 h0
    rwa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt a'.isLt] at this
  have ha' : a = a' := Fin.ext ha
  subst ha'
  rw [add_left_inj] at h1
  have hb : b = b' := by
    fin_cases b <;> fin_cases b' <;> simp [refl12_apply] at h1 ⊢ <;> exact absurd h1 (by decide)
  rw [hb]

/-- W8: there are exactly 24 of them. -/
theorem dihedral12_card : (Finset.univ.image dihedral12).card = 24 := by
  rw [Finset.card_image_of_injective _ dihedral12_injective]
  rfl

#print axioms rot12_pow_apply
#print axioms rot12_order
#print axioms refl12_order
#print axioms refl_rot_refl
#print axioms dihedral12_injective
#print axioms dihedral12_card

end Winding
