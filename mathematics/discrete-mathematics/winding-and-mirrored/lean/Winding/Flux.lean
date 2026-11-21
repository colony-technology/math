import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-! # Winding and Mirrored, W6: mirror-return flux

The grid `Z/m × Z/n'`, both coordinates periodic. An edge field gives a rational to the `+x` edge
from `v` to `v + (1, 0)` and to the `+y` edge from `v` to `v + (0, 1)`. The divergence at `v` is
outflow minus inflow. Part (b) takes `m = 2n`. -/

namespace Winding

/-- An edge field on the periodic grid `Z/m × Z/n'`: `ex v` on the edge `v → v + (1,0)`,
`ey v` on the edge `v → v + (0,1)`. -/
structure EdgeField (m n' : ℕ) where
  ex : ZMod m × ZMod n' → ℚ
  ey : ZMod m × ZMod n' → ℚ

/-- Outflow minus inflow at `v`. -/
def divergence {m n' : ℕ} (E : EdgeField m n') (v : ZMod m × ZMod n') : ℚ :=
  E.ex v + E.ey v - E.ex (v - (1, 0)) - E.ey (v - (0, 1))

/-- W6(a): the divergence sums to `0` over all cells, for every edge field. -/
theorem divergence_sum {m n' : ℕ} [NeZero m] [NeZero n'] (E : EdgeField m n') :
    ∑ v, divergence E v = 0 := by
  have h1 : ∑ v, E.ex (v - (1, 0)) = ∑ v, E.ex v :=
    Equiv.sum_comp (Equiv.subRight ((1, 0) : ZMod m × ZMod n')) E.ex
  have h2 : ∑ v, E.ey (v - (0, 1)) = ∑ v, E.ey v :=
    Equiv.sum_comp (Equiv.subRight ((0, 1) : ZMod m × ZMod n')) E.ey
  simp only [divergence, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

section Seam

variable (n : ℕ) [NeZero n]

instance neZero_two_mul : NeZero (2 * n) := ⟨by have := NeZero.ne n; omega⟩

/-- The cell `(n-1, 0)`, last of the left sheet. -/
def seamLeft : ZMod (2 * n) × ZMod n := (((n - 1 : ℕ) : ZMod (2 * n)), 0)

/-- The cell `(n, 0)`, first of the mirrored sheet. -/
def seamRight : ZMod (2 * n) × ZMod n := (((n : ℕ) : ZMod (2 * n)), 0)

/-- The field of W6(b): `c` on every `+x` edge, plus `q` on the edge `(n-1,0) → (n,0)`,
and `0` on every `+y` edge. -/
def seamField (c q : ℚ) : EdgeField (2 * n) n where
  ex v := c + if v = seamLeft n then q else 0
  ey _ := 0

theorem seamLeft_add : seamLeft n + (1, 0) = seamRight n := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  simp only [seamLeft, seamRight, Prod.mk_add_mk, add_zero, Prod.mk.injEq, and_true]
  rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel h1]

theorem seamLeft_val : (seamLeft n).1.val = n - 1 := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  exact ZMod.val_natCast_of_lt (by omega)

theorem seamRight_val : (seamRight n).1.val = n := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  exact ZMod.val_natCast_of_lt (by omega)

theorem seamLeft_ne_seamRight : seamLeft n ≠ seamRight n := by
  intro h
  have := congrArg (fun v => v.1.val) h
  simp only [seamLeft_val, seamRight_val] at this
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  omega

/-- W6(b): the divergence of the seam field is `+q` at `(n-1,0)`, `-q` at `(n,0)`, `0` elsewhere. -/
theorem seam_divergence (c q : ℚ) (v : ZMod (2 * n) × ZMod n) :
    divergence (seamField n c q) v =
      (if v = seamLeft n then q else 0) - (if v = seamRight n then q else 0) := by
  have e : (v - (1, 0) = seamLeft n) ↔ v = seamRight n := by
    rw [sub_eq_iff_eq_add, seamLeft_add]
  simp only [divergence, seamField, e]
  ring

theorem seam_divergence_left (c q : ℚ) : divergence (seamField n c q) (seamLeft n) = q := by
  rw [seam_divergence, if_pos rfl, if_neg (seamLeft_ne_seamRight n)]
  ring

theorem seam_divergence_right (c q : ℚ) : divergence (seamField n c q) (seamRight n) = -q := by
  rw [seam_divergence, if_neg (Ne.symm (seamLeft_ne_seamRight n)), if_pos rfl]
  ring

theorem seam_divergence_other (c q : ℚ) (v : ZMod (2 * n) × ZMod n) (h1 : v ≠ seamLeft n)
    (h2 : v ≠ seamRight n) : divergence (seamField n c q) v = 0 := by
  rw [seam_divergence, if_neg h1, if_neg h2]
  ring

/-- W6(b): the sum over the left sheet `x < n` is `+q`. -/
theorem seam_left_sheet (c q : ℚ) :
    ∑ v ∈ Finset.univ.filter (fun v : ZMod (2 * n) × ZMod n => v.1.val < n),
      divergence (seamField n c q) v = q := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  simp only [seam_divergence, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, seamLeft_val, seamRight_val]
  rw [if_pos (by omega), if_neg (by omega)]
  ring

/-- W6(b): the sum over the mirrored sheet `x ≥ n` is `-q`. -/
theorem seam_right_sheet (c q : ℚ) :
    ∑ v ∈ Finset.univ.filter (fun v : ZMod (2 * n) × ZMod n => n ≤ v.1.val),
      divergence (seamField n c q) v = -q := by
  have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  simp only [seam_divergence, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, seamLeft_val, seamRight_val]
  rw [if_neg (by omega), if_pos (le_refl n)]
  ring

end Seam

/-- W6(b) at the sizes of the ring: `n = 2^k`. -/
theorem seam_sheets_pow (k : ℕ) (c q : ℚ) :
    (∑ v ∈ Finset.univ.filter (fun v : ZMod (2 * 2 ^ k) × ZMod (2 ^ k) => v.1.val < 2 ^ k),
      divergence (seamField (2 ^ k) c q) v = q) ∧
    (∑ v ∈ Finset.univ.filter (fun v : ZMod (2 * 2 ^ k) × ZMod (2 ^ k) => 2 ^ k ≤ v.1.val),
      divergence (seamField (2 ^ k) c q) v = -q) :=
  ⟨seam_left_sheet (2 ^ k) c q, seam_right_sheet (2 ^ k) c q⟩

#print axioms divergence_sum
#print axioms seam_divergence
#print axioms seam_divergence_left
#print axioms seam_divergence_right
#print axioms seam_divergence_other
#print axioms seam_left_sheet
#print axioms seam_right_sheet
#print axioms seam_sheets_pow

end Winding
