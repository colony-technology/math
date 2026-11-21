import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 7, modular and integer orbit distinction -/

namespace Unifier

theorem integer_orbit_injective (x : ℤ) :
    Function.Injective (fun t : ℕ => x + (t : ℤ)) := by
  intro a b h
  have hc : (a : ℤ) = (b : ℤ) := add_left_cancel h
  exact_mod_cast hc

theorem integer_orbit_prefix_card (x : ℤ) (t : ℕ) :
    Nat.card (Set.range (fun i : Fin t => x + (i.val : ℤ))) = t := by
  classical
  let e : Fin t ↪ ℤ :=
    ⟨(fun i : Fin t => x + (i.val : ℤ)), by
      intro a b h
      apply Fin.ext
      have hc : (a.val : ℤ) = b.val := add_left_cancel h
      exact_mod_cast hc⟩
  calc
    Nat.card (Set.range (fun i : Fin t => x + (i.val : ℤ))) =
        Nat.card (Set.range e) := rfl
    _ = Nat.card (Fin t) :=
      (Nat.card_congr (Equiv.ofInjective e e.injective)).symm
    _ = t := by simp

theorem integer_orbit_aperiodic (x : ℤ) (t : ℕ) (ht : 0 < t) :
    x + (t : ℤ) ≠ x := by
  omega

/-- T24: the orbit of the integer step `x ↦ x + 1` is `t ↦ x + t`. -/
theorem integer_step_iterate (x : ℤ) (t : ℕ) :
    (fun z : ℤ => z + 1)^[t] x = x + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      omega

/-- T24: the integer step has no periodic point. -/
theorem integer_step_no_periodic (x : ℤ) (t : ℕ) (ht : 0 < t) :
    (fun z : ℤ => z + 1)^[t] x ≠ x := by
  rw [integer_step_iterate]
  omega

theorem modular_orbit_bijective (n : ℕ) [NeZero n] (x : ZMod n) :
    Function.Bijective (fun t : Fin n => x + ZMod.finEquiv n t) := by
  constructor
  · intro a b h
    apply (ZMod.finEquiv n).injective
    exact add_left_cancel h
  · intro y
    obtain ⟨t, ht⟩ := (ZMod.finEquiv n).surjective (y - x)
    refine ⟨t, ?_⟩
    change x + (ZMod.finEquiv n) t = y
    rw [ht]
    abel

theorem modular_state_count (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n) = n := ZMod.card n

theorem modular_step_iterations (n : ℕ) [NeZero n]
    (x : ZMod n) (t : ℕ) :
    (fun z : ZMod n => z + 1)^[t] x = x + (t : ZMod n) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      simp only [ih, Nat.cast_succ]
      abel

theorem modular_step_period (n : ℕ) [NeZero n] (x : ZMod n) :
    (fun z : ZMod n => z + 1)^[n] x = x := by
  rw [modular_step_iterations]
  simp

#print axioms integer_step_iterate
#print axioms integer_step_no_periodic
#print axioms integer_orbit_injective
#print axioms integer_orbit_prefix_card
#print axioms integer_orbit_aperiodic
#print axioms modular_orbit_bijective
#print axioms modular_state_count
#print axioms modular_step_iterations
#print axioms modular_step_period

end Unifier
