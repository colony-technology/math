import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! # The Unifier: Section 8, Fibonacci accumulation -/

namespace Unifier

def fibonacciStep (m : ℕ) (p : ZMod m × ZMod m) :
    ZMod m × ZMod m := (p.2, p.1 + p.2)

def fibonacciStepInv (m : ℕ) (p : ZMod m × ZMod m) :
    ZMod m × ZMod m := (p.2 - p.1, p.1)

def fibonacciStepEquiv (m : ℕ) :
    (ZMod m × ZMod m) ≃ (ZMod m × ZMod m) where
  toFun := fibonacciStep m
  invFun := fibonacciStepInv m
  left_inv := by
    intro p
    rcases p with ⟨a, b⟩
    simp [fibonacciStep, fibonacciStepInv]
  right_inv := by
    intro p
    rcases p with ⟨c, d⟩
    simp [fibonacciStep, fibonacciStepInv]

theorem fibonacci_step_bijective (m : ℕ) :
    Function.Bijective (fibonacciStep m) :=
  (fibonacciStepEquiv m).bijective

theorem fibonacci_accumulation (m n : ℕ) :
    (fibonacciStep m)^[n] (0, 1) =
      ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)) := by
  induction n with
  | zero =>
      simp [Nat.fib_zero, Nat.fib_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [fibonacciStep, Nat.succ_eq_add_one]
      rw [show n + 1 + 1 = n + 2 by omega]
      simp [Nat.fib_add_two]

#print axioms fibonacci_step_bijective
#print axioms fibonacci_accumulation

end Unifier
