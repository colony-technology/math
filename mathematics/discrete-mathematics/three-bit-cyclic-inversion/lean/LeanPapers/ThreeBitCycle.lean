import LeanPapers.ThreeBitPaper

namespace ThreeBitCyclic

def zeroTriple : Bool × Bool × Bool := (false,false,false)

/-- For all widths, the seven-step transition is the identity. -/
theorem linearStep_iterate_mod_seven (s : Bool × Bool × Bool) (n : Nat) :
    (linearStep^[n]) s = (linearStep^[n % 7]) s := by
  have h7 : (linearStep^[7]) = id := by
    funext t
    exact linearStep_period_seven t
  have hdiv : (linearStep^[7 * (n / 7)]) s = s := by
    rw [Function.iterate_mul, h7]
    simp
  calc
    (linearStep^[n]) s =
        (linearStep^[n % 7 + 7 * (n / 7)]) s := by
          congr 1
          exact (Nat.mod_add_div n 7).symm
    _ = (linearStep^[n % 7]) ((linearStep^[7 * (n / 7)]) s) :=
      Function.iterate_add_apply _ _ _ _
    _ = (linearStep^[n % 7]) s := by rw [hdiv]

/-- Zero is the unique fixed state at each exponent from 1 to 6. -/
theorem linearStep_small_fixed_points
    (s : Bool × Bool × Bool) (r : Nat) (hr : r < 7) :
    ((linearStep^[r]) s = s) ↔ (r = 0 ∨ s = zeroTriple) := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨
      r = 4 ∨ r = 5 ∨ r = 6 by omega) with
      h | h | h | h | h | h | h
  all_goals
    subst r
    rcases s with ⟨a,b,d⟩
    cases a <;> cases b <;> cases d <;> decide

/-- Exact orbit-closure criterion, for every width, without width enumeration. -/
theorem linearStep_fixed_iff (s : Bool × Bool × Bool) (w : Nat) :
    ((linearStep^[w]) s = s) ↔ (7 ∣ w ∨ s = zeroTriple) := by
  rw [linearStep_iterate_mod_seven]
  rw [linearStep_small_fixed_points s (w % 7) (by omega)]
  simp only [Nat.dvd_iff_mod_eq_zero]

#print axioms linearStep_iterate_mod_seven
#print axioms linearStep_small_fixed_points
#print axioms linearStep_fixed_iff

end ThreeBitCyclic
