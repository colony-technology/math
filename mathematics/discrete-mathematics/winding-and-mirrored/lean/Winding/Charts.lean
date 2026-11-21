import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Winding and Mirrored, W7: two charts (the Wu-Yang form of the Dirac monopole)

For real `n` and `u`: `a_N(u) = n(1-u)/2`, `a_S(u) = -n(1+u)/2`. The identities hold for every
real `u`, in particular on `[-1, 1]`. This is classical; the file only checks the identities. -/

namespace Winding

/-- The north potential `a_N(u) = n(1-u)/2`. -/
noncomputable def chartN (n u : ℝ) : ℝ := n * (1 - u) / 2

/-- The south potential `a_S(u) = -n(1+u)/2`. -/
noncomputable def chartS (n u : ℝ) : ℝ := -n * (1 + u) / 2

/-- W7(a): `a_N(u) - a_S(u) = n`. -/
theorem chart_overlap (n u : ℝ) : chartN n u - chartS n u = n := by
  unfold chartN chartS
  ring

/-- W7(b): `a_N(1) = 0`. -/
theorem chartN_north (n : ℝ) : chartN n 1 = 0 := by
  unfold chartN
  ring

/-- W7(b): `a_S(-1) = 0`. -/
theorem chartS_south (n : ℝ) : chartS n (-1) = 0 := by
  unfold chartS
  ring

/-- W7(c): `d a_N / du = -n/2`. -/
theorem chartN_hasDerivAt (n u : ℝ) : HasDerivAt (chartN n) (-n / 2) u := by
  have h := (((hasDerivAt_id u).const_sub 1).const_mul n).div_const 2
  have e : (fun y => n * (1 - id y) / 2) = chartN n := by
    funext y
    simp [chartN]
  rw [e] at h
  convert h using 1
  ring

/-- W7(c): `d a_S / du = -n/2`. -/
theorem chartS_hasDerivAt (n u : ℝ) : HasDerivAt (chartS n) (-n / 2) u := by
  have h := (((hasDerivAt_id u).const_add 1).const_mul (-n)).div_const 2
  have e : (fun y => -n * (1 + id y) / 2) = chartS n := by
    funext y
    simp [chartS]
  rw [e] at h
  convert h using 1
  ring

/-- W7(c), as values of `deriv`. -/
theorem chart_deriv (n u : ℝ) :
    deriv (chartN n) u = -n / 2 ∧ deriv (chartS n) u = -n / 2 :=
  ⟨(chartN_hasDerivAt n u).deriv, (chartS_hasDerivAt n u).deriv⟩

/-- W7(d): `∫_{-1}^{1} n/2 du = n`. -/
theorem chart_flux (n : ℝ) : ∫ _ in (-1 : ℝ)..1, n / 2 = n := by
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

#print axioms chart_overlap
#print axioms chartN_north
#print axioms chartS_south
#print axioms chartN_hasDerivAt
#print axioms chartS_hasDerivAt
#print axioms chart_deriv
#print axioms chart_flux

end Winding
