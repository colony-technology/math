import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-! # The Unifier: Section 1, hydrostatic inertia plane -/

namespace Unifier

theorem hydrostatic_linear (P : ℝ → ℝ) (ρ g : ℝ)
    (hP : ∀ h, HasDerivAt P (ρ * g) h)
    (h0 : P 0 = 0) :
    ∀ h, P h = ρ * g * h := by
  let L : ℝ → ℝ := fun h => ρ * g * h
  have hL : ∀ h, HasDerivAt L (ρ * g) h := by
    intro h
    simpa [L] using (hasDerivAt_id h).const_mul (ρ * g)
  have hdiffer : Differentiable ℝ (fun h => P h - L h) := by
    intro h
    exact (hP h).differentiableAt.sub (hL h).differentiableAt
  have hderiv : ∀ h, deriv (fun h => P h - L h) h = 0 := by
    intro h
    change deriv (P - L) h = 0
    simpa using ((hP h).sub (hL h)).deriv
  intro h
  have hconst := is_const_of_deriv_eq_zero hdiffer hderiv h 0
  change P h - ρ * g * h = P 0 - ρ * g * 0 at hconst
  simpa [h0, sub_eq_zero] using hconst

theorem hydrostatic_unique_level (P : ℝ → ℝ) (ρ g p : ℝ)
    (hP : ∀ h, HasDerivAt P (ρ * g) h)
    (h0 : P 0 = 0) (hρ : ρ * g ≠ 0) :
    ∃! h : ℝ, P h = p := by
  have hlin := hydrostatic_linear P ρ g hP h0
  refine ⟨p / (ρ * g), ?_, ?_⟩
  · change P (p / (ρ * g)) = p
    rw [hlin]
    calc
      ρ * g * (p / (ρ * g)) = (ρ * g) * p / (ρ * g) := by ring
      _ = p := mul_div_cancel_left₀ p hρ
  · intro h hh
    rw [hlin] at hh
    apply (eq_div_iff hρ).2
    calc
      h * (ρ * g) = (ρ * g) * h := mul_comm _ _
      _ = p := hh

/-- T2, the level itself: `P h = p` exactly when `h = p / (ρ g)`. -/
theorem hydrostatic_level_eq (P : ℝ → ℝ) (ρ g p : ℝ)
    (hP : ∀ h, HasDerivAt P (ρ * g) h)
    (h0 : P 0 = 0) (hρ : ρ * g ≠ 0) (h : ℝ) :
    P h = p ↔ h = p / (ρ * g) := by
  rw [hydrostatic_linear P ρ g hP h0 h, eq_div_iff hρ, mul_comm h]

theorem trit_keys_card (h : ℕ) :
    Fintype.card (Fin h → Fin 3) = 3 ^ h := by
  simp

theorem full_level_clog (h : ℕ) :
    Nat.clog 3 (3 ^ h) = h := by
  exact Nat.clog_pow 3 h (by decide)

#print axioms hydrostatic_linear
#print axioms hydrostatic_unique_level
#print axioms hydrostatic_level_eq
#print axioms trit_keys_card
#print axioms full_level_clog

end Unifier
