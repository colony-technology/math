import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # Winding and Mirrored, W5: mirror parity split

`V` a vector space over a field `K`, `X` a finite set, `M` a `K`-linear map on `X → V` with
`M (M F) = F` that maps mean-zero functions to mean-zero functions. The mean divides by `|X|`
and the split divides by `2`, so the theorem assumes `(2 : K) ≠ 0` and `(|X| : K) ≠ 0`
(NOTE-1.md: characteristic not 2 alone is not enough when the characteristic divides `|X|`).
Both hold over `ℚ` for nonempty `X`. -/

namespace Winding

open Finset

section General

variable (K : Type*) {V X : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype X]

/-- The mean of `F : X → V`, a vector of `V`. -/
def avg (F : X → V) : V := (Fintype.card X : K)⁻¹ • ∑ x, F x

variable {K}

theorem avg_sub (F G : X → V) : avg K (F - G) = avg K F - avg K G := by
  simp only [avg, Pi.sub_apply, Finset.sum_sub_distrib, smul_sub]

theorem avg_add (F G : X → V) : avg K (F + G) = avg K F + avg K G := by
  simp only [avg, Pi.add_apply, Finset.sum_add_distrib, smul_add]

theorem avg_smul (c : K) (F : X → V) : avg K (c • F) = c • avg K F := by
  simp only [avg, Pi.smul_apply, ← Finset.smul_sum, smul_comm c]

theorem avg_const (hX : (Fintype.card X : K) ≠ 0) (v : V) : avg K (fun _ : X => v) = v := by
  simp only [avg, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]
  exact inv_smul_smul₀ hX v

/-- W5: with `h` the mean of `F` (a constant function), `G = F - h`, `m = (G - M G)/2`,
`k = (G + M G)/2`: `F = m + k + h`, `M m = -m`, `M k = k`, and `m`, `k` have mean zero. -/
theorem parity_split (h2 : (2 : K) ≠ 0) (hX : (Fintype.card X : K) ≠ 0)
    (M : (X → V) →ₗ[K] (X → V)) (hMM : ∀ F, M (M F) = F)
    (hM0 : ∀ F, avg K F = 0 → avg K (M F) = 0) (F : X → V) :
    let h : X → V := fun _ => avg K F
    let G := F - h
    let m := (2 : K)⁻¹ • (G - M G)
    let k := (2 : K)⁻¹ • (G + M G)
    F = m + k + h ∧ M m = -m ∧ M k = k ∧ avg K m = 0 ∧ avg K k = 0 := by
  intro h G m k
  have hG : avg K G = 0 := by
    show avg K (F - h) = 0
    rw [avg_sub, avg_const hX, sub_self]
  have hMG : avg K (M G) = 0 := hM0 G hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hmk : m + k = G := by
      show (2 : K)⁻¹ • (G - M G) + (2 : K)⁻¹ • (G + M G) = G
      rw [← smul_add, show G - M G + (G + M G) = (2 : K) • G by rw [two_smul]; abel]
      exact inv_smul_smul₀ h2 G
    rw [hmk]
    show F = F - h + h
    rw [sub_add_cancel]
  · show M ((2 : K)⁻¹ • (G - M G)) = -((2 : K)⁻¹ • (G - M G))
    rw [map_smul, map_sub, hMM, ← smul_neg, neg_sub]
  · show M ((2 : K)⁻¹ • (G + M G)) = (2 : K)⁻¹ • (G + M G)
    rw [map_smul, map_add, hMM, add_comm]
  · show avg K ((2 : K)⁻¹ • (G - M G)) = 0
    rw [avg_smul, avg_sub, hG, hMG, sub_zero, smul_zero]
  · show avg K ((2 : K)⁻¹ • (G + M G)) = 0
    rw [avg_smul, avg_add, hG, hMG, add_zero, smul_zero]

/-- W5 over a field of characteristic zero with `X` nonempty. -/
theorem parity_split_charZero [CharZero K] [Nonempty X]
    (M : (X → V) →ₗ[K] (X → V)) (hMM : ∀ F, M (M F) = F)
    (hM0 : ∀ F, avg K F = 0 → avg K (M F) = 0) (F : X → V) :
    let h : X → V := fun _ => avg K F
    let G := F - h
    let m := (2 : K)⁻¹ • (G - M G)
    let k := (2 : K)⁻¹ • (G + M G)
    F = m + k + h ∧ M m = -m ∧ M k = k ∧ avg K m = 0 ∧ avg K k = 0 :=
  parity_split (by norm_num) (Nat.cast_ne_zero.2 Fintype.card_ne_zero) M hMM hM0 F

end General

section Instance

/-- The rectangle `R` as the finite type `Fin (2n) × Fin n`, `n = 2^k`. -/
abbrev Rect (k : ℕ) := Fin (2 * 2 ^ k) × Fin (2 ^ k)

/-- The mirror `mu(x, y) = (2n - 1 - x, y)` on `R`: `Fin.rev` on the first coordinate. -/
def rectMirror (k : ℕ) : Equiv.Perm (Rect k) := Equiv.prodCongr Fin.revPerm (Equiv.refl _)

theorem rectMirror_val (k : ℕ) (p : Rect k) :
    ((rectMirror k p).1 : ℕ) = 2 * 2 ^ k - 1 - p.1 ∧ (rectMirror k p).2 = p.2 := by
  refine ⟨?_, rfl⟩
  show ((Fin.rev p.1 : Fin (2 * 2 ^ k)) : ℕ) = _
  rw [Fin.val_rev]
  omega

theorem rectMirror_mirror (k : ℕ) (p : Rect k) : rectMirror k (rectMirror k p) = p := by
  obtain ⟨x, y⟩ := p
  simp [rectMirror]

/-- The vector mirror `(M F)(p) = (-F_x(mu p), F_y(mu p))` on `R → ℚ²`. -/
def vecMirror (k : ℕ) : (Rect k → ℚ × ℚ) →ₗ[ℚ] (Rect k → ℚ × ℚ) where
  toFun F p := (-(F (rectMirror k p)).1, (F (rectMirror k p)).2)
  map_add' F G := by
    funext p
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, neg_add, Prod.mk_add_mk]
  map_smul' c F := by
    funext p
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, mul_neg]

theorem vecMirror_apply (k : ℕ) (F : Rect k → ℚ × ℚ) (p : Rect k) :
    vecMirror k F p = (-(F (rectMirror k p)).1, (F (rectMirror k p)).2) := rfl

theorem vecMirror_involutive (k : ℕ) (F : Rect k → ℚ × ℚ) : vecMirror k (vecMirror k F) = F := by
  funext p
  simp only [vecMirror_apply, rectMirror_mirror, neg_neg]

theorem vecMirror_sum (k : ℕ) (F : Rect k → ℚ × ℚ) :
    ∑ p, vecMirror k F p = (-(∑ p, F p).1, (∑ p, F p).2) := by
  have e1 : ∑ p, (F (rectMirror k p)).1 = ∑ p, (F p).1 :=
    Equiv.sum_comp (rectMirror k) (fun p => (F p).1)
  have e2 : ∑ p, (F (rectMirror k p)).2 = ∑ p, (F p).2 :=
    Equiv.sum_comp (rectMirror k) (fun p => (F p).2)
  simp only [vecMirror_apply]
  ext
  · simp only [Prod.fst_sum, Finset.sum_neg_distrib, e1]
  · simp only [Prod.snd_sum, e2]

theorem card_rect_ne_zero (k : ℕ) : (Fintype.card (Rect k) : ℚ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact Fintype.card_ne_zero

theorem vecMirror_meanZero (k : ℕ) (F : Rect k → ℚ × ℚ) (hF : avg ℚ F = 0) :
    avg ℚ (vecMirror k F) = 0 := by
  have hX := card_rect_ne_zero k
  unfold avg at hF ⊢
  have hs : ∑ p, F p = 0 := by
    have := congrArg (fun v : ℚ × ℚ => (Fintype.card (Rect k) : ℚ) • v) hF
    rwa [smul_inv_smul₀ hX, smul_zero] at this
  rw [vecMirror_sum, hs]
  simp

/-- W5, the instance: `X = R`, `V = ℚ²`, `(M F)(p) = (-F_x(mu p), F_y(mu p))`. -/
theorem parity_split_rect (k : ℕ) (F : Rect k → ℚ × ℚ) :
    let h : Rect k → ℚ × ℚ := fun _ => avg ℚ F
    let G := F - h
    let m := (2 : ℚ)⁻¹ • (G - vecMirror k G)
    let kk := (2 : ℚ)⁻¹ • (G + vecMirror k G)
    F = m + kk + h ∧ vecMirror k m = -m ∧ vecMirror k kk = kk ∧ avg ℚ m = 0 ∧ avg ℚ kk = 0 :=
  parity_split (by norm_num) (card_rect_ne_zero k) (vecMirror k) (vecMirror_involutive k)
    (vecMirror_meanZero k) F

end Instance

#print axioms avg_const
#print axioms parity_split
#print axioms parity_split_charZero
#print axioms rectMirror_val
#print axioms rectMirror_mirror
#print axioms vecMirror_involutive
#print axioms vecMirror_sum
#print axioms vecMirror_meanZero
#print axioms parity_split_rect

end Winding
