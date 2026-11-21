import Mathlib.Data.Nat.Digits.Lemmas

/-! # The Unifier: Section 3, base-three accumulation and exact decoder -/

namespace Unifier

def TritKey (L : ℕ) := {digits : List ℕ //
  digits.length = L ∧ ∀ d ∈ digits, d < 3}

def base3Encode {L : ℕ} (word : TritKey L) : Fin (3 ^ L) :=
  ⟨Nat.ofDigits 3 word.val,
    Nat.mapsTo_ofDigits (by decide : 1 < 3) L word.property⟩

def base3Decode {L : ℕ} (i : Fin (3 ^ L)) : TritKey L :=
  ⟨Nat.digitsAppend 3 L i.val,
    Nat.mapsTo_digitsAppend (by decide : 1 < 3) L i.isLt⟩

theorem base3_decode_encode {L : ℕ} (word : TritKey L) :
    base3Decode (base3Encode word) = word := by
  apply Subtype.ext
  exact (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 3) L).1 word.property

theorem base3_encode_decode {L : ℕ} (i : Fin (3 ^ L)) :
    base3Encode (base3Decode i) = i := by
  apply Fin.ext
  exact (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 3) L).2 i.isLt

def base3KeyEquiv (L : ℕ) : TritKey L ≃ Fin (3 ^ L) where
  toFun := base3Encode
  invFun := base3Decode
  left_inv := base3_decode_encode
  right_inv := base3_encode_decode

theorem base3_encode_sum {L : ℕ} (word : TritKey L) :
    (base3Encode word).val =
      (word.val.mapIdx fun i digit => digit * 3 ^ i).sum := by
  exact Nat.ofDigits_eq_sum_mapIdx 3 word.val

#print axioms base3_decode_encode
#print axioms base3_encode_decode
#print axioms base3_encode_sum

end Unifier
