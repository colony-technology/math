# Lean 4 formalization

**lmtlssss🜐 · 21 November 2026**

Every theorem of the paper, T1 to T25 and C1 to C5, is proved in Lean 4.35.0 with Mathlib v4.35.0. The seventeen files contain 132 theorems. None uses `sorry`, `native_decide` or an added axiom. `#print axioms` on each of them reports only `propext`, `Classical.choice` and `Quot.sound`, or no axiom.

| Paper | Lean declarations | File |
| --- | --- | --- |
| T1 | `hydrostatic_linear` | `Unifier/Inertia.lean` |
| T2 | `hydrostatic_unique_level`, `hydrostatic_level_eq` | `Unifier/Inertia.lean` |
| T3 | `trit_keys_card`, `full_level_clog` | `Unifier/Inertia.lean` |
| T4 | `observationSetoid`, `quotient_projection_exact`, `quotient_projection_surjective`, `factorBoundary`, `factorBoundary_spec`, `factorBoundary_unique`, `factorBoundary_surjective`, `quotient_finite`, `quotient_card_le`, `exactBoundaryEquiv`, `exactBoundaryEquiv_spec`, `exactBoundaryEquiv_unique` | `Unifier/Contraction.lean` |
| T5 | `nativeTensor_one`, `nativeTensor_bit_xor`, `nativeTensor_square`, `nativeTensor_half` | `Unifier/Ternary.lean` |
| T6 | `tritForkEquiv`, `tritToRails_left`, `tritToRails_right`, `trit_no_forbidden_corner` | `Unifier/Ternary.lean` |
| T7 | `base3KeyEquiv`, `base3_decode_encode`, `base3_encode_decode`, `base3_encode_sum` | `Unifier/TritKeys.lean` |
| T8 | `response_mono`, `response_fork`, `windowTrit_classes` | `Unifier/Carry.lean` |
| T9 | `response_append`, `windowTrit_compose`, `tritCompose_assoc`, `tritCompose_left_id`, `tritCompose_right_id` | `Unifier/Carry.lean` |
| T10 | `response_normal_and`, `response_normal_or` | `Unifier/Carry.lean` |
| T11 | `oneStage_three`, `oneStage_surjective`, `oneStage_exact`, `oneStage_no_bool_boundary`, `oneStageQuotEquiv`, `oneStage_class_count` | `Unifier/Carry.lean` |
| T12 | `reverse_lookup_coefficient`, `reverse_lookup_integer` | `Unifier/Reverse.lean` |
| T13 | `reverse_lookup_angle` | `Unifier/Angle.lean` |
| T14 | `zodiac_reverse_mod12`, `successor_reverse_divisible`, `successor_reverse_mod` | `Unifier/Reverse.lean` |
| T15 | `dial_round_tolerance`, `uniform_dial_error`, `round_uniform_dial`, `reverse_lookup_from_readings` | `Unifier/Rounding.lean` |
| T16 | `straight_scale_tolerance`, `straight_scale_half_tie` | `Unifier/Rounding.lean` |
| T17 | `hilbert_bijOn`, `hilbert_mapsTo`, `hilbert_injOn`, `hilbert_surjOn` | `Unifier/Hilbert.lean` |
| T18 | `hilbert_locality`, `hilbert_chebyshev` | `Unifier/Hilbert.lean` |
| T19 | `hilbert_quarters`, `hilbertH_succ`, `hilbert_start`, `hilbert_end` | `Unifier/Hilbert.lean` |
| T20 | `unifier_exists`, `canonical_iso`, `unique_iso`, `unifier_unique_factorization` | `Unifier/Factorization.lean` |
| T21 | `trit_cost_factorization`, `trit_cost_minimal`, `range_card_le_of_factorization`, `independent_product_tritCost`, `correlated_pairing_counterexample` | `Unifier/Cost.lean` |
| T22 | `straight_distance`, `straight_lyapunov`, `straight_lyapunov_positive`, `straight_scale_unstable` | `Unifier/Straight.lean` |
| T23 | `dial_reader_idempotent`, `dial_reader_tick`, `dial_reader_tolerance` | `Unifier/Rounding.lean` |
| T24 | `integer_step_iterate`, `integer_step_no_periodic`, `integer_orbit_injective`, `integer_orbit_prefix_card`, `integer_orbit_aperiodic`, `modular_orbit_bijective`, `modular_state_count`, `modular_step_iterations`, `modular_step_period` | `Unifier/Dynamics.lean` |
| T25 | `dial_circumference`, `dial_curvature_inverse_radius`, `dial_curvature_relation`, `dial_tolerance_positive`, `dial_tolerance_straight_limit` | `Unifier/Curvature.lean` |
| C1 | `fibonacciStepEquiv`, `fibonacci_step_bijective`, `fibonacci_accumulation` | `Unifier/Fibonacci.lean` |
| C2 | `segmented_log_two` | `Unifier/SegmentedLog.lean` |
| C3 | `impossible_halfway_root`, `sqrt_ne_half_integer` | `Unifier/Special.lean` |
| C4 | `zodiac_reverse_mod12`, `successor_reverse_mod` | `Unifier/Reverse.lean` |
| C5 | `bitWindow_response`, `binary_full_adder`, `binary_block_carry`, `bitWindow_trit`, `bitsValue_eq_sum`, `rippleCarry_eq_blockCarry`, `binary_word_adder`, `bitsValue_lt`, `rippleSum_length`, `rippleSum_getD`, `binary_word_adder_digits` | `Unifier/Carry.lean` |

A window is a list of `Step`s read from the top, and `response S r` is its response to the incoming bit `r`. `windowTrit S` is the trit of the window. `hilbertH k d` is the Hilbert coordinate of Definition 6.1, and `tritCost f` is the cost of Definition 7.1. `round` is Mathlib's rounding, which sends a half upward as the paper's does (`straight_scale_half_tie`).

## Rebuild

```sh
lake exe cache get
lake build Unifier
lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` prints the axioms of every declaration in the table. A build from the sources alone on 21 November 2026 completed 2,269 jobs with exit status 0.

## Statements as compiled

### T1 to T3, the hydrostatic column

`Unifier.hydrostatic_linear`, `Unifier/Inertia.lean`, line 10

```lean
theorem hydrostatic_linear (P : ℝ → ℝ) (ρ g : ℝ)
    (hP : ∀ h, HasDerivAt P (ρ * g) h)
    (h0 : P 0 = 0) :
    ∀ h, P h = ρ * g * h
```

```text
'Unifier.hydrostatic_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.hydrostatic_unique_level`, `Unifier/Inertia.lean`, line 30

```lean
theorem hydrostatic_unique_level (P : ℝ → ℝ) (ρ g p : ℝ)
    (hP : ∀ h, HasDerivAt P (ρ * g) h)
    (h0 : P 0 = 0) (hρ : ρ * g ≠ 0) :
    ∃! h : ℝ, P h = p
```

```text
'Unifier.hydrostatic_unique_level' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.full_level_clog`, `Unifier/Inertia.lean`, line 59

```lean
theorem full_level_clog (h : ℕ) :
    Nat.clog 3 (3 ^ h) = h
```

```text
'Unifier.full_level_clog' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T4, the contraction

`Unifier.quotient_projection_exact`, `Unifier/Contraction.lean`, line 31

```lean
theorem quotient_projection_exact {X : Type u}
    (s : Setoid X) (x y : X) :
    (Quotient.mk s x = Quotient.mk s y) ↔ s.r x y
```

```text
'Unifier.quotient_projection_exact' depends on axioms: [propext, Quot.sound]
```

`Unifier.factorBoundary_unique`, `Unifier/Contraction.lean`, line 57

```lean
theorem factorBoundary_unique {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B) (hb : retainedBoundary s b)
    (r : Set.range b → Quotient s)
    (hr : ∀ x, r ⟨b x, ⟨x, rfl⟩⟩ = Quotient.mk s x) :
    r = factorBoundary s b hb
```

```text
'Unifier.factorBoundary_unique' depends on axioms: [Classical.choice, Quot.sound]
```

`Unifier.quotient_card_le`, `Unifier/Contraction.lean`, line 80

```lean
theorem quotient_card_le {X : Type u} {B : Type v} [Fintype B]
    (s : Setoid X) [Fintype (Quotient s)]
    (b : X → B) (hb : retainedBoundary s b) :
    Fintype.card (Quotient s) ≤ Fintype.card B
```

```text
'Unifier.quotient_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.exactBoundaryEquiv_unique`, `Unifier/Contraction.lean`, line 120

```lean
theorem exactBoundaryEquiv_unique {X : Type u} {B : Type v}
    (s : Setoid X) (b : X → B)
    (he : exactBoundary s b) (hs : Function.Surjective b)
    (e : B ≃ Quotient s)
    (h : ∀ x, e (b x) = Quotient.mk s x) :
    e = exactBoundaryEquiv s b he hs
```

```text
'Unifier.exactBoundaryEquiv_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T5 to T7, the native product, the fork and base-3 keys

`Unifier.nativeTensor_bit_xor`, `Unifier/Ternary.lean`, line 13

```lean
theorem nativeTensor_bit_xor (a b : Bool) :
    a.toNat + b.toNat = (a.xor b).toNat + nativeTensor a.toNat b.toNat
```

```text
'Unifier.nativeTensor_bit_xor' does not depend on any axioms
```

`Unifier.tritToRails_left`, `Unifier/Ternary.lean`, line 53

```lean
theorem tritToRails_left (t : Fin 3) :
    railsToTrit (tritToRails t) = t
```

```text
'Unifier.tritToRails_left' depends on axioms: [propext, Quot.sound]
```

`Unifier.tritToRails_right`, `Unifier/Ternary.lean`, line 60

```lean
theorem tritToRails_right (p : LegalRails) :
    tritToRails (railsToTrit p) = p
```

```text
'Unifier.tritToRails_right' depends on axioms: [propext, Quot.sound]
```

`Unifier.base3_encode_sum`, `Unifier/TritKeys.lean`, line 34

```lean
theorem base3_encode_sum {L : ℕ} (word : TritKey L) :
    (base3Encode word).val =
      (word.val.mapIdx fun i digit => digit * 3 ^ i).sum
```

```text
'Unifier.base3_encode_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T8 to T11, the fork in every ordered decision

`Unifier.response_fork`, `Unifier/Carry.lean`, line 37

```lean
theorem response_fork (S : List Step) (r : Bool) :
    response S r = (response S false || (response S true && r))
```

```text
'Unifier.response_fork' depends on axioms: [propext]
```

`Unifier.windowTrit_classes`, `Unifier/Carry.lean`, line 45

```lean
theorem windowTrit_classes (S : List Step) (r : Bool) :
    (windowTrit S = 0 → response S r = false) ∧
    (windowTrit S = 1 → response S r = r) ∧
    (windowTrit S = 2 → response S r = true)
```

```text
'Unifier.windowTrit_classes' depends on axioms: [propext]
```

`Unifier.windowTrit_compose`, `Unifier/Carry.lean`, line 69

```lean
theorem windowTrit_compose (S T : List Step) :
    windowTrit (S ++ T) = tritCompose (windowTrit S) (windowTrit T)
```

```text
'Unifier.windowTrit_compose' depends on axioms: [propext]
```

`Unifier.response_normal_and`, `Unifier/Carry.lean`, line 106

```lean
theorem response_normal_and (S : List Step) (r : Bool) :
    response S r = (response S false || (allAnd S && r))
```

```text
'Unifier.response_normal_and' depends on axioms: [propext]
```

`Unifier.response_normal_or`, `Unifier/Carry.lean`, line 117

```lean
theorem response_normal_or (S : List Step) (r : Bool) :
    response S r = (response S true && (allOr S || r))
```

```text
'Unifier.response_normal_or' depends on axioms: [propext]
```

`Unifier.oneStage_class_count`, `Unifier/Carry.lean`, line 248

```lean
theorem oneStage_class_count : Fintype.card (Quotient oneStageSetoid) = 3
```

```text
'Unifier.oneStage_class_count' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.oneStage_no_bool_boundary`, `Unifier/Carry.lean`, line 159

```lean
theorem oneStage_no_bool_boundary (b : Bool × Bool → Bool)
    (hb : ∀ u v, b u = b v → oneStageTrit u = oneStageTrit v) : False
```

```text
'Unifier.oneStage_no_bool_boundary' depends on axioms: [propext]
```

### T12 to T16, reverse lookup and its tolerance

`Unifier.reverse_lookup_integer`, `Unifier/Reverse.lean`, line 78

```lean
theorem reverse_lookup_integer (k : ℕ) (N x : ℤ)
    (n ε a : Fin k → ℤ)
    (hn : ∀ i, n i ∣ N)
    (hres : ∀ i, n i ∣ a i - x)
    (hsum : (∑ i : Fin k, ε i * (N / n i)) = 1) :
    N ∣ (∑ i : Fin k, (ε i * (N / n i)) * a i) - x
```

```text
'Unifier.reverse_lookup_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.reverse_lookup_coefficient`, `Unifier/Reverse.lean`, line 33

```lean
theorem reverse_lookup_coefficient (k : ℕ) (N x : ℤ)
    (n c a : Fin k → ℤ)
    (hcoeff : ∀ i, N ∣ c i * n i)
    (hres : ∀ i, n i ∣ a i - x)
    (hsum : N ∣ (∑ i : Fin k, c i) - 1) :
    N ∣ (∑ i : Fin k, c i * a i) - x
```

```text
'Unifier.reverse_lookup_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.reverse_lookup_angle`, `Unifier/Angle.lean`, line 10

```lean
theorem reverse_lookup_angle (k : ℕ) (N x : ℤ)
    (n ε : Fin k → ℤ)
    (hN : (N : ℚ) ≠ 0)
    (hn : ∀ i, (n i : ℚ) ≠ 0)
    (hunit : 1 / (N : ℚ) = ∑ i : Fin k, (ε i : ℚ) / (n i : ℚ)) :
    ∃ m : ℤ, (x : ℚ) / (N : ℚ) =
      (∑ i : Fin k, (ε i : ℚ) * ((x % n i : ℤ) : ℚ) / (n i : ℚ))
       + (m : ℚ)
```

```text
'Unifier.reverse_lookup_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.zodiac_reverse_mod12`, `Unifier/Reverse.lean`, line 11

```lean
theorem zodiac_reverse_mod12 (x : ℤ) :
    (x - (4 * (x % 3) - 3 * (x % 4))) % 12 = 0
```

```text
'Unifier.zodiac_reverse_mod12' depends on axioms: [propext, Quot.sound]
```

`Unifier.successor_reverse_mod`, `Unifier/Reverse.lean`, line 27

```lean
theorem successor_reverse_mod (n : ℕ) (hn : 1 ≤ n) (x : ℤ) :
    ((n : ℤ) * ((n : ℤ) + 1)) ∣
      x - (((n : ℤ) + 1) * (x % (n : ℤ)) -
           (n : ℤ) * (x % ((n : ℤ) + 1)))
```

```text
'Unifier.successor_reverse_mod' depends on axioms: [propext, Quot.sound]
```

`Unifier.round_uniform_dial`, `Unifier/Rounding.lean`, line 104

```lean
theorem round_uniform_dial (nmin nmax n : ℕ)
    (hmin : 1 ≤ nmin) (hmid : nmin ≤ n) (hmax : n ≤ nmax)
    (a : ℤ) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / n| <
      1 / (2 * ((nmax + nmin : ℕ) : ℝ))) :
    round ((n : ℝ) * θ) = a
```

```text
'Unifier.round_uniform_dial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.reverse_lookup_from_readings`, `Unifier/Rounding.lean`, line 116

```lean
theorem reverse_lookup_from_readings (k : ℕ) (N x : ℤ) (nmin nmax : ℕ)
    (n : Fin k → ℕ) (c : Fin k → ℤ) (θ : Fin k → ℝ)
    (hmin : 1 ≤ nmin) (hrange : ∀ i, nmin ≤ n i ∧ n i ≤ nmax)
    (hcoeff : ∀ i, N ∣ c i * (n i : ℤ))
    (hsum : N ∣ (∑ i : Fin k, c i) - 1)
    (hθ : ∀ i, |θ i - ((x % (n i : ℤ) : ℤ) : ℝ) / (n i : ℝ)| <
      1 / (2 * ((nmax + nmin : ℕ) : ℝ))) :
    N ∣ (∑ i : Fin k, c i * round ((n i : ℝ) * θ i)) - x
```

```text
'Unifier.reverse_lookup_from_readings' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.straight_scale_tolerance`, `Unifier/Rounding.lean`, line 38

```lean
theorem straight_scale_tolerance (N : ℕ) (hN : 0 < N)
    (x : ℤ) (δ : ℝ)
    (h : |δ| < 1 / (2 * N)) :
    round ((N : ℝ) * ((x : ℝ) / N + δ)) = x
```

```text
'Unifier.straight_scale_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.straight_scale_half_tie`, `Unifier/Rounding.lean`, line 50

```lean
theorem straight_scale_half_tie (N : ℕ) (hN : 0 < N)
    (x : ℤ) :
    round ((N : ℝ) * ((x : ℝ) / N + 1 / (2 * N))) = x + 1
```

```text
'Unifier.straight_scale_half_tie' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T17 to T19, the Hilbert coordinate

`Unifier.hilbert_bijOn`, `Unifier/Hilbert.lean`, line 215

```lean
theorem hilbert_bijOn (k : ℕ) :
    Set.BijOn (hilbertH k) {d | d < 4 ^ k} (hilbertGrid k)
```

```text
'Unifier.hilbert_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.hilbert_locality`, `Unifier/Hilbert.lean`, line 228

```lean
theorem hilbert_locality (k : ℕ) :
    ∀ d, d + 1 < 4 ^ k → GridAdjacent (hilbertH k d) (hilbertH k (d + 1))
```

```text
'Unifier.hilbert_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.hilbert_quarters`, `Unifier/Hilbert.lean`, line 270

```lean
theorem hilbert_quarters (k r : ℕ) (hr : r < 4 ^ k) :
    hilbertH (k + 1) (0 * 4 ^ k + r) = ((hilbertH k r).2, (hilbertH k r).1) ∧
    hilbertH (k + 1) (1 * 4 ^ k + r) = ((hilbertH k r).1, (hilbertH k r).2 + 2 ^ k) ∧
    hilbertH (k + 1) (2 * 4 ^ k + r) =
      ((hilbertH k r).1 + 2 ^ k, (hilbertH k r).2 + 2 ^ k) ∧
    hilbertH (k + 1) (3 * 4 ^ k + r) =
      (2 * 2 ^ k - 1 - (hilbertH k r).2, 2 ^ k - 1 - (hilbertH k r).1)
```

```text
'Unifier.hilbert_quarters' depends on axioms: [propext]
```

`Unifier.hilbert_end`, `Unifier/Hilbert.lean`, line 144

```lean
theorem hilbert_end (k : ℕ) : hilbertH k (4 ^ k - 1) = (2 ^ k - 1, 0)
```

```text
'Unifier.hilbert_end' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T20 and T21, the Unifier and its cost

`Unifier.unifier_exists`, `Unifier/Factorization.lean`, line 34

```lean
theorem unifier_exists {X : Type u} {Y : Type v} (f : X → Y) :
    Nonempty (Factorization f)
```

```text
'Unifier.unifier_exists' depends on axioms: [Quot.sound]
```

`Unifier.unifier_unique_factorization`, `Unifier/Factorization.lean`, line 141

```lean
theorem unifier_unique_factorization {X : Type u} {Y : Type v}
    {f : X → Y} (F G : Factorization f) :
    ∃! p : (F.Q ≃ G.Q) × (F.K ≃ G.K),
      FactorIsomorphism F G p.1 p.2
```

```text
'Unifier.unifier_unique_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.trit_cost_factorization`, `Unifier/Cost.lean`, line 44

```lean
theorem trit_cost_factorization {X : Type u} {Y : Type v}
    (f : X → Y) [Fintype (Set.range f)]
    (hpos : 0 < Fintype.card (Set.range f)) :
    ∃ (dec : X → (Fin (tritCost f) → Fin 3))
      (enc : (Fin (tritCost f) → Fin 3) → Y),
      ∀ x, f x = enc (dec x)
```

```text
'Unifier.trit_cost_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.trit_cost_minimal`, `Unifier/Cost.lean`, line 64

```lean
theorem trit_cost_minimal {X : Type u} {Y : Type v}
    (f : X → Y) [Fintype (Set.range f)] (L : ℕ)
    (dec : X → (Fin L → Fin 3))
    (enc : (Fin L → Fin 3) → Y)
    (h : ∀ x, f x = enc (dec x)) :
    tritCost f ≤ L
```

```text
'Unifier.trit_cost_minimal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.independent_product_tritCost`, `Unifier/Cost.lean`, line 161

```lean
theorem independent_product_tritCost
    {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type w'}
    (f₁ : X₁ → Y₁) (f₂ : X₂ → Y₂)
    [Fintype (Set.range f₁)] [Fintype (Set.range f₂)]
    [Fintype (Set.range (Prod.map f₁ f₂))]
    (h₁ : 0 < Fintype.card (Set.range f₁))
    (h₂ : 0 < Fintype.card (Set.range f₂)) :
    tritCost (Prod.map f₁ f₂) ≤ tritCost f₁ + tritCost f₂ ∧
    tritCost f₁ + tritCost f₂ ≤ tritCost (Prod.map f₁ f₂) + 1
```

```text
'Unifier.independent_product_tritCost' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.correlated_pairing_counterexample`, `Unifier/Cost.lean`, line 177

```lean
theorem correlated_pairing_counterexample :
    tritCost (fun x : Fin 9 => x) = 2 ∧
    tritCost (fun x : Fin 9 => (x, x)) = 2 ∧
    ¬ (tritCost (fun x : Fin 9 => x) + tritCost (fun x : Fin 9 => x) ≤
        tritCost (fun x : Fin 9 => (x, x)) + 1)
```

```text
'Unifier.correlated_pairing_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T22 to T25, straight segments and closed curves

`Unifier.straight_lyapunov`, `Unifier/Straight.lean`, line 33

```lean
theorem straight_lyapunov (n t : ℕ) (hn : 2 ≤ n)
    (ht : 0 < t) (x y : ℝ) (hxy : x ≠ y) :
    (1 / (t : ℝ)) *
      Real.log (|(straightStep n)^[t] x -
        (straightStep n)^[t] y| / |x - y|) =
      Real.log (n : ℝ)
```

```text
'Unifier.straight_lyapunov' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.straight_scale_unstable`, `Unifier/Straight.lean`, line 51

```lean
theorem straight_scale_unstable (n : ℕ) (hn : 2 ≤ n)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℝ, ∃ t : ℕ,
      |x - y| < ε ∧
      1 ≤ |(straightStep n)^[t] x - (straightStep n)^[t] y|
```

```text
'Unifier.straight_scale_unstable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.dial_reader_idempotent`, `Unifier/Rounding.lean`, line 76

```lean
theorem dial_reader_idempotent (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    dialReader n (dialReader n θ) = dialReader n θ
```

```text
'Unifier.dial_reader_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.dial_reader_tolerance`, `Unifier/Rounding.lean`, line 81

```lean
theorem dial_reader_tolerance (n : ℕ) (hn : 0 < n)
    (a : ℤ) (θ : ℝ)
    (h : |θ - (a : ℝ) / n| < 1 / (2 * n)) :
    dialReader n θ = (a : ℝ) / n
```

```text
'Unifier.dial_reader_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.integer_orbit_injective`, `Unifier/Dynamics.lean`, line 10

```lean
theorem integer_orbit_injective (x : ℤ) :
    Function.Injective (fun t : ℕ => x + (t : ℤ))
```

```text
'Unifier.integer_orbit_injective' depends on axioms: [propext]
```

`Unifier.modular_step_period`, `Unifier/Dynamics.lean`, line 77

```lean
theorem modular_step_period (n : ℕ) [NeZero n] (x : ZMod n) :
    (fun z : ZMod n => z + 1)^[n] x = x
```

```text
'Unifier.modular_step_period' depends on axioms: [propext, Quot.sound]
```

`Unifier.dial_curvature_relation`, `Unifier/Curvature.lean`, line 27

```lean
theorem dial_curvature_relation (n : ℕ) (hn : 0 < n) :
    dialTolerance n = dialCurvature n / (4 * Real.pi)
```

```text
'Unifier.dial_curvature_relation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.dial_tolerance_straight_limit`, `Unifier/Curvature.lean`, line 41

```lean
theorem dial_tolerance_straight_limit :
    Filter.Tendsto (fun n : ℕ => dialTolerance n)
      Filter.atTop (nhds (0 : ℝ))
```

```text
'Unifier.dial_tolerance_straight_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### C1 to C5, the special cases

`Unifier.fibonacci_accumulation`, `Unifier/Fibonacci.lean`, line 33

```lean
theorem fibonacci_accumulation (m n : ℕ) :
    (fibonacciStep m)^[n] (0, 1) =
      ((Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m))
```

```text
'Unifier.fibonacci_accumulation' depends on axioms: [propext, Quot.sound]
```

`Unifier.segmented_log_two`, `Unifier/SegmentedLog.lean`, line 9

```lean
theorem segmented_log_two (x : ℝ) (e : ℤ)
    (hx : 0 < x)
    (hlo : (2 : ℝ) ^ e ≤ x)
    (hhi : x < (2 : ℝ) ^ (e + 1)) :
    Real.logb 2 x = (e : ℝ) + Real.logb 2 (x / (2 : ℝ) ^ e) ∧
      (1 : ℝ) ≤ x / (2 : ℝ) ^ e ∧
      x / (2 : ℝ) ^ e < 2
```

```text
'Unifier.segmented_log_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.sqrt_ne_half_integer`, `Unifier/Special.lean`, line 29

```lean
theorem sqrt_ne_half_integer (n : ℕ) (k : ℤ) : Real.sqrt n ≠ (k : ℝ) + 1 / 2
```

```text
'Unifier.sqrt_ne_half_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.binary_full_adder`, `Unifier/Carry.lean`, line 186

```lean
theorem binary_full_adder (a b r : Bool) :
    a.toNat + b.toNat + r.toNat =
      ((a.xor b).xor r).toNat +
        2 * (response (bitWindow a b) r).toNat
```

```text
'Unifier.binary_full_adder' does not depend on any axioms
```

`Unifier.binary_block_carry`, `Unifier/Carry.lean`, line 200

```lean
theorem binary_block_carry (ps : List (Bool × Bool)) (r : Bool) :
    blockCarry ps r = response (blockWindow ps) r
```

```text
'Unifier.binary_block_carry' depends on axioms: [propext]
```

`Unifier.rippleCarry_eq_blockCarry`, `Unifier/Carry.lean`, line 298

```lean
theorem rippleCarry_eq_blockCarry (ps : List (Bool × Bool)) (r : Bool) :
    rippleCarry ps r = blockCarry ps.reverse r ∧
    rippleCarry ps r = response (blockWindow ps.reverse) r
```

```text
'Unifier.rippleCarry_eq_blockCarry' depends on axioms: [propext]
```

`Unifier.rippleSum_getD`, `Unifier/Carry.lean`, line 348

```lean
theorem rippleSum_getD (ps : List (Bool × Bool)) (r : Bool) (i : ℕ) (hi : i < ps.length) :
    (rippleSum ps r).getD i false =
      (((ps.getD i (false, false)).1.xor (ps.getD i (false, false)).2).xor
        (rippleCarry (ps.take i) r))
```

```text
'Unifier.rippleSum_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.binary_word_adder_digits`, `Unifier/Carry.lean`, line 365

```lean
theorem binary_word_adder_digits (ps : List (Bool × Bool)) (r : Bool) :
    (bitsValue (ps.map Prod.fst) + bitsValue (ps.map Prod.snd) + r.toNat) % 2 ^ ps.length =
        bitsValue (rippleSum ps r) ∧
    (bitsValue (ps.map Prod.fst) + bitsValue (ps.map Prod.snd) + r.toNat) / 2 ^ ps.length =
        (rippleCarry ps r).toNat
```

```text
'Unifier.binary_word_adder_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Unifier.bitWindow_trit`, `Unifier/Carry.lean`, line 252

```lean
theorem bitWindow_trit (a b : Bool) :
    windowTrit (bitWindow a b) = a.toNat + b.toNat
```

```text
'Unifier.bitWindow_trit' does not depend on any axioms
```
