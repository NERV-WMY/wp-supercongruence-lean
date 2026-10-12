import WPFieldAssembly.ActualFiniteEntropyCarry
import WPActualEvenLogCarry

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoLegendreField WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry

namespace WPFieldAssembly.ActualEntropyPolynomial

set_option maxHeartbeats 1000000

/-- The whole literal even logarithm, in the squared variable. -/
noncomputable def movingEvenQ (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun j => if j = 0 then 0 else 1 / ((2 * j : ℕ) : ℚ))

/-- The original binomial entropy coefficients; the top half coefficient is retained. -/
noncomputable def entropySumQ (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun j => if j = 0 then 0 else entropyCoefficientQ p j)

noncomputable def entropyPowerQ (p : ℕ) : ℚ[X] :=
  C (1 / (2 * (p : ℚ))) * (2 - (1 - X)^p - (1 + X)^p)

theorem entropyPowerQ_origin (p : ℕ) : (entropyPowerQ p).coeff 0 = 0 := by
  simp [entropyPowerQ, coeff_sub,
    WPActualEvenLogCarry.coeff_one_sub_X_pow, coeff_one_add_X_pow]
  norm_num

theorem entropyPowerQ_coeff_even (p j : ℕ) [Fact p.Prime] (hj : 0 < j) :
    (entropyPowerQ p).coeff (2 * j) = entropyCoefficientQ p j := by
  have hj0 : 2 * j ≠ 0 := by omega
  have hz : (2 : ℚ[X]).coeff (2 * j) = 0 := by
    change (C (2 : ℚ)).coeff (2*j) = 0
    rw [coeff_C, if_neg hj0]
  have hs : (-1 : ℚ)^(2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [entropyPowerQ, coeff_C_mul, coeff_sub, coeff_sub,
    WPActualEvenLogCarry.coeff_one_sub_X_pow, coeff_one_add_X_pow, hz, hs]
  unfold entropyCoefficientQ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hp0]
  ring

theorem entropyPowerQ_even (p : ℕ) :
    (entropyPowerQ p).comp (-X) = entropyPowerQ p := by
  simp only [entropyPowerQ, mul_comp, C_comp, sub_comp, ofNat_comp,
    pow_comp, one_comp, X_comp, sub_neg_eq_add, add_comp]
  ring

theorem entropySum_eq_contract (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    entropySumQ p = contract 2 (entropyPowerQ p) := by
  ext j
  rw [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), entropySumQ,
    rankCoefficientPolynomial_coeff]
  by_cases h0 : j = 0
  · subst j
    simp [entropyPowerQ_origin]
  · rw [Nat.mul_comm j 2, entropyPowerQ_coeff_even p j (by omega)]
    by_cases hj : j < (p - 1) / 2 + 1
    · rw [if_pos hj, if_neg h0]
    · rw [if_neg hj]
      have hn := WPActualEvenLogCarry.prime_half_identity p (by omega : 7 ≤ p)
      have ht : p < 2 * j := by omega
      simp [entropyCoefficientQ, Nat.choose_eq_zero_of_lt ht]

private theorem rational_even_expand_contract (P : ℚ[X]) (hP : P.comp (-X) = P) :
    expand ℚ 2 (contract 2 P) = P := by
  ext j
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hj : 2 ∣ j
  · rw [if_pos hj, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hj]
  · rw [if_neg hj]
    have hm : j % 2 = 1 := by
      have ht := Nat.mod_lt j (by norm_num : 0 < (2 : ℕ))
      have hz : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hj
      omega
    have ho : Odd j := ⟨j / 2, by have hh := Nat.mod_add_div j 2; omega⟩
    have hc := congrArg (fun Q : ℚ[X] => Q.coeff j) hP
    rw [WPActualEvenLogCarry.coeff_comp_neg, ho.neg_one_pow] at hc
    linarith

theorem actual_entropy_square_pullback (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (entropySumQ p).comp (X^2) = entropyPowerQ p := by
  rw [entropySum_eq_contract p hp, ← expand_eq_comp_X_pow]
  exact rational_even_expand_contract _ (entropyPowerQ_even p)

/-- The binomial sum is the actual rational entropy, not a field replacement. -/
theorem actual_entropy_powers (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (z : ℚ) :
    (entropySumQ p).eval (z^2) =
      (2 - (1 - z)^p - (1 + z)^p) / (2 * (p : ℚ)) := by
  have h := congrArg (fun P : ℚ[X] => P.eval z) (actual_entropy_square_pullback p hp)
  simp only [eval_comp, eval_pow, eval_X, entropyPowerQ, eval_mul, eval_C,
    eval_sub, eval_ofNat, eval_one, eval_add] at h
  rw [h]
  ring

noncomputable def movingEvenIntegral (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun j => if j = 0 then 0 else smallIntegralInverse p (2 * j))

noncomputable def entropyCarryIntegral (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun j => if j = 0 then 0 else entropyCoefficientCarryIntegral p j)

noncomputable def entropyIntegral (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  movingEvenIntegral p - C (p : integralRationals p) * entropyCarryIntegral p

noncomputable def harmonicEvenField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun j => if j = 0 then 0 else
      (∑ k ∈ Finset.range (2 * j - 1), ((k + 1 : ℕ) : ZMod p)⁻¹) /
        ((2 * j : ℕ) : ZMod p))

private theorem half_index_unit (p j : ℕ) [Fact p.Prime] (hj : j ≤ (p - 1) / 2) :
    2 * j < p := by
  have hp0 := (Fact.out : p.Prime).pos
  have hn := Nat.div_mul_le_self (p - 1) 2
  omega

theorem movingEvenIntegral_value (p : ℕ) [Fact p.Prime] :
    (movingEvenIntegral p).map (integralRationals p).subtype = movingEvenQ p := by
  ext j
  rw [coeff_map, movingEvenIntegral, movingEvenQ,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  by_cases hj : j ≤ (p - 1) / 2
  · simp only [if_pos (by omega : j < (p - 1) / 2 + 1)]
    by_cases h0 : j = 0
    · simp only [if_pos h0, map_zero]
    · simp only [if_neg h0, Subring.subtype_apply]
      exact smallIntegralInverse_value p (2 * j) (by omega) (half_index_unit p j hj)
  · simp only [if_neg (by omega : ¬ j < (p - 1) / 2 + 1), map_zero]

theorem entropyCarryIntegral_field (p : ℕ) [Fact p.Prime] :
    (entropyCarryIntegral p).map (residueHom p) = harmonicEvenField p := by
  ext j
  rw [coeff_map, entropyCarryIntegral, harmonicEvenField,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  by_cases hj : j ≤ (p - 1) / 2
  · simp only [if_pos (by omega : j < (p - 1) / 2 + 1)]
    by_cases h0 : j = 0
    · simp only [if_pos h0, map_zero]
    · simp only [if_neg h0]
      exact entropyCoefficientCarryIntegral_field p j (by omega) (half_index_unit p j hj)
  · simp only [if_neg (by omega : ¬ j < (p - 1) / 2 + 1), map_zero]

/-- Whole polynomial p-division is attached to the literal entropy, coefficient by coefficient. -/
theorem actual_entropy_polynomial_lift (p : ℕ) [Fact p.Prime] :
    movingEvenQ p - entropySumQ p =
      C (p : ℚ) * (entropyCarryIntegral p).map (integralRationals p).subtype := by
  ext j
  rw [coeff_sub, coeff_C_mul, coeff_map, movingEvenQ, entropySumQ, entropyCarryIntegral,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff,
    rankCoefficientPolynomial_coeff]
  by_cases hj : j ≤ (p - 1) / 2
  · simp only [if_pos (by omega : j < (p - 1) / 2 + 1)]
    by_cases h0 : j = 0
    · simp only [if_pos h0, map_zero]
      ring
    · simp only [if_neg h0, Subring.subtype_apply]
      rw [entropyCoefficientCarryIntegral_value p j (by omega)
        (half_index_unit p j hj)]
      unfold entropyCoefficientCarryQ
      field_simp [show (p : ℚ) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero]
  · simp only [if_neg (by omega : ¬ j < (p - 1) / 2 + 1), map_zero]
    ring

theorem entropyIntegral_value (p : ℕ) [Fact p.Prime] :
    (entropyIntegral p).map (integralRationals p).subtype = entropySumQ p := by
  rw [entropyIntegral, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    map_natCast, movingEvenIntegral_value]
  linear_combination actual_entropy_polynomial_lift p

/-- The complete top-inclusive entropy carry is reduced only after its Q division. -/
theorem actual_entropy_evaluation_carry (p : ℕ) [Fact p.Prime]
    (z : integralRationals p) :
    (movingEvenQ p).eval z.val - (entropySumQ p).eval z.val =
      (p : ℚ) * ((entropyCarryIntegral p).eval z).val := by
  have h := congrArg (fun P : ℚ[X] => P.eval z.val) (actual_entropy_polynomial_lift p)
  rw [eval_sub, eval_mul, eval_C] at h
  change (movingEvenQ p).eval z.val - (entropySumQ p).eval z.val =
    (p : ℚ) * ((entropyCarryIntegral p).map (integralRationals p).subtype).eval
      ((integralRationals p).subtype z) at h
  rw [eval_map_apply] at h
  exact h

theorem actual_entropy_evaluation_field (p : ℕ) [Fact p.Prime]
    (z : integralRationals p) :
    residueHom p ((entropyCarryIntegral p).eval z) =
      (harmonicEvenField p).eval (residueHom p z) := by
  rw [← eval_map_apply, entropyCarryIntegral_field]

end WPFieldAssembly.ActualEntropyPolynomial
