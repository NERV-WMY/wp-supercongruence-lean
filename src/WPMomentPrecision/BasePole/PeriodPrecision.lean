import WPMomentPrecision.BasePole.WeightAttachment
import WPMomentPrecision.BasePole.EndpointQuotient
import WPMomentPrecision.BasePole.CarryResonances
import WPMomentPrecision.BasePole.Baselines
import WPMomentPrecision.BasePole.UnitTaylor

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeMomentIntegrality

namespace WPMomentPrecision.BasePole

/-- The two retained precision predicates have exactly the same valuation definition. -/
theorem precision_sub_zero (p k : ℕ) (a b : ℚ) :
    WPReview.RationalCongruent p k a b ↔ WPReview.RationalCongruent p k (a-b) 0 := by
  change WPGammaArithmetic.RationalCongruent p k a b ↔
    WPGammaArithmetic.RationalCongruent p k (a-b) 0
  exact WPGammaArithmetic.rationalCongruent_iff_sub_zero p k a b

theorem precision_zero_add (p k : ℕ) (hp : p.Prime) (a b : ℚ)
    (ha : WPReview.RationalCongruent p k a 0)
    (hb : WPReview.RationalCongruent p k b 0) :
    WPReview.RationalCongruent p k (a+b) 0 := by
  change WPGammaArithmetic.RationalCongruent p k a 0 at ha
  change WPGammaArithmetic.RationalCongruent p k b 0 at hb
  change WPGammaArithmetic.RationalCongruent p k (a+b) 0
  exact WPGammaArithmetic.rationalCongruent_zero_add p k hp a b ha hb

theorem degree_mul_bound (P Q : ℤ[X]) (a b : ℕ)
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b) :
    (P * Q).natDegree ≤ a + b :=
  natDegree_mul_le.trans (Nat.add_le_add hP hQ)

theorem degree_C_mul_bound (a : ℤ) (P : ℤ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d) : (C a * P).natDegree ≤ d := by
  simpa only [natDegree_C, zero_add] using
    (natDegree_mul_le (p := C a) (q := P)).trans (Nat.add_le_add le_rfl hP)

theorem degree_add_bound (P Q : ℤ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) : (P + Q).natDegree ≤ d :=
  (natDegree_add_le _ _).trans (max_le hP hQ)

theorem frobeniusF_degree (p : ℕ) : (frobeniusF p : ℤ[X]).natDegree ≤ p := by
  unfold frobeniusF
  exact (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))

theorem frobeniusG_degree (p : ℕ) : (frobeniusG p : ℤ[X]).natDegree ≤ p := by
  unfold frobeniusG
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simpa only [natDegree_C, natDegree_X_pow, zero_add] using
      (natDegree_mul_le (p := C ((4 : ℤ) ^ p)) (q := X ^ p))
  · simp

theorem endpointGeometric_degree {K : Type*} [CommRing K] (p : ℕ) :
    (endpointGeometric p : K[X]).natDegree ≤ p - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [endpointGeometric_coefficient, if_neg (by omega : ¬j < p)]

theorem endpointFCarryQuotient_degree (p : ℕ) :
    (endpointFCarryQuotient p).natDegree ≤ p - 1 := by
  rw [endpointFCarryQuotient, natDegree_neg,
    natDegree_divByMonic _ (monic_X_sub_C 4)]
  exact (Nat.sub_le _ _).trans (binomialInterior_degree p (-1) 4)

noncomputable def baseUncarriedNumerator (p : ℕ) : ℤ[X] :=
  frobeniusF p ^ 2 * frobeniusG p

noncomputable def baseCubicRemainder (p : ℕ) : ℤ[X] :=
  firstFCarry p ^ 2 * firstGCarry p

noncomputable def endpointUncarriedNumerator (p : ℕ) : ℤ[X] :=
  endpointGeometric p * frobeniusF p * frobeniusG p

noncomputable def endpointCubicRemainder (p : ℕ) : ℤ[X] :=
  endpointFCarryQuotient p * firstFCarry p * firstGCarry p

theorem baseUncarriedNumerator_degree (p : ℕ) :
    (baseUncarriedNumerator p).natDegree ≤ 3*p := by
  have hf := natDegree_pow_le_of_le 2 (frobeniusF_degree p)
  have h := degree_mul_bound _ _ (2*p) p hf (frobeniusG_degree p)
  simpa only [baseUncarriedNumerator, show 2*p+p=3*p by omega] using h

theorem baseCubicRemainder_degree (p : ℕ) :
    (baseCubicRemainder p).natDegree ≤ 3*p := by
  have hf := natDegree_pow_le_of_le 2 (binomialInterior_degree (K := ℤ) p (-1) 4)
  have h := degree_mul_bound _ _ (2*(p-1)) (p-1) hf
    (binomialInterior_degree (K := ℤ) p 4 (-1))
  exact h.trans (by omega)

theorem baseSecondCarry_degree (p : ℕ) :
    (baseSecondCarry p : ℤ[X]).natDegree ≤ 3*p := by
  have hf : (firstFCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p (-1) 4
  have hg : (firstGCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p 4 (-1)
  have hs := degree_mul_bound _ _ (2*(p-1)) p
    (natDegree_pow_le_of_le 2 hf) (frobeniusG_degree p)
  have ht := degree_mul_bound _ _ (p+(p-1)) (p-1)
    (degree_mul_bound _ _ p (p-1) (frobeniusF_degree p) hf) hg
  unfold baseSecondCarry
  apply degree_add_bound _ _ (3*p) (hs.trans (by omega))
  change (C (2 : ℤ) * frobeniusF p * firstFCarry p * firstGCarry p).natDegree ≤ 3*p
  have he : (C (2 : ℤ) * frobeniusF p * firstFCarry p * firstGCarry p : ℤ[X]) =
      C 2 * (frobeniusF p * firstFCarry p * firstGCarry p) := by ring
  rw [he]
  exact degree_C_mul_bound 2 _ _ (ht.trans (by omega))

theorem endpointUncarriedNumerator_degree (p : ℕ) :
    (endpointUncarriedNumerator p).natDegree ≤ 3*p := by
  have h := degree_mul_bound _ _ ((p-1)+p) p
    (degree_mul_bound _ _ (p-1) p (endpointGeometric_degree p) (frobeniusF_degree p))
    (frobeniusG_degree p)
  exact h.trans (by omega)

theorem endpointSecondCarry_degree (p : ℕ) :
    (endpointSecondCarry p).natDegree ≤ 3*p := by
  have hf : (firstFCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p (-1) 4
  have hg : (firstGCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p 4 (-1)
  have hs := degree_mul_bound _ _ ((p-1)+(p-1)) p
    (degree_mul_bound _ _ (p-1) (p-1) (endpointFCarryQuotient_degree p) hf)
    (frobeniusG_degree p)
  have ht := degree_mul_bound _ _ ((p-1)+(p-1)) (p-1)
    (degree_mul_bound _ _ (p-1) (p-1) (endpointGeometric_degree p) hf) hg
  unfold endpointSecondCarry
  apply degree_add_bound _ _ (3*p) (hs.trans (by omega))
  have he : (2 * endpointGeometric p * firstFCarry p * firstGCarry p : ℤ[X]) =
      C 2 * (endpointGeometric p * firstFCarry p * firstGCarry p) := by
    rw [C_ofNat]
    ring
  rw [he]
  exact degree_C_mul_bound 2 _ _ (ht.trans (by omega))

theorem endpointCubicRemainder_degree (p : ℕ) :
    (endpointCubicRemainder p).natDegree ≤ 3*p := by
  have h := degree_mul_bound _ _ ((p-1)+(p-1)) (p-1)
    (degree_mul_bound _ _ (p-1) (p-1) (endpointFCarryQuotient_degree p)
      (binomialInterior_degree (K := ℤ) p (-1) 4))
    (binomialInterior_degree (K := ℤ) p 4 (-1))
  exact h.trans (by omega)

/-- No first, second, or third carry is deleted before applying the actual primitive. -/
theorem actual_baseMoment_exact_carries (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualMomentDefect.baseMoment p =
      (numeratorPeriod p (baseUncarriedNumerator p) +
        (p : ℚ) * numeratorPeriod p (baseFirstCarry p) +
        (p : ℚ)^2 * numeratorPeriod p (baseSecondCarry p) +
        (p : ℚ)^3 * numeratorPeriod p (baseCubicRemainder p)) / 9 := by
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [actual_baseMoment_numerator p (by omega)]
  unfold baseNumerator integerF integerG
  rw [actual_base_three_carry_source p ho]
  rw [show (C ((p : ℤ)^3)*firstFCarry p^2*firstGCarry p : ℤ[X]) =
    C ((p : ℤ)^3)*(firstFCarry p^2*firstGCarry p) by rw [mul_assoc]]
  simp only [numeratorPeriod_add, numeratorPeriod_C_mul, Int.cast_natCast, Int.cast_pow]
  rfl

/-- The canceled actual endpoint numerator has an integral entire three-carry expansion. -/
theorem actual_endpointFPeriod_exact_carries (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    endpointFPeriod p = 16 *
      (numeratorPeriod p (endpointUncarriedNumerator p) +
        (p : ℚ) * numeratorPeriod p (endpointFirstCarry p) +
        (p : ℚ)^2 * numeratorPeriod p (endpointSecondCarry p) +
        (p : ℚ)^3 * numeratorPeriod p (endpointCubicRemainder p)) := by
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [actual_endpointFPeriod_numerator p (by omega)]
  unfold endpointNumerator integerF integerG
  rw [actual_endpoint_three_carry_source p ho]
  rw [show (C ((p : ℤ)^3)*endpointFCarryQuotient p*firstFCarry p*firstGCarry p : ℤ[X]) =
    C ((p : ℤ)^3)*(endpointFCarryQuotient p*firstFCarry p*firstGCarry p) by ring]
  simp only [numeratorPeriod_add, numeratorPeriod_C_mul, Int.cast_natCast, Int.cast_pow]
  rfl

theorem integral_prime_power_precision (p k : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : 0 ≤ padicValRat p q) :
    WPReview.RationalCongruent p k ((p : ℚ)^k * q) 0 := by
  by_cases hz : q = 0
  · exact Or.inl (by simp [hz])
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply Or.inr
  rw [sub_zero, padicValRat.mul (pow_ne_zero k hpq) hz, padicValRat.pow,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  omega

theorem precision_prime_power_mul_integral (p k l : ℕ) [Fact p.Prime]
    (c q : ℚ) (hc : 0 ≤ padicValRat p c)
    (hq : WPReview.RationalCongruent p k q 0) :
    WPReview.RationalCongruent p (k+l) ((p : ℚ)^l * c * q) 0 := by
  rcases hq with hq | hq
  · exact Or.inl (by simp [hq])
  by_cases hc0 : c = 0
  · exact Or.inl (by simp [hc0])
  by_cases hq0 : q = 0
  · exact Or.inl (by simp [hq0])
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply Or.inr
  rw [sub_zero, padicValRat.mul (mul_ne_zero (pow_ne_zero l hpq) hc0) hq0,
    padicValRat.mul (pow_ne_zero l hpq) hc0, padicValRat.pow,
    padicValRat.self (Fact.out : p.Prime).one_lt]
  simp only [sub_zero] at hq
  push_cast
  omega

theorem base_normalizer_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (1 / (9 * (125 : ℚ)^p)) := by
  change 1 / (9 * (125 : ℚ)^p) ∈ integralRationals p
  have h3 := WPFiniteConductorPolynomial.small_inverse_integral p 3 (by omega) (by omega)
  have h125 := WPHasseIntegralTransport.one_over_125_integral p (by omega)
  have h := (integralRationals p).mul_mem
    ((integralRationals p).pow_mem h3 2) ((integralRationals p).pow_mem h125 p)
  convert h using 1
  norm_num [one_div, inv_pow, mul_inv_rev]
  rw [← inv_pow, show (125 : ℚ)⁻¹ = (1/125 : ℚ) by norm_num]
  ring

/-- The complete first carry gains its missing digit only after its actual unit contraction. -/
theorem actual_base_first_carry_mod_cube (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      ((p : ℚ) * numeratorPeriod p (baseFirstCarry p) / 9) 0 := by
  rw [actual_baseFirstCarry_period_attachment]
  have h := precision_prime_power_mul_integral p 1 2
    (1 / (9 * (125 : ℚ)^p)) (actualFirstCarryUnitSum p)
    (base_normalizer_integral p hp) (actualFirstCarryUnitSum_first_digit p hp)
  convert h using 1
  ring

/-- The third carry is p-integral with the original support, so its p^3 factor is sufficient. -/
theorem actual_base_cubic_remainder_mod_cube (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      ((p : ℚ)^3 * numeratorPeriod p (baseCubicRemainder p) / 9) 0 := by
  have h3 := WPFiniteConductorPolynomial.small_inverse_integral p 3 (by omega) (by omega)
  have h9 : (1 / 9 : ℚ) ∈ integralRationals p := by
    simpa only [Nat.cast_ofNat, show (1 / 3 : ℚ)^2 = 1/9 by norm_num] using
      (integralRationals p).pow_mem h3 2
  have hq := (integralRationals p).mul_mem
    (numeratorPeriod_integral p hp _ (baseCubicRemainder_degree p)) h9
  convert integral_prime_power_precision p 3
    (numeratorPeriod p (baseCubicRemainder p) * (1/9)) hq using 1
  ring

/-- The actual base modulo p^3 keeps the complete uncarried row and both second resonances. -/
theorem actual_baseMoment_second_carry_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPActualMomentDefect.baseMoment p)
      ((numeratorPeriod p (baseUncarriedNumerator p) +
        (p : ℚ)^2 * numeratorPeriod p (baseSecondCarry p)) / 9) := by
  apply (precision_sub_zero p 3 _ _).mpr
  rw [actual_baseMoment_exact_carries p hp]
  rw [show
    (numeratorPeriod p (baseUncarriedNumerator p) +
      (p : ℚ) * numeratorPeriod p (baseFirstCarry p) +
      (p : ℚ)^2 * numeratorPeriod p (baseSecondCarry p) +
      (p : ℚ)^3 * numeratorPeriod p (baseCubicRemainder p)) / 9 -
    (numeratorPeriod p (baseUncarriedNumerator p) +
      (p : ℚ)^2 * numeratorPeriod p (baseSecondCarry p)) / 9 =
      (p : ℚ) * numeratorPeriod p (baseFirstCarry p) / 9 +
      (p : ℚ)^3 * numeratorPeriod p (baseCubicRemainder p) / 9 by ring]
  exact precision_zero_add p 3 (Fact.out : p.Prime) _ _
    (actual_base_first_carry_mod_cube p hp) (actual_base_cubic_remainder_mod_cube p hp)

/-- The actual endpoint quotient's second and third rows are retained and then bounded. -/
theorem actual_endpointFPeriod_first_carry_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (endpointFPeriod p)
      (16 * (numeratorPeriod p (endpointUncarriedNumerator p) +
        (p : ℚ) * numeratorPeriod p (endpointFirstCarry p))) := by
  have h2 := integral_prime_power_precision p 2
    (16 * numeratorPeriod p (endpointSecondCarry p))
    ((integralRationals p).mul_mem (natCast_mem _ 16)
      (numeratorPeriod_integral p hp _ (endpointSecondCarry_degree p)))
  have h3 := integral_prime_power_precision p 2
    ((p : ℚ) * 16 * numeratorPeriod p (endpointCubicRemainder p))
    ((integralRationals p).mul_mem
      ((integralRationals p).mul_mem (natCast_mem _ p) (natCast_mem _ 16))
      (numeratorPeriod_integral p hp _ (endpointCubicRemainder_degree p)))
  apply (precision_sub_zero p 2 _ _).mpr
  rw [actual_endpointFPeriod_exact_carries p hp]
  convert precision_zero_add p 2 (Fact.out : p.Prime) _ _ h2 h3 using 1
  ring

theorem baseSecondCarry_degree_sharp (p : ℕ) (hp : 1 ≤ p) :
    (baseSecondCarry p : ℤ[X]).natDegree ≤ 3*p-2 := by
  have hf : (firstFCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p (-1) 4
  have hg : (firstGCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p 4 (-1)
  have hs := degree_mul_bound _ _ (2*(p-1)) p
    (natDegree_pow_le_of_le 2 hf) (frobeniusG_degree p)
  have ht := degree_mul_bound _ _ (p+(p-1)) (p-1)
    (degree_mul_bound _ _ p (p-1) (frobeniusF_degree p) hf) hg
  unfold baseSecondCarry
  apply degree_add_bound _ _ (3*p-2) (hs.trans (by omega))
  have he : (2 * frobeniusF p * firstFCarry p * firstGCarry p : ℤ[X]) =
      C 2 * (frobeniusF p * firstFCarry p * firstGCarry p) := by
    rw [C_ofNat]
    ring
  rw [he]
  exact degree_C_mul_bound 2 _ _ (ht.trans (by omega))

theorem baseSecondCarry_coefficient_zero (p : ℕ) :
    (baseSecondCarry p : ℤ[X]).coeff 0 = 0 := by
  have hf0 : (firstFCarry p : ℤ[X]).coeff 0 = 0 := by
    simp [firstFCarry, binomialInterior_coefficient]
  simp only [baseSecondCarry, pow_two, coeff_add, mul_coeff_zero, hf0,
    zero_mul, mul_zero, zero_add]

/-- Integer carry coefficients are cast after the complete polynomial operations. -/
theorem baseSecondCarry_integer_coefficient_cast (p n : ℕ) [Fact p.Prime] :
    ((baseSecondCarry p : ℤ[X]).coeff n : ZMod p) =
      (baseSecondCarry p : (ZMod p)[X]).coeff n := by
  have hf : (firstFCarry p : ℤ[X]).map (Int.castRingHom (ZMod p)) = firstFCarry p := by
    unfold firstFCarry
    rw [binomialInterior_map]
    simp only [map_neg, map_one, map_ofNat]
  have hg : (firstGCarry p : ℤ[X]).map (Int.castRingHom (ZMod p)) = firstGCarry p := by
    unfold firstGCarry
    rw [binomialInterior_map]
    simp only [map_neg, map_one, map_ofNat]
  have hs : (baseSecondCarry p : ℤ[X]).map (Int.castRingHom (ZMod p)) =
      (baseSecondCarry p : (ZMod p)[X]) := by
    unfold baseSecondCarry
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_ofNat, hf, hg]
    unfold frobeniusF frobeniusG
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, map_pow, map_ofNat]
  have he := congrArg (fun Q : (ZMod p)[X] ↦ Q.coeff n) hs
  simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using he

/-- The scalar 18 comes from both original signed endpoint weights. -/
theorem actual_baseSecondCarry_period_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (numeratorPeriod p (baseSecondCarry p) : ZMod p) =
      (18/125 : ZMod p) * WPFiniteInversion.R p 16 := by
  have h3 : (baseSecondCarry p : ℤ[X]).coeff (3*p) = 0 :=
    coeff_eq_zero_of_natDegree_lt
      ((baseSecondCarry_degree_sharp p (by omega)).trans_lt (by omega))
  rw [numeratorPeriod_two_resonance_residue p hp _ (baseSecondCarry_degree p)
    (baseSecondCarry_coefficient_zero p) h3,
    baseSecondCarry_integer_coefficient_cast, baseSecondCarry_integer_coefficient_cast]
  have h := actual_second_carry_resonances p hp
  rw [h.1, h.2]
  have htwo : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  have height : (8 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 htwo using 1
    norm_num
  have hfive : (5 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 5 (by omega) (by omega)
  have h125 : (125 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 hfive using 1
    norm_num
  field_simp [htwo, height, h125]
  ring

/-- The rational lift is the original full finite dilogarithm, with every denominator retained. -/
noncomputable def actualAlpha (p : ℕ) : ℚ :=
  ∑ r ∈ Finset.Ico 1 p, (16 : ℚ)^r / (r : ℚ)^2

theorem actualAlpha_term_integral (p r : ℕ) [Fact p.Prime]
    (hr : r ∈ Finset.Ico 1 p) :
    0 ≤ padicValRat p ((16 : ℚ)^r / (r : ℚ)^2) := by
  change (16 : ℚ)^r / (r : ℚ)^2 ∈ integralRationals p
  have hinv := WPFiniteConductorPolynomial.small_inverse_integral p r
    (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2
  have h := (integralRationals p).mul_mem
    ((integralRationals p).pow_mem (natCast_mem _ 16) r)
    ((integralRationals p).pow_mem hinv 2)
  simpa only [div_eq_mul_inv, one_div, inv_pow, one_mul, Nat.cast_ofNat] using h

theorem actualAlpha_integral (p : ℕ) [Fact p.Prime] :
    0 ≤ padicValRat p (actualAlpha p) := by
  change actualAlpha p ∈ integralRationals p
  exact (integralRationals p).sum_mem (fun r hr ↦ actualAlpha_term_integral p r hr)

theorem actualAlpha_residue (p : ℕ) [Fact p.Prime] :
    (actualAlpha p : ZMod p) = WPFiniteInversion.R p 16 := by
  rw [actualAlpha, cast_sum_integral p _ _ (fun r hr ↦ actualAlpha_term_integral p r hr)]
  unfold WPFiniteInversion.R
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
  have hn : (((((r : ℚ)^2).num : ℤ)) : ZMod p) ≠ 0 := by
    simpa only [Rat.num_pow, Rat.num_natCast, Int.cast_pow, Int.cast_natCast] using
      (pow_ne_zero 2 hr0)
  have hnum : 0 ≤ padicValRat p ((16 : ℚ)^r) := by
    change (16 : ℚ)^r ∈ integralRationals p
    simpa only [Nat.cast_ofNat] using
      (integralRationals p).pow_mem (natCast_mem (integralRationals p) 16) r
  rw [Rat.cast_div_of_ne_zero
    (integral_denominator_cast_ne_zero p ((16 : ℚ)^r) hnum) hn,
    Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]

theorem actual_baseSecondCarry_first_digit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (numeratorPeriod p (baseSecondCarry p))
      ((18/125 : ℚ) * actualAlpha p) := by
  have h125 := WPHasseIntegralTransport.one_over_125_integral p (by omega)
  have hc : 0 ≤ padicValRat p (18/125 : ℚ) := by
    change (18/125 : ℚ) ∈ integralRationals p
    simpa only [one_div, div_eq_mul_inv, one_mul, Nat.cast_ofNat] using
      (integralRationals p).mul_mem (natCast_mem _ 18) h125
  have hi := (integralRationals p).mul_mem hc (actualAlpha_integral p)
  apply (integral_residue_eq_iff p _ _
    (numeratorPeriod_integral p hp _ (baseSecondCarry_degree p)) hi).mp
  rw [actual_baseSecondCarry_period_residue p hp,
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hc)
      (integral_denominator_cast_ne_zero p _ (actualAlpha_integral p)), actualAlpha_residue]
  congr 1
  symm
  have hfive : (5 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 5 (by omega) (by omega)
  have h125c : (125 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 hfive using 1
    norm_num
  rw [Rat.cast_div_of_ne_zero (by norm_num : ((18 : ℚ).den : ZMod p) ≠ 0)
    (by norm_num; exact h125c),
    Rat.cast_ofNat, Rat.cast_ofNat]

/-- The actual p^3 base keeps the uncarried source and the literal alpha correction. -/
theorem actual_baseMoment_alpha_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPActualMomentDefect.baseMoment p)
      (numeratorPeriod p (baseUncarriedNumerator p) / 9 +
        (p : ℚ)^2 * (2/125) * actualAlpha p) := by
  apply precision_trans p 3 _ _ _ (actual_baseMoment_second_carry_precision p hp)
  have h3 := WPFiniteConductorPolynomial.small_inverse_integral p 3 (by omega) (by omega)
  have h9 : 0 ≤ padicValRat p (1/9 : ℚ) := by
    change (1/9 : ℚ) ∈ integralRationals p
    simpa only [Nat.cast_ofNat, show (1/3 : ℚ)^2=1/9 by norm_num] using
      (integralRationals p).pow_mem h3 2
  have hs := (precision_sub_zero p 1 _ _).mp
    (actual_baseSecondCarry_first_digit p hp)
  have h := precision_prime_power_mul_integral p 1 2 (1/9)
    (numeratorPeriod p (baseSecondCarry p) - (18/125)*actualAlpha p) h9 hs
  apply (precision_sub_zero p 3 _ _).mpr
  convert h using 1
  ring

/-- The actual uncarried numerator retains its four signed resonances. -/
theorem baseUncarriedNumerator_exact (p : ℕ) :
    baseUncarriedNumerator p =
      C (-((4 : ℤ)^p)^2) * X^(0*p) +
      C (((4 : ℤ)^p)^3+2*(4 : ℤ)^p) * X^(1*p) -
      C (2*((4 : ℤ)^p)^2+1) * X^(2*p) +
      C ((4 : ℤ)^p) * X^(3*p) := by
  unfold baseUncarriedNumerator frobeniusF frobeniusG
  simp only [map_neg, map_pow, map_add, map_mul, map_one, C_ofNat,
    zero_mul, one_mul, pow_zero, mul_one,
    show 2*p=p*2 by omega, show 3*p=p*3 by omega, pow_mul]
  ring

/-- The four original endpoint weights give S(2^p), before any Taylor expansion. -/
theorem actual_baseUncarried_period (p : ℕ) [Fact p.Prime] :
    numeratorPeriod p (baseUncarriedNumerator p) =
      baseBaseline ((2 : ℚ)^p) / (125 : ℚ)^p := by
  have hi (c : ℕ) : 2*((c*p : ℕ) : ℤ)-5*(p : ℤ) =
      (2*(c : ℤ)-5)*(p : ℤ) := by push_cast; ring
  have hf : (4 : ℚ)^p = ((2 : ℚ)^p)^2 := by
    rw [show (4 : ℚ)=(2 : ℚ)^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [baseUncarriedNumerator_exact]
  simp only [numeratorPeriod_add, numeratorPeriod_sub, numeratorPeriod_monomial,
    Int.cast_neg, Int.cast_pow, Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_ofNat]
  rw [hi 0, hi 1, hi 2, hi 3,
    primitiveWeight_lambda, primitiveWeight_lambda,
    primitiveWeight_lambda, primitiveWeight_lambda]
  simp only [hf]
  have hl : (2 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
  have h125 : (125 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
  unfold baseBaseline
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zpow_neg, zpow_natCast, zpow_one, Int.cast_neg, Int.cast_ofNat]
  field_simp [hl, h125]
  ring

/-- Actual SB3--SB6 precision, with S(2^p) and the original literal alpha lift. -/
theorem actual_baseMoment_baseline_alpha (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPActualMomentDefect.baseMoment p)
      (baseBaseline ((2 : ℚ)^p) / (9*(125 : ℚ)^p) +
        (p : ℚ)^2*(2/125)*actualAlpha p) := by
  have h := actual_baseMoment_alpha_precision p hp
  rw [actual_baseUncarried_period] at h
  convert h using 1
  ring

theorem actual_baseBaseline_mod_cube (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      (baseBaseline ((2 : ℚ)^p)/(9*(125 : ℚ)^p))
      (baseUnitTarget p (fermatQ p 2) (fermatQ p 5)) := by
  apply (precision_sub_zero p 3 _ _).mpr
  rw [actual_baseBaseline_exact_taylor p hp, add_sub_cancel_left]
  exact integral_prime_power_precision p 3 _ (actualBaseUnitRemainder_integral p hp)

/-- SB7 with the original integer Fermat quotients and literal alpha, for both prime classes. -/
theorem actual_baseMoment_SB7 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPActualMomentDefect.baseMoment p)
      ((24/625)*(1 + (p : ℚ)*((32/3)*fermatQ p 2-3*fermatQ p 5) +
        (p : ℚ)^2*((97/2)*(fermatQ p 2)^2 -
          32*fermatQ p 2*fermatQ p 5 + 6*(fermatQ p 5)^2 + (5/12)*actualAlpha p))) := by
  have hb := actual_baseBaseline_mod_cube p hp
  have hshift : WPReview.RationalCongruent p 3
      (baseBaseline ((2 : ℚ)^p)/(9*(125 : ℚ)^p)+(p : ℚ)^2*(2/125)*actualAlpha p)
      (baseUnitTarget p (fermatQ p 2) (fermatQ p 5)+(p : ℚ)^2*(2/125)*actualAlpha p) := by
    apply (precision_sub_zero p 3 _ _).mpr
    rw [show
      baseBaseline ((2 : ℚ)^p)/(9*(125 : ℚ)^p)+(p : ℚ)^2*(2/125)*actualAlpha p -
      (baseUnitTarget p (fermatQ p 2) (fermatQ p 5)+(p : ℚ)^2*(2/125)*actualAlpha p) =
      baseBaseline ((2 : ℚ)^p)/(9*(125 : ℚ)^p)-baseUnitTarget p (fermatQ p 2) (fermatQ p 5)
      by ring]
    exact (precision_sub_zero p 3 _ _).mp hb
  have h := precision_trans p 3 _ _ _ (actual_baseMoment_baseline_alpha p hp) hshift
  unfold baseUnitTarget at h
  convert h using 1
  ring

theorem actual_endpointBaseline_mod_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2
      (16*(fermatUnit p 2)^2*endpointBaseline ((2 : ℚ)^p)/(125 : ℚ)^p)
      (endpointUnitTarget p (fermatQ p 2) (fermatQ p 5)) := by
  apply (precision_sub_zero p 2 _ _).mpr
  rw [actual_endpointBaseline_exact_taylor p hp, add_sub_cancel_left]
  exact integral_prime_power_precision p 2 _ (actualEndpointUnitRemainder_integral p hp)

theorem actual_endpointUnit_mod_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (1+(fermatUnit p 2)⁻¹)
      (2-(p : ℚ)*fermatQ p 2) := by
  apply (precision_sub_zero p 2 _ _).mpr
  rw [actual_endpointUnit_exact_taylor p hp, add_sub_cancel_left]
  exact integral_prime_power_precision p 2 _ (actual_endpointUnit_remainder_integral p hp)

noncomputable def endpointResonantNumerator (p : ℕ) : ℤ[X] :=
  C (-((4 : ℤ)^(p-1)*(4 : ℤ)^p))*X^(0*p) +
    C ((4 : ℤ)^(p-1)*(((4 : ℤ)^p)^2+1))*X^(1*p) -
      C ((4 : ℤ)^(p-1)*(4 : ℤ)^p)*X^(2*p)

theorem endpointInterior_degree (p : ℕ) : (endpointInterior p).natDegree ≤ p-1 := by
  unfold endpointInterior
  exact (natDegree_sub_le _ _).trans
    (max_le (endpointGeometric_degree p) (by simp))

theorem endpointInterior_coefficient_zero (p : ℕ) [Fact p.Prime] :
    (endpointInterior p).coeff 0 = 0 := by
  rw [endpointInterior, coeff_sub, endpointGeometric_coefficient,
    if_pos (Fact.out : p.Prime).pos, coeff_C_zero]
  simp

/-- The geometric constant and every interior index are separated by an exact polynomial identity. -/
theorem endpointUncarriedNumerator_exact (p : ℕ) :
    endpointUncarriedNumerator p = endpointResonantNumerator p +
      C (-(4 : ℤ)^p)*(endpointInterior p*X^(0*p)) +
      C (((4 : ℤ)^p)^2+1)*(endpointInterior p*X^(1*p)) -
      C ((4 : ℤ)^p)*(endpointInterior p*X^(2*p)) := by
  unfold endpointUncarriedNumerator endpointResonantNumerator endpointInterior
    frobeniusF frobeniusG
  simp only [map_neg, map_mul, map_add, map_pow, map_one, C_ofNat,
    zero_mul, one_mul, pow_zero, mul_one, show 2*p=p*2 by omega, pow_mul]
  ring

theorem actual_endpointUncarried_period_attachment (p : ℕ) [Fact p.Prime] :
    numeratorPeriod p (endpointUncarriedNumerator p) =
      numeratorPeriod p (endpointResonantNumerator p) +
        (p : ℚ)/(125 : ℚ)^p*actualEndpointMainUnitSum p := by
  rw [endpointUncarriedNumerator_exact]
  simp only [numeratorPeriod_add, numeratorPeriod_sub, numeratorPeriod_C_mul]
  rw [numeratorPeriod_unit_block p _ 0 (endpointInterior_degree p)
      (endpointInterior_coefficient_zero p),
    numeratorPeriod_unit_block p _ 1 (endpointInterior_degree p)
      (endpointInterior_coefficient_zero p),
    numeratorPeriod_unit_block p _ 2 (endpointInterior_degree p)
      (endpointInterior_coefficient_zero p)]
  simp only [Int.cast_neg, Int.cast_pow, Int.cast_ofNat, Int.cast_add,
    Int.cast_one, actualEndpointMainUnitSum]
  ring

theorem actual_endpointResonant_period (p : ℕ) [Fact p.Prime] :
    numeratorPeriod p (endpointResonantNumerator p) =
      (fermatUnit p 2)^2*endpointBaseline ((2 : ℚ)^p)/(125 : ℚ)^p := by
  have hi (c : ℕ) : 2*((c*p : ℕ) : ℤ)-5*(p : ℤ) =
      (2*(c : ℤ)-5)*(p : ℤ) := by push_cast; ring
  have ha : (4 : ℚ)^p = ((2 : ℚ)^p)^2 := by
    rw [show (4 : ℚ)=(2 : ℚ)^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hb : (4 : ℚ)^(p-1) = (fermatUnit p 2)^2 := by
    unfold fermatUnit
    rw [show (4 : ℚ)=(2 : ℚ)^2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  unfold endpointResonantNumerator
  simp only [numeratorPeriod_add, numeratorPeriod_sub, numeratorPeriod_monomial,
    Int.cast_neg, Int.cast_pow, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_ofNat]
  rw [hi 0, hi 1, hi 2, primitiveWeight_lambda, primitiveWeight_lambda, primitiveWeight_lambda]
  simp only [ha, hb]
  have hl : (2 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
  have h125 : (125 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
  unfold endpointBaseline
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zpow_neg, zpow_natCast, zpow_one, Int.cast_neg, Int.cast_ofNat]
  field_simp [hl, h125]
  ring

/-- The actual endpoint main row has a p^2 error only after complete unit-band cancellation. -/
theorem actual_endpointUncarried_mod_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (16*numeratorPeriod p (endpointUncarriedNumerator p))
      (16*(fermatUnit p 2)^2*endpointBaseline ((2 : ℚ)^p)/(125 : ℚ)^p) := by
  have h125 := WPHasseIntegralTransport.one_over_125_integral p (by omega)
  have hc : 0 ≤ padicValRat p (16/(125 : ℚ)^p) := by
    change 16/(125 : ℚ)^p ∈ integralRationals p
    simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul, Nat.cast_ofNat] using
      (integralRationals p).mul_mem (natCast_mem _ 16)
        ((integralRationals p).pow_mem h125 p)
  have h := precision_prime_power_mul_integral p 1 1 (16/(125 : ℚ)^p)
    (actualEndpointMainUnitSum p) hc (actualEndpointMainUnitSum_first_digit p hp)
  apply (precision_sub_zero p 2 _ _).mpr
  rw [actual_endpointUncarried_period_attachment, actual_endpointResonant_period]
  convert h using 1
  ring

theorem endpointGeometric_field_coefficient (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) :
    (endpointGeometric p : (ZMod p)[X]).coeff r = geometricCoeff p r := by
  have h4 := four_field_ne_zero p (by omega)
  rw [endpointGeometric_coefficient, if_pos (Finset.mem_Ico.mp hr).2,
    pow_sub₀ (4 : ZMod p) h4 (by have h := (Finset.mem_Ico.mp hr).2; omega),
    ZMod.pow_card_sub_one_eq_one h4, one_mul]
  unfold geometricCoeff
  exact (inv_pow (4 : ZMod p) r).symm

theorem actual_endpoint_HF_middle (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((endpointGeometric p : (ZMod p)[X])*firstFCarry p).coeff p = 0 := by
  rw [mul_comm, product_middle_coefficient p (by omega) _ _
    (by simp [firstFCarry, binomialInterior_coefficient])
    (by simp [firstFCarry, binomialInterior_coefficient])]
  apply Eq.trans _ (geometric_F_convolution p (by omega))
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p-r ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr
    (by have h := Finset.mem_Ico.mp hr; omega)
  rw [actual_firstFCarry_field_coefficient p r (by omega) hr,
    endpointGeometric_field_coefficient p (p-r) hp hpr]
  exact mul_comm _ _

theorem actual_endpoint_HG_middle (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((endpointGeometric p : (ZMod p)[X])*firstGCarry p).coeff p =
      WPFiniteInversion.ell p 16/4 := by
  rw [mul_comm, product_middle_coefficient p (by omega) _ _
    (by simp [firstGCarry, binomialInterior_coefficient])
    (by simp [firstGCarry, binomialInterior_coefficient])]
  apply Eq.trans _ (geometric_G_convolution p (by omega))
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p-r ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr
    (by have h := Finset.mem_Ico.mp hr; omega)
  rw [actual_firstGCarry_field_coefficient p r (by omega) hr,
    endpointGeometric_field_coefficient p (p-r) hp hpr]
  exact mul_comm _ _

theorem geometricInterior_product_outer {K : Type*} [CommRing K]
    (p n : ℕ) (hp : 1 ≤ p) (hn : 2*p ≤ n) (a b : K) :
    (endpointGeometric p*binomialInterior p a b).coeff n = 0 := by
  have hd : (endpointGeometric p*binomialInterior p a b).natDegree ≤
      (p-1)+(p-1) := natDegree_mul_le.trans
    (Nat.add_le_add (endpointGeometric_degree p) (binomialInterior_degree p a b))
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The map retains the actual integral quotient and both full Frobenius factors. -/
theorem actual_endpointFirstCarry_field_source (p : ℕ) [Fact p.Prime] :
    (endpointFirstCarry p).map (Int.castRingHom (ZMod p)) =
      8*(endpointGeometric p*firstFCarry p)*X^p -
        2*(endpointGeometric p*firstFCarry p) +
        4*(endpointGeometric p*firstGCarry p) -
        (endpointGeometric p*firstGCarry p)*X^p := by
  have hF : (frobeniusF p : ℤ[X]).map (Int.castRingHom (ZMod p)) =
      C (4 : ZMod p)-X^p := by
    change (C ((4 : ℤ)^p)-X^p).map (Int.castRingHom (ZMod p)) = _
    rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    simp only [map_pow, map_ofNat, ZMod.pow_card]
  have hG : (frobeniusG p : ℤ[X]).map (Int.castRingHom (ZMod p)) =
      C (4 : ZMod p)*X^p-1 := by
    change (C ((4 : ℤ)^p)*X^p-1).map (Int.castRingHom (ZMod p)) = _
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    simp only [map_pow, map_ofNat, ZMod.pow_card]
  unfold endpointFirstCarry
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_ofNat,
    endpointGeometric_map, firstFCarry_integer_map, firstGCarry_integer_map, hF, hG, C_ofNat]
  ring

theorem endpointFirstCarry_coefficient_map (p n : ℕ) [Fact p.Prime] :
    ((endpointFirstCarry p).coeff n : ZMod p) =
      ((endpointFirstCarry p).map (Int.castRingHom (ZMod p))).coeff n := by
  rw [Polynomial.coeff_map]
  rfl

/-- E1's two resonances are derived from hf=0 and hg=beta/4, rather than supplied as premises. -/
theorem actual_endpointFirstCarry_resonances (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((endpointFirstCarry p).coeff p : ZMod p) = WPFiniteInversion.ell p 16 ∧
      ((endpointFirstCarry p).coeff (2*p) : ZMod p) = -WPFiniteInversion.ell p 16/4 := by
  have hf := actual_endpoint_HF_middle p hp
  have hg := actual_endpoint_HG_middle p hp
  have hf0 : ((endpointGeometric p : (ZMod p)[X])*firstFCarry p).coeff 0 = 0 := by
    simp [mul_coeff_zero, firstFCarry, binomialInterior_coefficient]
  have hg0 : ((endpointGeometric p : (ZMod p)[X])*firstGCarry p).coeff 0 = 0 := by
    simp [mul_coeff_zero, firstGCarry, binomialInterior_coefficient]
  have hf2 : ((endpointGeometric p : (ZMod p)[X])*firstFCarry p).coeff (2*p) = 0 :=
    geometricInterior_product_outer p (2*p) (by omega) le_rfl (-1) 4
  have hg2 : ((endpointGeometric p : (ZMod p)[X])*firstGCarry p).coeff (2*p) = 0 :=
    geometricInterior_product_outer p (2*p) (by omega) le_rfl 4 (-1)
  have h4 := four_field_ne_zero p (by omega)
  have hn : (endpointFirstCarry p).map (Int.castRingHom (ZMod p)) =
      8*((endpointGeometric p*firstFCarry p)*X^p) -
        2*(endpointGeometric p*firstFCarry p) +
        4*(endpointGeometric p*firstGCarry p) -
        (endpointGeometric p*firstGCarry p)*X^p := by
    rw [actual_endpointFirstCarry_field_source]
    ring
  constructor
  · rw [endpointFirstCarry_coefficient_map, hn]
    simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
    rw [coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, hf0, hf, hg,
      coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, hg0]
    simp only [mul_zero, sub_zero, zero_add]
    exact mul_div_cancel₀ _ h4
  · rw [endpointFirstCarry_coefficient_map, hn]
    simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
    rw [coeff_mul_X_pow', if_pos (by omega : p ≤ 2*p), show 2*p-p=p by omega,
      hf, hf2, hg2, coeff_mul_X_pow', if_pos (by omega : p ≤ 2*p),
      show 2*p-p=p by omega, hg]
    ring

theorem endpointFirstCarry_degree_sharp (p : ℕ) (hp : 1 ≤ p) :
    (endpointFirstCarry p).natDegree ≤ 3*p-2 := by
  have hf : (firstFCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p (-1) 4
  have hg : (firstGCarry p : ℤ[X]).natDegree ≤ p-1 := binomialInterior_degree p 4 (-1)
  have hs := degree_mul_bound _ _ ((p-1)+(p-1)) p
    (degree_mul_bound _ _ (p-1) (p-1) (endpointGeometric_degree p) hf) (frobeniusG_degree p)
  have ht := degree_mul_bound _ _ ((p-1)+p) (p-1)
    (degree_mul_bound _ _ (p-1) p (endpointGeometric_degree p) (frobeniusF_degree p)) hg
  unfold endpointFirstCarry
  apply degree_add_bound _ _ (3*p-2) _ (ht.trans (by omega))
  have he : (2*endpointGeometric p*firstFCarry p*frobeniusG p : ℤ[X]) =
      C 2*(endpointGeometric p*firstFCarry p*frobeniusG p) := by rw [C_ofNat]; ring
  rw [he]
  exact degree_C_mul_bound 2 _ _ (hs.trans (by omega))

theorem endpointFirstCarry_coefficient_zero (p : ℕ) : (endpointFirstCarry p).coeff 0 = 0 := by
  have hf0 : (firstFCarry p : ℤ[X]).coeff 0 = 0 := by
    simp [firstFCarry, binomialInterior_coefficient]
  have hg0 : (firstGCarry p : ℤ[X]).coeff 0 = 0 := by
    simp [firstGCarry, binomialInterior_coefficient]
  simp only [endpointFirstCarry, coeff_add, mul_coeff_zero, hf0, hg0, zero_mul, mul_zero, zero_add]

theorem actual_endpointFirstCarry_period_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (numeratorPeriod p (endpointFirstCarry p) : ZMod p) =
      (9/(4*125) : ZMod p)*WPFiniteInversion.ell p 16 := by
  have hd := endpointFirstCarry_degree_sharp p (by omega)
  have h3 : (endpointFirstCarry p).coeff (3*p) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
  rw [numeratorPeriod_two_resonance_residue p hp _ (hd.trans (by omega))
    (endpointFirstCarry_coefficient_zero p) h3]
  have h := actual_endpointFirstCarry_resonances p hp
  rw [h.1, h.2]
  have htwo : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  have hfour := four_field_ne_zero p (by omega)
  have height : (8 : ZMod p) ≠ 0 := by convert pow_ne_zero 3 htwo using 1; norm_num
  have hfive : (5 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 5 (by omega) (by omega)
  have h125 : (125 : ZMod p) ≠ 0 := by convert pow_ne_zero 3 hfive using 1; norm_num
  field_simp [htwo, hfour, height, h125]
  ring

theorem endpointCarryNormalizer_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (9/(4*125) : ℚ) := by
  change (9/(4*125) : ℚ) ∈ integralRationals p
  have h2 := WPFiniteConductorPolynomial.small_inverse_integral p 2 (by omega) (by omega)
  have h125 := WPHasseIntegralTransport.one_over_125_integral p (by omega)
  have h := (integralRationals p).mul_mem
    ((integralRationals p).mul_mem (natCast_mem _ 9) ((integralRationals p).pow_mem h2 2)) h125
  convert h using 1
  norm_num

theorem actual_endpointFirstCarry_first_digit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (numeratorPeriod p (endpointFirstCarry p))
      ((9/(4*125) : ℚ)*actualBeta p) := by
  have hc := endpointCarryNormalizer_integral p hp
  have hi := (integralRationals p).mul_mem hc (actualBeta_integral p)
  apply (integral_residue_eq_iff p _ _
    (numeratorPeriod_integral p hp _ ((endpointFirstCarry_degree_sharp p (by omega)).trans (by omega))) hi).mp
  rw [actual_endpointFirstCarry_period_residue p hp,
    Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ hc)
      (integral_denominator_cast_ne_zero p _ (actualBeta_integral p)), actualBeta_residue p hp]
  congr 1
  symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  have hfive : (5 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using primitive_weight_small_nat_ne_zero p 5 (by omega) (by omega)
  have h500 : (500 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 htwo) (pow_ne_zero 3 hfive) using 1
    norm_num
  rw [show (9/(4*125) : ℚ) = 9/500 by norm_num]
  rw [Rat.cast_div_of_ne_zero (by norm_num : ((9 : ℚ).den : ZMod p) ≠ 0)
    (by norm_num; exact h500), Rat.cast_ofNat, Rat.cast_ofNat]
  norm_num

theorem precision_add (p k : ℕ) [Fact p.Prime] (a b c d : ℚ)
    (hab : WPReview.RationalCongruent p k a b)
    (hcd : WPReview.RationalCongruent p k c d) :
    WPReview.RationalCongruent p k (a+c) (b+d) := by
  apply (precision_sub_zero p k _ _).mpr
  rw [show a+c-(b+d)=(a-b)+(c-d) by ring]
  exact precision_zero_add p k (Fact.out : p.Prime) _ _
    ((precision_sub_zero p k _ _).mp hab)
    ((precision_sub_zero p k _ _).mp hcd)

theorem precision_weaken (p k l : ℕ) (hkl : l ≤ k) (a b : ℚ)
    (h : WPReview.RationalCongruent p k a b) :
    WPReview.RationalCongruent p l a b := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((Int.ofNat_le.mpr hkl).trans h)

/-- The whole endpoint numerator gives the actual beta correction, with its original normalization. -/
theorem actual_endpointFPeriod_baseline_beta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (endpointFPeriod p)
      (16*(fermatUnit p 2)^2*endpointBaseline ((2 : ℚ)^p)/(125 : ℚ)^p +
        (p : ℚ)*(180/625)*actualBeta p) := by
  have hi16 : 0 ≤ padicValRat p (16 : ℚ) := by
    change (16 : ℚ) ∈ integralRationals p
    exact natCast_mem (integralRationals p) 16
  have hcarry := precision_prime_power_mul_integral p 1 1 16
    (numeratorPeriod p (endpointFirstCarry p)-(9/(4*125))*actualBeta p) hi16
    ((precision_sub_zero p 1 _ _).mp
      (actual_endpointFirstCarry_first_digit p hp))
  have hc : WPReview.RationalCongruent p 2
      (16*(p : ℚ)*numeratorPeriod p (endpointFirstCarry p))
      ((p : ℚ)*(180/625)*actualBeta p) := by
    apply (precision_sub_zero p 2 _ _).mpr
    convert hcarry using 1
    ring
  have h := precision_add p 2 _ _ _ _ (actual_endpointUncarried_mod_square p hp) hc
  apply precision_trans p 2 _ _ _ (actual_endpointFPeriod_first_carry_precision p hp)
  convert h using 1
  ring

def endpointFirstDigit (p : ℕ) : ℚ :=
  (10476*fermatQ p 2-3132*fermatQ p 5+180*actualBeta p)/625

def endpointPrecisionTarget (p : ℕ) : ℚ := 1044/625+(p : ℚ)*endpointFirstDigit p

theorem endpointFirstDigit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (endpointFirstDigit p) := by
  change endpointFirstDigit p ∈ integralRationals p
  let R := integralRationals p
  let q2 : R := ⟨fermatQ p 2, fermatQ_integral p 2⟩
  let q5 : R := ⟨fermatQ p 5, fermatQ_integral p 5⟩
  let beta : R := ⟨actualBeta p, actualBeta_integral p⟩
  let c5 : R := ⟨1/5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by omega) (by omega)⟩
  have h := ((10476*q2-3132*q5+180*beta)*c5^4).property
  change (10476*fermatQ p 2-3132*fermatQ p 5+180*actualBeta p)*(1/5 : ℚ)^4
    ∈ integralRationals p at h
  convert h using 1
  unfold endpointFirstDigit
  ring

theorem endpointPrecisionTarget_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (endpointPrecisionTarget p) := by
  change endpointPrecisionTarget p ∈ integralRationals p
  let R := integralRationals p
  let PP : R := ⟨p, natCast_mem R p⟩
  let e1 : R := ⟨endpointFirstDigit p, endpointFirstDigit_integral p hp⟩
  let c5 : R := ⟨1/5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by omega) (by omega)⟩
  have h := (1044*c5^4+PP*e1).property
  change 1044*(1/5 : ℚ)^4+(p : ℚ)*endpointFirstDigit p ∈ integralRationals p at h
  convert h using 1
  unfold endpointPrecisionTarget
  ring

/-- SB8 comes from the entire endpoint quotient, its pointwise main-band cancellation and E1. -/
theorem actual_endpointFPeriod_SB8 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (endpointFPeriod p)
      ((1044+(p : ℚ)*(10476*fermatQ p 2-3132*fermatQ p 5+180*actualBeta p))/625) := by
  have ht := precision_add p 2 _ _ _ _ (actual_endpointBaseline_mod_square p hp)
    (Or.inl rfl : WPReview.RationalCongruent p 2
      ((p : ℚ)*(180/625)*actualBeta p) ((p : ℚ)*(180/625)*actualBeta p))
  have h := precision_trans p 2 _ _ _ (actual_endpointFPeriod_baseline_beta p hp) ht
  unfold endpointUnitTarget at h
  convert h using 1
  ring

theorem actual_endpointFPeriod_target_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (endpointFPeriod p) (endpointPrecisionTarget p) := by
  have h := actual_endpointFPeriod_SB8 p hp
  unfold endpointPrecisionTarget endpointFirstDigit
  convert h using 1
  ring

def baseLinearTarget (p : ℕ) : ℚ :=
  (24/625)*(1+(p : ℚ)*((32/3)*fermatQ p 2-3*fermatQ p 5))

noncomputable def baseQuadraticDigit (p : ℕ) : ℚ :=
  (24/625)*((97/2)*(fermatQ p 2)^2-32*fermatQ p 2*fermatQ p 5+
    6*(fermatQ p 5)^2+(5/12)*actualAlpha p)

theorem baseQuadraticDigit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (baseQuadraticDigit p) := by
  change baseQuadraticDigit p ∈ integralRationals p
  let R := integralRationals p
  let q2 : R := ⟨fermatQ p 2, fermatQ_integral p 2⟩
  let q5 : R := ⟨fermatQ p 5, fermatQ_integral p 5⟩
  let alpha : R := ⟨actualAlpha p, actualAlpha_integral p⟩
  let c2 : R := ⟨1/2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by omega) (by omega)⟩
  let c3 : R := ⟨1/3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by omega) (by omega)⟩
  let c5 : R := ⟨1/5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by omega) (by omega)⟩
  have h := (24*c5^4*(97*c2*q2^2-32*q2*q5+6*q5^2+5*c2^2*c3*alpha)).property
  change 24*(1/5 : ℚ)^4*(97*(1/2)*(fermatQ p 2)^2-
    32*fermatQ p 2*fermatQ p 5+6*(fermatQ p 5)^2+5*(1/2)^2*(1/3)*actualAlpha p)
    ∈ integralRationals p at h
  convert h using 1
  unfold baseQuadraticDigit
  ring

theorem actual_baseMoment_mod_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (WPActualMomentDefect.baseMoment p) (baseLinearTarget p) := by
  have hb := precision_weaken p 3 2 (by omega) _ _ (actual_baseMoment_SB7 p hp)
  have he := integral_prime_power_precision p 2 _ (baseQuadraticDigit_integral p hp)
  have h : WPReview.RationalCongruent p 2
      (baseLinearTarget p+(p : ℚ)^2*baseQuadraticDigit p) (baseLinearTarget p) := by
    apply (precision_sub_zero p 2 _ _).mpr
    simpa only [add_sub_cancel_left] using he
  apply precision_trans p 2 _ _ _ _ h
  unfold baseLinearTarget baseQuadraticDigit at h ⊢
  convert hb using 1
  ring

/-- The unit multiplier in the checked actual pole coupling is p-integral. -/
theorem actual_endpointUnit_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (1+(fermatUnit p 2)⁻¹) := by
  change 1+(fermatUnit p 2)⁻¹ ∈ integralRationals p
  exact (integralRationals p).add_mem (integralRationals p).one_mem
    (fermatUnit_inverse_integral p 2 (by omega) (by omega))

/-- SB9 uses SB1's checked coupling, the actual endpoint row and the original beta identity. -/
theorem actual_polePeriod_SB9 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (WPActualEtaIntegration.polePeriod p ((p-1)/2))
      ((36/625)*fermatQ p 2*(52+(p : ℚ)*
        (-151*fermatQ p 2+150*fermatQ p 3-6*fermatQ p 5))) := by
  have hE := (precision_sub_zero p 2 _ _).mp
    (actual_endpointFPeriod_target_precision p hp)
  have hU := (precision_sub_zero p 2 _ _).mp
    (actual_endpointUnit_mod_square p hp)
  have hB := (precision_sub_zero p 2 _ _).mp
    (actual_baseMoment_mod_square p hp)
  have hq := fermatQ_integral p 2
  have he := precision_mul_integral p 2
    (fermatQ p 2*(1+(fermatUnit p 2)⁻¹)) _ 0
    ((integralRationals p).mul_mem hq (actual_endpointUnit_integral p hp)) hE
  have hu := precision_mul_integral p 2
    (fermatQ p 2*endpointPrecisionTarget p) _ 0
    ((integralRationals p).mul_mem hq (endpointPrecisionTarget_integral p hp)) hU
  have hnine : 0 ≤ padicValRat p (-9 : ℚ) := by
    change (-9 : ℚ) ∈ integralRationals p
    exact (integralRationals p).neg_mem (natCast_mem (integralRationals p) 9)
  have hb := precision_mul_integral p 2 (-9*fermatQ p 2) _ 0
    ((integralRationals p).mul_mem hnine hq) hB
  have htail := integral_prime_power_precision p 2
    (-(fermatQ p 2)^2*endpointFirstDigit p)
    ((integralRationals p).mul_mem
      ((integralRationals p).neg_mem ((integralRationals p).pow_mem hq 2))
      (endpointFirstDigit_integral p hp))
  simp only [mul_zero] at he hu hb
  have hsum := precision_zero_add p 2 (Fact.out : p.Prime) _ _
    (precision_zero_add p 2 (Fact.out : p.Prime) _ _ he hu)
    (precision_zero_add p 2 (Fact.out : p.Prime) _ _ hb htail)
  apply (precision_sub_zero p 2 _ _).mpr
  rw [actual_polePeriod_coupled p hp]
  convert hsum using 1
  unfold endpointPrecisionTarget endpointFirstDigit baseLinearTarget actualBeta
  ring

end WPMomentPrecision.BasePole
