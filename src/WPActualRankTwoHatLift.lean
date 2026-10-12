import WPActualRankTwoComparison

open scoped Polynomial BigOperators
open Polynomial WPPIntegralReduction WPActualRankTwoLegendreField WPActualRankTwoFirstLift
  WPActualRankTwoProper WPActualRankTwoComparison WPActualGaussBottom WPActualGaussProper
  WPActualCMGauss WPActualRankTwoLowTaylor WPActualRankTwoResidueSource
  WPActualRankTwoDividedDifference WPActualNativeHasse WPActualRankTwoGaussODE
  WPActualRankTwoParameter

namespace WPActualRankTwoHatLift

set_option maxHeartbeats 800000

noncomputable def rationalHarmonic (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℚ)

theorem rationalHarmonic_zero : rationalHarmonic 0 = 0 := by simp [rationalHarmonic]

theorem rationalHarmonic_succ (n : ℕ) :
    rationalHarmonic (n + 1) = rationalHarmonic n + 1 / ((n + 1 : ℕ) : ℚ) := by
  simp only [rationalHarmonic, Finset.sum_range_succ]

/-- A literal rational reciprocal, retained in the integral coefficient subring. -/
noncomputable def smallIntegralInverse (p j : ℕ) [Fact p.Prime] : integralRationals p :=
  if h : 0 < j ∧ j < p then
    ⟨1 / (j : ℚ), WPFiniteConductorPolynomial.small_inverse_integral p j h.1 h.2⟩ else 0

theorem smallIntegralInverse_value (p j : ℕ) [Fact p.Prime] (hj : 0 < j) (hjp : j < p) :
    (smallIntegralInverse p j).val = 1 / (j : ℚ) := by
  simp [smallIntegralInverse, hj, hjp]

theorem smallIntegralInverse_field (p j : ℕ) [Fact p.Prime] (hj : 0 < j) (hjp : j < p) :
    residueHom p (smallIntegralInverse p j) = (j : ZMod p)⁻¹ := by
  have hmul : (j : integralRationals p) * smallIntegralInverse p j = 1 := by
    apply Subtype.ext
    change (j : ℚ) * (smallIntegralInverse p j).val = 1
    rw [smallIntegralInverse_value p j hj hjp]
    exact mul_one_div_cancel (by exact_mod_cast (Nat.ne_of_gt hj) : (j : ℚ) ≠ 0)
  have h := congrArg (residueHom p) hmul
  simp only [map_mul, map_natCast, map_one] at h
  apply mul_left_cancel₀ (small_cast_ne_zero p j hj hjp)
  rw [h, mul_inv_cancel₀ (small_cast_ne_zero p j hj hjp)]

noncomputable def integralHarmonic (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ Finset.range n, smallIntegralInverse p (j + 1)

theorem integralHarmonic_value (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    (integralRationals p).subtype (integralHarmonic p n) = rationalHarmonic n := by
  rw [integralHarmonic, map_sum, rationalHarmonic]
  apply Finset.sum_congr rfl
  intro j hj
  exact smallIntegralInverse_value p (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)

theorem integralHarmonic_field (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    residueHom p (integralHarmonic p n) = fieldHarmonic p n := by
  rw [integralHarmonic, map_sum, fieldHarmonic]
  apply Finset.sum_congr rfl
  intro j hj
  exact smallIntegralInverse_field p (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)

noncomputable def rationalProperGauss (d : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial d (fun n => (rationalHarmonic d - rationalHarmonic n) *
    (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff n))

noncomputable def integralProperGauss (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  rankCoefficientPolynomial (p / 6) (fun n => (integralHarmonic p (p / 6) - integralHarmonic p n) *
    (((shiftedLegendre (p / 6)).map (Int.castRingHom (integralRationals p))).coeff n))

theorem integralProperGauss_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralProperGauss p).map (integralRationals p).subtype = rationalProperGauss (p / 6) := by
  ext n
  rw [coeff_map, integralProperGauss, rationalProperGauss,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs with hn
  · rw [map_mul, map_sub, integralHarmonic_value p (p / 6) (by omega),
      integralHarmonic_value p n (by omega)]
    congr 1
    rw [← coeff_map, map_integer_polynomial]
  · exact map_zero _

theorem integralProperGauss_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralProperGauss p).map (residueHom p) = degreeProperGauss p := by
  ext n
  rw [coeff_map, integralProperGauss, rankCoefficientPolynomial_coeff, degreeProperGauss_coeff]
  split_ifs with hn
  · rw [map_mul, map_sub, integralHarmonic_field p (p / 6) (by omega),
      integralHarmonic_field p n (by omega)]
    congr 1
    rw [← coeff_map, map_integer_polynomial]
    rfl
  · rw [coeff_eq_zero_of_natDegree_lt ((actualLegendreGauss_degree p).trans_lt (by omega)), mul_zero]
    exact map_zero _

noncomputable def rationalProperJacobi (d : ℕ) : ℚ[X] :=
  -(rationalProperGauss d).comp (C (1 / 2 : ℚ) * (1 - X))

noncomputable def integralProperJacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  -(integralProperGauss p).comp (C (integralHalf p hp) * (1 - X))

theorem integralProperJacobi_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralProperJacobi p hp).map (integralRationals p).subtype = rationalProperJacobi (p / 6) := by
  rw [integralProperJacobi, Polynomial.map_neg, Polynomial.map_comp, integralProperGauss_value p hp]
  simp [rationalProperJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem integralProperJacobi_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralProperJacobi p hp).map (residueHom p) = properLegendreJacobi p := by
  rw [integralProperJacobi, Polynomial.map_neg, Polynomial.map_comp, integralProperGauss_field p hp]
  simp [properLegendreJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf_field]

theorem rationalProperGauss_coeff (d n : ℕ) :
    (rationalProperGauss d).coeff n = (rationalHarmonic d - rationalHarmonic n) *
      (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff n) := by
  rw [rationalProperGauss, rankCoefficientPolynomial_coeff]
  split_ifs with hn
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt
      (Polynomial.natDegree_map_le.trans_lt (by rw [natDegree_shiftedLegendre]; omega)), mul_zero]

theorem rationalProperGauss_origin (d : ℕ) :
    (rationalProperGauss d).eval 0 = rationalHarmonic d := by
  rw [← coeff_zero_eq_eval_zero, rationalProperGauss_coeff, rationalHarmonic_zero]
  simp [coeff_map, coeff_shiftedLegendre]

theorem rationalProperGauss_degree (d : ℕ) :
    (rationalProperGauss d).natDegree ≤ d - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [rationalProperGauss_coeff]
  by_cases he : n = d
  · simp [he]
  · rw [coeff_eq_zero_of_natDegree_lt
      (Polynomial.natDegree_map_le.trans_lt (by rw [natDegree_shiftedLegendre]; omega)), mul_zero]

theorem rationalProperGauss_recurrence (d n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * (rationalProperGauss d).coeff (n + 1) -
      ((n : ℚ) - d) * ((n : ℚ) + d + 1) * (rationalProperGauss d).coeff n =
      -((n : ℚ) + 1) * (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff (n + 1)) := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) (shiftedLegendre_cleared_recurrence d n)
  have hrec : ((n : ℚ) + 1) ^ 2 * (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff (n + 1)) =
      ((n : ℚ) - d) * ((n : ℚ) + d + 1) * (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff n) := by
    simpa only [coeff_map, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_sub,
      Int.cast_one, Int.cast_natCast, Int.coe_castRingHom] using he
  have hi : ((n : ℚ) + 1) * (1 / ((n : ℚ) + 1)) = 1 := mul_one_div_cancel (by positivity)
  rw [rationalProperGauss_coeff, rationalProperGauss_coeff, rationalHarmonic_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  linear_combination (rationalHarmonic d - rationalHarmonic n) * hrec -
    (((n : ℚ) + 1) * (((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff (n + 1))) * hi

theorem rationalProperGauss_source (d : ℕ) :
    legendreRegular d (rationalProperGauss d) =
      -((shiftedLegendre d).map (Int.castRingHom ℚ)).derivative := by
  have he : legendreEuler d (rationalProperGauss d) =
      -theta ((shiftedLegendre d).map (Int.castRingHom ℚ)) := by
    ext n
    cases n with
    | zero => simp [legendreEuler_coeff_zero, theta_coeff]
    | succ n =>
      rw [legendreEuler_coeff_succ, coeff_neg, theta_coeff]
      simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using rationalProperGauss_recurrence d n
  rw [legendreEuler_eq_X_regular, theta] at he
  have hz : X * (legendreRegular d (rationalProperGauss d) +
      ((shiftedLegendre d).map (Int.castRingHom ℚ)).derivative) = 0 := by linear_combination he
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left X_ne_zero)

theorem rationalProperJacobi_endpoint_one (d : ℕ) :
    (rationalProperJacobi d).eval 1 = -rationalHarmonic d := by
  simp [rationalProperJacobi, eval_comp, rationalProperGauss_origin]

theorem rationalProperJacobi_degree (d : ℕ) :
    (rationalProperJacobi d).natDegree ≤ d - 1 := by
  rw [rationalProperJacobi, natDegree_neg]
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul (rationalProperGauss_degree d) jacobiCoordinate_degree).trans (by simp))

theorem rationalProperJacobi_source (d : ℕ) :
    legendreJacobi d (rationalProperJacobi d) = -2 * (rationalLegendre d).derivative := by
  have haP : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    have h := congrArg (C : ℚ → ℚ[X]) (by norm_num : (2 : ℚ) * (1 / 2) = 1)
    simpa only [map_mul, map_ofNat, map_one] using h
  rw [rationalProperJacobi, legendreJacobi_neg,
    ← legendre_coordinate d (1 / 2 : ℚ) (by norm_num), rationalProperGauss_source]
  simp only [neg_comp, neg_neg, rationalLegendre, derivative_comp, derivative_mul,
    derivative_C, zero_mul, zero_add, derivative_sub, derivative_one, derivative_X,
    zero_sub, mul_neg, mul_one]
  linear_combination -((shiftedLegendre d).map (Int.castRingHom ℚ)).derivative.comp
    (C (1 / 2 : ℚ) * (1 - X)) * haP

noncomputable def integralLogPolynomial (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  ∑ j ∈ Finset.Ico 1 p, C (smallIntegralInverse p j) * X ^ j

noncomputable def rationalLogPolynomial (p : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.Ico 1 p, C (1 / (j : ℚ)) * X ^ j

theorem integralLogPolynomial_value (p : ℕ) [Fact p.Prime] :
    (integralLogPolynomial p).map (integralRationals p).subtype = rationalLogPolynomial p := by
  rw [integralLogPolynomial, rationalLogPolynomial, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjj := Finset.mem_Ico.mp hj
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rw [show (integralRationals p).subtype (smallIntegralInverse p j) = 1 / (j : ℚ) from
    smallIntegralInverse_value p j (by omega) hjj.2]

theorem integralLogPolynomial_field (p : ℕ) [Fact p.Prime] :
    (integralLogPolynomial p).map (residueHom p) = WPFiniteAffineLog.LP p := by
  rw [integralLogPolynomial, WPFiniteAffineLog.LP, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjj := Finset.mem_Ico.mp hj
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rw [smallIntegralInverse_field p j (by omega) hjj.2]

noncomputable def integralEvenLog (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  C (integralHalf p hp) * (integralLogPolynomial p + (integralLogPolynomial p).comp (-X))

noncomputable def rationalEvenLog (p : ℕ) : ℚ[X] :=
  C (1 / 2 : ℚ) * (rationalLogPolynomial p + (rationalLogPolynomial p).comp (-X))

theorem integralEvenLog_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralEvenLog p hp).map (integralRationals p).subtype = rationalEvenLog p := by
  simp only [integralEvenLog, rationalEvenLog, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    integralLogPolynomial_value]
  rfl

theorem integralEvenLog_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralEvenLog p hp).map (residueHom p) = evenLogPolynomial p := by
  simp only [integralEvenLog, evenLogPolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    integralLogPolynomial_field, integralHalf_field, one_div]

noncomputable def rationalRankHat (p : ℕ) : ℚ[X] :=
  rationalLegendre (p / 6) * (rationalEvenLog p +
    C ((WPFiniteInversion.integerFermatQuotient p 2 : ℚ) - rationalHarmonic (p / 6))) -
    X ^ p * rationalProperJacobi (p / 6)

noncomputable def integralRankHat (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  integralLegendre p (p / 6) hp * (integralEvenLog p hp +
    C ((WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) - integralHarmonic p (p / 6))) -
    X ^ p * integralProperJacobi p hp

theorem integralRankHat_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRankHat p hp).map (integralRationals p).subtype = rationalRankHat p := by
  simp only [integralRankHat, rationalRankHat, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    integralLegendre_value, integralEvenLog_value, integralProperJacobi_value,
    map_sub, map_intCast]
  rw [show (integralRationals p).subtype (integralHarmonic p (p / 6)) = rationalHarmonic (p / 6) from
    integralHarmonic_value p (p / 6) (by omega)]
  simp only [Polynomial.map_intCast]

theorem integralRankHat_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRankHat p hp).map (residueHom p) = rankHatField p := by
  simp only [integralRankHat, rankHatField, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    integralLegendre_field, integralEvenLog_field, integralProperJacobi_field,
    map_sub, map_intCast]
  rw [integralHarmonic_field p (p / 6) (by omega)]
  simp only [Polynomial.map_intCast]

theorem rationalRankHat_coefficient_integral (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p ((rationalRankHat p).coeff n) := by
  rw [← integralRankHat_value p hp, coeff_map]
  exact ((integralRankHat p hp).coeff n).property

theorem rationalRankHat_coefficient_field (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((rationalRankHat p).coeff n : ZMod p) = (rankHatField p).coeff n := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff n) (integralRankHat_value p hp)
  have hr := congrArg (fun P : (ZMod p)[X] => P.coeff n) (integralRankHat_field p hp)
  rw [coeff_map] at hv hr
  rw [← hv]
  exact hr

theorem rankDividedJacobi_coefficient_field (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((rankDividedJacobi p).coeff n : ZMod p) = (actualRankDividedField p hp).coeff n := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff n) (rankDividedIntegralJacobi_value p hp)
  rw [coeff_map] at hv
  rw [← hv]
  rw [actualRankDividedField, coeff_map]
  rfl

/-- The actual next native digit, divided in Q before taking any residue. -/
noncomputable def actualSecondCarryCoefficient (p n : ℕ) : ℚ :=
  ((rankDividedJacobi p).coeff n - (rationalRankHat p).coeff n) / (p : ℚ)

theorem actualSecondCarryCoefficient_integral (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualSecondCarryCoefficient p n) := by
  have ha := actual_rankDividedJacobi_integral p n (by omega : 7 ≤ p)
  have hb := rationalRankHat_coefficient_integral p n (by omega : 7 ≤ p)
  have hf : ((rankDividedJacobi p).coeff n : ZMod p) = ((rationalRankHat p).coeff n : ZMod p) := by
    rw [rankDividedJacobi_coefficient_field p n (by omega),
      rationalRankHat_coefficient_field p n (by omega), actual_rankDividedField_eq_hat p hp]
  have hg := (integral_residue_eq_iff p _ _ ha hb).mp hf
  rcases hg with hz | hv
  · simp [actualSecondCarryCoefficient, hz]
  · by_cases hz : (rankDividedJacobi p).coeff n - (rationalRankHat p).coeff n = 0
    · simp [actualSecondCarryCoefficient, hz]
    · have hpq : (p : ℚ) ≠ 0 := by positivity
      rw [actualSecondCarryCoefficient, padicValRat.div hz hpq, padicValRat.self (by omega)]
      omega

theorem rationalLogPolynomial_degree (p : ℕ) :
    (rationalLogPolynomial p).natDegree ≤ p - 1 := by
  unfold rationalLogPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjp := (Finset.mem_Ico.mp hj).2
  exact (natDegree_C_mul_le _ _).trans (by simp; omega)

theorem rationalEvenLog_degree (p : ℕ) : (rationalEvenLog p).natDegree ≤ p - 1 := by
  have hc : (-X : ℚ[X]).natDegree ≤ 1 := by simp
  have hn : ((rationalLogPolynomial p).comp (-X)).natDegree ≤ p - 1 :=
    Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul (rationalLogPolynomial_degree p) hc).trans (by simp))
  unfold rationalEvenLog
  exact (natDegree_C_mul_le _ _).trans
    (by simpa only [Nat.max_self] using natDegree_add_le_of_le (rationalLogPolynomial_degree p) hn)

theorem rationalRankHat_degree (p : ℕ) (hp : 7 ≤ p) :
    (rationalRankHat p).natDegree ≤ p + p / 6 - 1 := by
  have hc : (C ((WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
      rationalHarmonic (p / 6))).natDegree ≤ p - 1 := by rw [natDegree_C]; exact Nat.zero_le _
  have hH : (rationalEvenLog p +
      C ((WPFiniteInversion.integerFermatQuotient p 2 : ℚ) - rationalHarmonic (p / 6))).natDegree ≤ p - 1 :=
    by simpa only [Nat.max_self] using natDegree_add_le_of_le (rationalEvenLog_degree p) hc
  have hY := natDegree_mul_le (p := rationalLegendre (p / 6))
    (q := rationalEvenLog p + C ((WPFiniteInversion.integerFermatQuotient p 2 : ℚ) - rationalHarmonic (p / 6)))
  have hn := natDegree_mul_le (p := (X : ℚ[X]) ^ p) (q := rationalProperJacobi (p / 6))
  have hYb : (rationalLegendre (p / 6) * (rationalEvenLog p +
      C ((WPFiniteInversion.integerFermatQuotient p 2 : ℚ) - rationalHarmonic (p / 6)))).natDegree ≤
      p + p / 6 - 1 := hY.trans (by have hy := rationalLegendre_degree (p / 6); omega)
  have hnb : ((X : ℚ[X]) ^ p * rationalProperJacobi (p / 6)).natDegree ≤ p + p / 6 - 1 :=
    hn.trans (by have hn' := rationalProperJacobi_degree (p / 6); simp only [natDegree_X_pow] at *; omega)
  unfold rationalRankHat
  simpa only [Nat.max_self] using natDegree_sub_le_of_le hYb hnb

noncomputable def actualSecondCarryPolynomial (p : ℕ) : ℚ[X] :=
  WPActualNativeSecondTaylor.coefficientPolynomial (p + p / 6 - 1) (actualSecondCarryCoefficient p)

theorem actualSecondCarryPolynomial_degree (p : ℕ) :
    (actualSecondCarryPolynomial p).natDegree ≤ p + p / 6 - 1 :=
  WPActualNativeSecondTaylor.coefficientPolynomial_degree _ _

theorem actualSecondCarryPolynomial_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankDividedJacobi p - rationalRankHat p = C (p : ℚ) * actualSecondCarryPolynomial p := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  ext n
  rw [coeff_sub, coeff_C_mul, actualSecondCarryPolynomial,
    WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  split_ifs with hn
  · unfold actualSecondCarryCoefficient
    field_simp
  · rw [coeff_eq_zero_of_natDegree_lt ((rankDividedJacobi_degree p).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((rationalRankHat_degree p (by omega)).trans_lt (by omega))]
    ring

theorem actualSecondCarryPolynomial_integral (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualSecondCarryPolynomial p).coeff n) := by
  rw [actualSecondCarryPolynomial, WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  split_ifs
  · exact actualSecondCarryCoefficient_integral p n hp
  · simp

theorem rationalRankHat_endpoint_one (p : ℕ) :
    (rationalRankHat p).eval 1 =
      (rationalEvenLog p).eval 1 + (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) := by
  simp only [rationalRankHat, eval_sub, eval_mul, eval_add, eval_C, eval_pow, eval_X,
    one_pow, one_mul, rationalLegendre_endpoint_one, rationalProperJacobi_endpoint_one]
  ring

theorem actualSecondCarryPolynomial_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSecondCarryPolynomial p).eval 1 =
      -((rationalEvenLog p).eval 1 + (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)) / (p : ℚ) := by
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (actualSecondCarryPolynomial_source p hp)
  rw [eval_sub, rankDividedJacobi_endpoint_one, rationalRankHat_endpoint_one,
    eval_mul, eval_C] at h
  apply (eq_div_iff (by positivity : (p : ℚ) ≠ 0)).mpr
  linear_combination -h

end WPActualRankTwoHatLift
