import WPLiteralAdapter.ConductorAttachment
import WPLiteralAdapter.OriginGamma

open scoped LaurentSeries
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

theorem actual_beta_origin_fraction (p : ℕ) (hp : 4 ≤ p) :
    actualBetaFunctional p = ι (Be p (p - 4)) +
      ι (retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0) /
        ι conductorRegularDenominator := by
  have hD0 : conductorRegularDenominator.coeff 0 ≠ 0 := by
    rw [conductor_regular_denominator_constant]
    norm_num
  have hD : ι conductorRegularDenominator ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by intro hz; apply hD0; simp [hz])
  rw [actual_full_numerator_regularized p hp]
  simp only [map_add, map_mul]
  field_simp [hD]
  ring

/-- The actual Beta function expands into the full honest conductor series. -/
theorem actual_beta_full_series_attachment (p : ℕ) (hp : 4 ≤ p) :
    actualRationalSeries (actualBetaFunctional p) =
      (fullConductorSeries p : LaurentSeries ℚ) := by
  have hD0 : conductorRegularDenominator.coeff 0 ≠ 0 := by
    rw [conductor_regular_denominator_constant]
    norm_num
  rw [actual_beta_origin_fraction p hp, div_eq_mul_inv]
  unfold actualRationalSeries
  rw [map_add, map_mul]
  change actualRationalSeries (ι (Be p (p - 4))) +
    actualRationalSeries
      (ι (retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0)) *
    actualRationalSeries ((ι conductorRegularDenominator)⁻¹) =
      (fullConductorSeries p : LaurentSeries ℚ)
  rw [actual_rational_series_polynomial, actual_rational_series_polynomial,
    actual_polynomial_inverse_series _ hD0]
  simp only [fullConductorSeries, map_add, map_mul]

theorem actual_beta_full_integer_coefficient (p : ℕ) (hp : 4 ≤ p) (k : ℤ) :
    actualRationalCoefficient (actualBetaFunctional p) k =
      if k < 0 then 0 else PowerSeries.coeff k.natAbs (fullConductorSeries p) := by
  rw [actualRationalCoefficient, actual_beta_full_series_attachment p hp,
    PowerSeries.coeff_coe]

theorem actual_beta_full_negative_coefficient
    (p : ℕ) (hp : 4 ≤ p) (k : ℤ) (hk : k < 0) :
    actualRationalCoefficient (actualBetaFunctional p) k = 0 := by
  rw [actual_beta_full_integer_coefficient p hp k, if_pos hk]

theorem actual_beta_full_natural_coefficient (p : ℕ) (hp : 4 ≤ p) (k : ℕ) :
    actualRationalCoefficient (actualBetaFunctional p) k =
      PowerSeries.coeff k (fullConductorSeries p) := by
  rw [actualRationalCoefficient, actual_beta_full_series_attachment p hp,
    LaurentSeries.coeff_coe_powerSeries]

theorem actual_polynomial_integer_coefficient (P : ℚ[X]) (k : ℤ) :
    actualRationalCoefficient (ι P) k =
      if k < 0 then 0 else P.coeff k.natAbs := by
  rw [actualRationalCoefficient, actual_rational_series_polynomial,
    PowerSeries.coeff_coe]
  simp only [Polynomial.coeff_coe]

theorem actual_beta_short_source_origin_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p) *
        (actualBetaFunctional p - ι (Be p (p - 1 - p / 6)))) k) := by
  rw [actual_rational_coefficient_scalar, actual_rational_coefficient_sub,
    actual_beta_full_integer_coefficient p (by omega) k,
    actual_polynomial_integer_coefficient]
  by_cases hk : k < 0
  · simp only [if_pos hk, sub_self, mul_zero]
    exact Or.inl rfl
  · simp only [if_neg hk]
    simpa only [map_sub, Polynomial.coeff_coe] using
      actual_full_short_source_coefficient_precision p hp k.natAbs

/-- Every signed coefficient of the source-minus-short error has six digits. -/
theorem actual_source_short_origin_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
      (actualTotalSource p - RatFunc.C (WPReview.nativeEndpoint p) *
        ι (Be p (p - 1 - p / 6))) k) := by
  have hsplit : actualTotalSource p - RatFunc.C (WPReview.nativeEndpoint p) *
      ι (Be p (p - 1 - p / 6)) =
    (actualTotalSource p - RatFunc.C (WPReview.nativeEndpoint p) * actualBetaFunctional p) +
      RatFunc.C (WPReview.nativeEndpoint p) *
        (actualBetaFunctional p - ι (Be p (p - 1 - p / 6))) := by ring
  rw [hsplit, actual_rational_coefficient_add]
  exact precisionZero_add p 6 _ _
    (actual_source_conductor_error_origin_precision p hp k)
    (actual_beta_short_source_origin_precision p hp k)

theorem actual_source_short_natural_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 6 (actualRationalCoefficient (actualTotalSource p) k -
      WPReview.nativeEndpoint p * (Be p (p - 1 - p / 6)).coeff k) := by
  have hP : actualRationalCoefficient (ι (Be p (p - 1 - p / 6))) (k : ℤ) =
      (Be p (p - 1 - p / 6)).coeff k := by
    rw [actualRationalCoefficient, actual_rational_series_polynomial,
      LaurentSeries.coeff_coe_powerSeries, Polynomial.coeff_coe]
  have h := actual_source_short_origin_precision p hp (k : ℤ)
  rw [actual_rational_coefficient_sub, actual_rational_coefficient_scalar, hP] at h
  exact h

theorem actual_source_negative_origin_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℤ) (hk : k < 0) :
    precisionZero p 6 (actualRationalCoefficient (actualTotalSource p) k) := by
  have h := actual_source_short_origin_precision p hp k
  rw [actual_rational_coefficient_sub, actual_rational_coefficient_scalar,
    actual_polynomial_integer_coefficient, if_pos hk, mul_zero, sub_zero] at h
  exact h

/-- The true short polynomial degree gives the high-source precision. -/
theorem actual_source_high_origin_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℕ) (hk : 3 * p ≤ k) :
    precisionZero p 6 (actualRationalCoefficient (actualTotalSource p) k) := by
  have hd := native_cutoff_conductor_degree p hp
  have hz : (Be p (p - 1 - p / 6)).coeff k = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have h := actual_source_short_natural_precision p hp k
  simpa only [hz, mul_zero, sub_zero] using h

end

end WPLiteralAdapter
