import WPLiteralAdapter.OriginGamma
import WPActualSquareForcing

open scoped BigOperators LaurentSeries
open WPForcedSourceStokes Polynomial

namespace WPLiteralAdapter

noncomputable section

theorem actual_rational_series_polynomial (P : ℚ[X]) :
    actualRationalSeries (algebraMap ℚ[X] (RatFunc ℚ) P) =
      ((P : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [actualRationalSeries,
    ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) (LaurentSeries ℚ)]
  rfl

/-- A unit power-series denominator has the same inverse in the actual Laurent field. -/
theorem actual_polynomial_inverse_series (D : ℚ[X])
    (hD : D.coeff 0 ≠ 0) :
    actualRationalSeries ((algebraMap ℚ[X] (RatFunc ℚ) D)⁻¹) =
      HahnSeries.ofPowerSeries ℤ ℚ ((D : PowerSeries ℚ)⁻¹) := by
  have h0 : PowerSeries.constantCoeff (D : PowerSeries ℚ) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] using hD
  have hmul := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
    (PowerSeries.mul_inv_cancel (D : PowerSeries ℚ) h0)
  have hu : ((D : PowerSeries ℚ) : LaurentSeries ℚ) *
      HahnSeries.ofPowerSeries ℤ ℚ ((D : PowerSeries ℚ)⁻¹) = 1 := by
    simpa only [map_mul, map_one] using hmul
  rw [actualRationalSeries, map_inv₀]
  change (actualRationalSeries (algebraMap ℚ[X] (RatFunc ℚ) D))⁻¹ = _
  rw [actual_rational_series_polynomial]
  exact inv_eq_of_mul_eq_one_right hu

/-- The checked square forcing series is the honest expansion of the actual rational forcing. -/
theorem actual_square_forcing_series_attachment (p : ℕ) (hp : 2≤p) :
    actualRationalSeries (nativeSquareForcing p) =
      (actualSquareForcingSeries p : LaurentSeries ℚ) := by
  rw [actual_square_forcing_rational p hp, div_eq_mul_inv]
  have hD : squareRegularDenominator.coeff 0 ≠ 0 := by
    rw [square_regular_denominator_constant]
    norm_num
  simp only [actualRationalSeries, map_mul, rational_laurent_coefficient]
  change HahnSeries.C (WPReview.nativeEndpoint p^2) *
    actualRationalSeries (algebraMap ℚ[X] (RatFunc ℚ) (squareUnscaledPolynomial p)) *
    actualRationalSeries ((algebraMap ℚ[X] (RatFunc ℚ) squareRegularDenominator)⁻¹) = _
  rw [actual_rational_series_polynomial, actual_polynomial_inverse_series _ hD]
  simp only [actualSquareForcingSeries, map_mul, HahnSeries.ofPowerSeries_C]

theorem actual_square_forcing_origin_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℕ) :
    precisionZero p 6 (actualRationalCoefficient (nativeSquareForcing p) k) := by
  rw [actualRationalCoefficient, actual_square_forcing_series_attachment p (by omega),
    LaurentSeries.coeff_coe_powerSeries]
  exact actual_square_forcing_coefficient_precision p hp k

/-- The actual squared upper residual vanishes after the extended Gamma map modulo p^5. -/
theorem actual_square_forcing_gamma_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPReview.RationalCongruent p 5
      (WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (nativeSquareForcing p) k)) 0 := by
  have h := WPReview.Gamma_p6_to_p5 p (3*p-1) Fact.out (by omega) le_rfl
    (fun k => actualRationalCoefficient (nativeSquareForcing p) k) (fun _ => 0)
    (by
      intro k _hk
      rcases actual_square_forcing_origin_precision p hp k with hz | hv
      · exact Or.inl hz
      · exact Or.inr (by simpa only [sub_zero] using hv))
  simpa only [WPReview.Gamma, mul_zero, Finset.sum_const_zero] using h

end

end WPLiteralAdapter
