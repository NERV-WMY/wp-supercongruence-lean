import WPLiteralAdapter.ConductorAttachment
import WPFullConductorPrecision
import WPActualEscapeCoefficients

open scoped LaurentSeries
open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

local notation "ι" => algebraMap ℚ[X] (RatFunc ℚ)

theorem actual_escape_polynomial_series (P : ℚ[X]) :
    actualEscapeRationalSeries (ι P) =
      HahnSeries.ofPowerSeries ℤ ℚ (taylor escapePoint P : PowerSeries ℚ) := by
  rw [actualEscapeRationalSeries, rational_translation_polynomial,
    actual_rational_series_polynomial]

theorem actual_escape_polynomial_inverse_series (D : ℚ[X])
    (hD : D.eval escapePoint ≠ 0) :
    actualEscapeRationalSeries ((ι D)⁻¹) =
      HahnSeries.ofPowerSeries ℤ ℚ ((taylor escapePoint D : PowerSeries ℚ)⁻¹) := by
  rw [actualEscapeRationalSeries, map_inv₀, rational_translation_polynomial]
  exact actual_polynomial_inverse_series _ (by
    simpa only [taylor_coeff_zero] using hD)

theorem taylor_escape_linear :
    taylor escapePoint escape = C (99 : ℚ) * X := by
  change taylor escapePoint (C (99 : ℚ) * X - C (50 : ℚ)) = _
  rw [map_sub, taylor_mul, taylor_C, taylor_X, taylor_C,
    mul_add, ← C_mul]
  norm_num [escapePoint]

theorem actual_escape_polynomial_escape :
    actualEscapeRationalSeries (ι escape) =
      HahnSeries.single (1 : ℤ) (99 : ℚ) := by
  rw [actual_escape_polynomial_series, taylor_escape_linear]
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    PowerSeries.coe_mul, PowerSeries.coe_C, PowerSeries.coe_X,
    HahnSeries.C_apply, HahnSeries.single_mul_single]
  norm_num

theorem actual_escape_series_scalar (q : ℚ) :
    actualEscapeRationalSeries (RatFunc.C q) = HahnSeries.C q := by
  rw [actualEscapeRationalSeries, rational_translation_scalar,
    actualRationalSeries, rational_laurent_coefficient]

/-- A double pole is attached using the actual translated unit inverse. -/
theorem actual_escape_square_fraction_series (N D : ℚ[X])
    (hD : D.eval escapePoint ≠ 0) :
    actualEscapeRationalSeries (ι N / ι (D * escape ^ 2)) =
      HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
        HahnSeries.ofPowerSeries ℤ ℚ
          ((taylor escapePoint N : PowerSeries ℚ) *
            (taylor escapePoint D : PowerSeries ℚ)⁻¹) := by
  let Ψ : RatFunc ℚ →+* LaurentSeries ℚ :=
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp
      (rationalTranslationHom escapePoint)
  have hN : Ψ (ι N) =
      HahnSeries.ofPowerSeries ℤ ℚ (taylor escapePoint N : PowerSeries ℚ) :=
    actual_escape_polynomial_series N
  have hDi : Ψ ((ι D)⁻¹) =
      HahnSeries.ofPowerSeries ℤ ℚ ((taylor escapePoint D : PowerSeries ℚ)⁻¹) :=
    actual_escape_polynomial_inverse_series D hD
  have he : Ψ ((ι escape)⁻¹) =
      HahnSeries.single (-1 : ℤ) (1 / (99 : ℚ)) := by
    rw [map_inv₀]
    change (actualEscapeRationalSeries (ι escape))⁻¹ = _
    rw [actual_escape_polynomial_escape, HahnSeries.inv_single]
    norm_num
  have he2 :
      (HahnSeries.single (-1 : ℤ) (1 / (99 : ℚ)) : LaurentSeries ℚ) ^ 2 =
      HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) := by
    rw [pow_two, HahnSeries.single_mul_single]
    norm_num
  have hf : ι N / ι (D * escape ^ 2) =
      ι N * (ι D)⁻¹ * ((ι escape)⁻¹) ^ 2 := by
    simp only [map_mul, map_pow, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  change Ψ (ι N / ι (D * escape ^ 2)) = _
  rw [hf, map_mul, map_mul, map_pow, hN, hDi, he, he2,
    ← PowerSeries.coe_mul]
  exact mul_comm _ _

theorem actual_beta_escape_series_attachment (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalSeries (actualBetaFunctional p) =
      HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
        (actualEscapeRegularSeries p : LaurentSeries ℚ) := by
  rw [actual_beta_full_numerator p hp]
  change actualEscapeRationalSeries
    (ι (originalNumerator p (p - 2)) / ι (escapeBase * escape ^ 2)) = _
  simpa only [actualEscapeRegularSeries] using
    actual_escape_square_fraction_series
      (originalNumerator p (p - 2)) escapeBase escape_base_nonzero

theorem escape_shift_coefficient (A : PowerSeries ℚ) (n : ℤ) :
    (HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
      (A : LaurentSeries ℚ)).coeff n =
      (1 / (99 : ℚ) ^ 2) *
        (if n + 2 < 0 then 0 else PowerSeries.coeff (n + 2).natAbs A) := by
  rw [HahnSeries.coeff_single_mul,
    show n - (-2) = n + 2 by ring, PowerSeries.coeff_coe]

theorem escape_shift_minus_two (A : PowerSeries ℚ) :
    (HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
      (A : LaurentSeries ℚ)).coeff (-2) =
      PowerSeries.coeff 0 A / (99 : ℚ) ^ 2 := by
  rw [escape_shift_coefficient]
  norm_num
  ring

theorem escape_shift_minus_one (A : PowerSeries ℚ) :
    (HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
      (A : LaurentSeries ℚ)).coeff (-1) =
      PowerSeries.coeff 1 A / (99 : ℚ) ^ 2 := by
  rw [escape_shift_coefficient]
  norm_num
  ring

theorem escape_shift_below (A : PowerSeries ℚ) (n : ℤ) (hn : n < -2) :
    (HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
      (A : LaurentSeries ℚ)).coeff n = 0 := by
  rw [escape_shift_coefficient, if_pos (by omega), mul_zero]

theorem actual_beta_escape_minus_two (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalCoefficient (actualBetaFunctional p) (-2) =
      conductorEscapeDouble p / (99 : ℚ) ^ 2 := by
  rw [actualEscapeRationalCoefficient, actual_beta_escape_series_attachment p hp,
    escape_shift_minus_two, actual_escape_series_double]

theorem actual_beta_escape_minus_one (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalCoefficient (actualBetaFunctional p) (-1) =
      conductorEscapeSimple p / 99 := by
  rw [actualEscapeRationalCoefficient, actual_beta_escape_series_attachment p hp,
    escape_shift_minus_one]
  calc
    PowerSeries.coeff 1 (actualEscapeRegularSeries p) / (99 : ℚ)^2 =
        (PowerSeries.coeff 1 (actualEscapeRegularSeries p) / 99) / 99 := by ring
    _ = _ := by rw [actual_escape_series_simple]

theorem actual_beta_escape_below (p : ℕ) (hp : 2 ≤ p)
    (n : ℤ) (hn : n < -2) :
    actualEscapeRationalCoefficient (actualBetaFunctional p) n = 0 := by
  rw [actualEscapeRationalCoefficient, actual_beta_escape_series_attachment p hp]
  exact escape_shift_below _ n hn

theorem actual_square_escape_series_attachment (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalSeries (nativeSquareForcing p) =
      HahnSeries.single (-2 : ℤ) (1 / (99 : ℚ) ^ 2) *
        (actualSquareEscapeSeries p : LaurentSeries ℚ) := by
  let Ψ : RatFunc ℚ →+* LaurentSeries ℚ :=
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp
      (rationalTranslationHom escapePoint)
  have hD : (1 - lam).eval escapePoint ≠ 0 := by norm_num [lam, escapePoint]
  change Ψ (nativeSquareForcing p) = _
  rw [actual_square_forcing_rational p hp]
  change Ψ (RatFunc.C (WPReview.nativeEndpoint p ^ 2) *
    ι (squareUnscaledPolynomial p) / ι ((1 - lam) * escape ^ 2)) = _
  rw [show RatFunc.C (WPReview.nativeEndpoint p ^ 2) *
      ι (squareUnscaledPolynomial p) / ι ((1 - lam) * escape ^ 2) =
      RatFunc.C (WPReview.nativeEndpoint p ^ 2) *
        (ι (squareUnscaledPolynomial p) / ι ((1 - lam) * escape ^ 2)) by ring, map_mul]
  change actualEscapeRationalSeries (RatFunc.C (WPReview.nativeEndpoint p ^ 2)) *
    actualEscapeRationalSeries
      (ι (squareUnscaledPolynomial p) / ι ((1 - lam) * escape ^ 2)) = _
  rw [actual_escape_series_scalar, actual_escape_square_fraction_series _ _ hD]
  simp only [actualSquareEscapeSeries, PowerSeries.coe_mul, PowerSeries.coe_C]
  ring

theorem actual_square_escape_minus_three (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalCoefficient (nativeSquareForcing p) (-3) = 0 := by
  rw [actualEscapeRationalCoefficient, actual_square_escape_series_attachment p hp]
  exact escape_shift_below _ (-3) (by norm_num)

theorem actual_square_escape_minus_two (p : ℕ) (hp : 2 ≤ p) :
    actualEscapeRationalCoefficient (nativeSquareForcing p) (-2) =
      PowerSeries.coeff 0 (actualSquareEscapeSeries p) / (99 : ℚ)^2 := by
  rw [actualEscapeRationalCoefficient, actual_square_escape_series_attachment p hp,
    escape_shift_minus_two]

theorem escape_inverse_99_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 / (99 : ℚ)) ∈ integralSubring p := by
  let R := integralSubring p
  have h3 : (1 / 3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h11 : (1 / 11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  rw [show (1 / (99 : ℚ)) = (1 / 3)^2 * (1 / 11) by norm_num]
  exact R.mul_mem (R.pow_mem h3 2) h11

theorem actual_square_escape_minus_three_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    precisionZero p 6
      (actualEscapeRationalCoefficient (nativeSquareForcing p) (-3)) := by
  exact Or.inl (actual_square_escape_minus_three p (by omega))

theorem actual_square_escape_minus_two_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    precisionZero p 6
      (actualEscapeRationalCoefficient (nativeSquareForcing p) (-2)) := by
  rw [actual_square_escape_minus_two p (by omega)]
  have h99 : (1 / (99 : ℚ)^2) ∈ integralSubring p := by
    rw [show (1 / (99 : ℚ)^2) = (1 / (99 : ℚ))^2 by norm_num]
    exact (integralSubring p).pow_mem (escape_inverse_99_integral p hp) 2
  convert precisionZero_mul_integral p 6 _ _
    (actual_square_escape_coefficient_precision p hp 0) h99 using 1
  ring

end

end WPLiteralAdapter
