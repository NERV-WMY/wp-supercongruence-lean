import WPLiteralAdapter.SquareGamma
import WPLiteralAdapter.EscapeAlgebra

open scoped LaurentSeries
open WPForcedSourceStokes WPFiniteConductorPolynomial Polynomial

namespace WPLiteralAdapter

noncomputable section

theorem actual_polynomial_inverse_coefficient (D : ℚ[X])
    (hD : D.coeff 0 ≠ 0) (k : ℕ) :
    actualRationalCoefficient ((algebraMap ℚ[X] (RatFunc ℚ) D)⁻¹) k =
      PowerSeries.coeff k ((D : PowerSeries ℚ)⁻¹) := by
  rw [actualRationalCoefficient, actual_polynomial_inverse_series D hD,
    LaurentSeries.coeff_coe_powerSeries]

/-- All coefficients of each honest inverse escape power are integral at the origin. -/
theorem escape_inverse_origin_integral (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (m k : ℕ) :
    actualRationalCoefficient ((algebraMap ℚ[X] (RatFunc ℚ) (escape^m))⁻¹) k ∈
      integralSubring p := by
  let R := integralSubring p
  let S := coefficientSubring R
  have hE : escape ∈ S := S.sub_mem
    (S.mul_mem (natCast_mem S 99) (X_mem_coefficientSubring R)) (natCast_mem S 50)
  have hcoeff := (mem_coefficientSubring R _).mp (S.pow_mem hE m)
  have hconst : (escape^m).coeff 0 = (-50 : ℚ)^m := by
    simp [escape, coeff_zero_eq_eval_zero]
  have h2 : (1/2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hinv : (PowerSeries.constantCoeff ((escape^m : ℚ[X]) : PowerSeries ℚ))⁻¹ ∈ R := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hconst,
      ← inv_pow, show (-50 : ℚ)⁻¹ = -((1/2)*(1/5)^2) by norm_num]
    exact R.pow_mem (R.neg_mem (R.mul_mem h2 (R.pow_mem h5 2))) m
  have hnonzero : (escape^m).coeff 0 ≠ 0 := by
    rw [hconst]
    exact pow_ne_zero _ (by norm_num)
  rw [actual_polynomial_inverse_coefficient _ hnonzero]
  exact integral_series_inverse R _
    (fun i => by simpa only [Polynomial.coeff_coe] using hcoeff i) hinv k

/-- Both actual escape tails retain precision six at every origin Taylor coefficient. -/
theorem actual_escape_tail_origin_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (a₁ a₂ : ℚ) (ha₁ : precisionZero p 6 a₁) (ha₂ : precisionZero p 6 a₂)
    (k : ℕ) : precisionZero p 6 (actualRationalCoefficient (actualEscapeTail a₁ a₂) k) := by
  have hE : algebraMap ℚ[X] (RatFunc ℚ) escape = 99*symbol-50 := by
    norm_num [escape, symbol, map_ratCast, _root_.map_ofNat]
  rw [actualEscapeTail, div_eq_mul_inv, div_eq_mul_inv,
    actual_rational_coefficient_add, actual_rational_coefficient_scalar,
    actual_rational_coefficient_scalar, ← hE, ← map_pow]
  apply precisionZero_add p 6
  · apply precisionZero_mul_integral p 6 _ _ ha₁
    change actualRationalCoefficient ((algebraMap ℚ[X] (RatFunc ℚ) escape)⁻¹) k ∈ integralSubring p
    simpa only [pow_one] using escape_inverse_origin_integral p hp 1 k
  · exact precisionZero_mul_integral p 6 _ _ ha₂
      (escape_inverse_origin_integral p hp 2 k)

end

end WPLiteralAdapter
