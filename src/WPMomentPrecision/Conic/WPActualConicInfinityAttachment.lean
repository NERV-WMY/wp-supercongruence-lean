import WPMomentPrecision.Conic.WPActualConicInfinitySource
import WPMomentPrecision.Conic.WPRationalInfinitySeries
import WPActualEtaIntegrality

open scoped BigOperators Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualNativeHasse WPActualNativeQuadraticSquare
  WPActualEtaIntegrality WPActualPullbackSource WPPIntegralReduction WPRationalInfinitySeries

namespace WPActualConicInfinityAttachment

theorem nativeHField_literal_coefficient (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hn : n ≤ p / 6) :
    (nativeHField p).coeff n = (WPReview.nativeCoefficient n / (n : ℚ) : ℚ) := by
  rw [nativeHField_coeff, if_pos hn]
  by_cases hn0 : n = 0
  · subst n; simp
  have hden := integral_denominator_cast_ne_zero p _
    (actual_native_coefficient_integral p n hp (by omega))
  have hnu : (n : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p n (by omega) (by omega)
  have hnum : (((n : ℚ).num : ℤ) : ZMod p) ≠ 0 := by simpa using hnu
  rw [Rat.cast_div_of_ne_zero hden hnum]
  simp

/-- Original rational H_d lifted coefficient by coefficient into the integral subring. -/
noncomputable def nativeHIntegral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  ∑ n : Fin (p / 6 + 1), monomial n.val
    ⟨WPReview.nativeCoefficient n.val / (n.val : ℚ),
      native_Hcoefficient_integral p n.val hp (by have hn := n.isLt; omega)⟩

theorem nativeHIntegral_map_rational (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeHIntegral p hp).map (integralRationals p).subtype = Hpolynomial (p / 6) := by
  simp only [nativeHIntegral, Polynomial.map_sum, map_monomial, Subring.coe_subtype]
  exact Fin.sum_univ_eq_sum_range
    (fun n => monomial n (WPReview.nativeCoefficient n / (n : ℚ))) (p / 6 + 1)

theorem nativeHIntegral_map_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeHIntegral p hp).map (residueHom p) = nativeHField p := by
  ext n
  rw [coeff_map]
  change (((nativeHIntegral p hp).coeff n).val : ZMod p) = _
  have he := congrArg (fun P : ℚ[X] => P.coeff n) (nativeHIntegral_map_rational p hp)
  rw [coeff_map] at he
  change ((nativeHIntegral p hp).coeff n).val = (Hpolynomial (p / 6)).coeff n at he
  rw [he, Hpolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn]
    exact (nativeHField_literal_coefficient p n hp (by omega)).symm
  · rw [if_neg hn, nativeHField_coeff, if_neg (by omega)]
    simp

theorem rankDensityDenominator_native_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankDensityDenominator p =
      (1 - X ^ 2) * (nativeField p (p / 6)).comp (1 - X ^ 2) := by
  rw [actual_native_Jacobi_square p hp]
  rfl

/-- The whole actual native density, its reciprocal Jacobian and regular infinity expansion. -/
theorem actual_rank_infinity_series_representation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((rankInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
        (-(algebraMap (ZMod p)[X] (RatFunc (ZMod p)) X)⁻¹ ^ 2 *
          (rankDensityNumerator p).eval₂ RatFunc.C
            (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) X)⁻¹ /
          (rankDensityDenominator p).eval₂ RatFunc.C
            (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) X)⁻¹) := by
  exact rational_infinity_series_representation (2 * (p / 6))
    (rankDensityNumerator p) (rankDensityDenominator p)
    (rankDensityNumerator_degree p) (rankDensityDenominator_degree p hp)
    (rankDensityDenominator_ne_zero p hp)

end WPActualConicInfinityAttachment
