import WPMomentPrecision.ConicCoordinates
import WPMomentPrecision.Conic.WPActualConicInfinityAttachment

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualConicInfinityAttachment
  WPActualNativeHasse WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.ConicRankDensity

variable {K L : Type*} [Field K] [Field L]

/-- The coefficient of the actual IR19 differential, with the original native H and F. -/
noncomputable def nativeOmegaDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (u : K) : K :=
  (nativeHField p).eval₂ f (q u) /
    (A u * (nativeField p (p / 6)).eval₂ f (q u))

/-- The same rank-two density before the cubic pullback. -/
noncomputable def nativeRankDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (T : K) : K :=
  (rankDensityNumerator p).eval₂ f T / (rankDensityDenominator p).eval₂ f T

theorem rank_numerator_eval (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (T : K) :
    (rankDensityNumerator p).eval₂ f T = (nativeHField p).eval₂ f (1 - T ^ 2) := by
  simp [rankDensityNumerator, Polynomial.eval₂_comp]

theorem rank_denominator_eval (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (T : K) :
    (rankDensityDenominator p).eval₂ f T =
      (1 - T ^ 2) * (nativeField p (p / 6)).eval₂ f (1 - T ^ 2) := by
  rw [rankDensityDenominator_native_source p hp]
  simp [Polynomial.eval₂_comp]

/-- This includes the literal dT/du and the factor 1/3. -/
theorem actual_omega_rank_density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (u : K) (h3 : (3 : K) ≠ 0) :
    nativeOmegaDensity p f u =
      (1 / 3) * nativeRankDensity p f (cubic u) * (3 * (4 * u ^ 2 - 1)) := by
  have ht : 1 - cubic u ^ 2 = q u := by
    linear_combination -(cubic_square u)
  have hq : q u = A u * (4 * u ^ 2 - 1) := by unfold q A; ring
  unfold nativeOmegaDensity nativeRankDensity
  rw [rank_numerator_eval, rank_denominator_eval p hp, ht, hq]
  by_cases hB : 4 * u ^ 2 - 1 = 0
  · have hA : A u = 0 := by simp [A, hB]
    simp [hB, hA]
  by_cases hA : A u = 0
  · simp [hA]
  by_cases hF : (nativeField p (p / 6)).eval₂ f (A u * (4 * u ^ 2 - 1)) = 0
  · simp [hF]
  field_simp [h3, hA, hB, hF]

theorem cubic_polynomial_derivative :
    Polynomial.derivative (4 * X ^ 3 - 3 * X : K[X]) = 3 * (4 * X ^ 2 - 1) := by
  simp [map_ofNat]
  ring

theorem map_nativeOmegaDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (g : K →+* L) (u : K) :
    g (nativeOmegaDensity p f u) = nativeOmegaDensity p (g.comp f) (g u) := by
  simp only [nativeOmegaDensity, map_div₀, map_mul, Polynomial.hom_eval₂,
    q, A, map_sub, map_one, map_pow, map_ofNat]

/-- Native omega_H itself is a rational function, with no freely chosen source. -/
noncomputable def actualOmegaHRational (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  nativeOmegaDensity p RatFunc.C RatFunc.X

theorem actualOmegaHRational_rank_transport (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualOmegaHRational p =
      (1 / 3) * nativeRankDensity p RatFunc.C (cubic (RatFunc.X : RatFunc (ZMod p))) *
        (3 * (4 * (RatFunc.X : RatFunc (ZMod p)) ^ 2 - 1)) := by
  have h3field : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h3 : (3 : RatFunc (ZMod p)) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (RatFunc.C (K := ZMod p))).mpr h3field
  exact actual_omega_rank_density p hp RatFunc.C RatFunc.X h3

/-- Its literal reciprocal-coordinate coefficient retains the negative Jacobian. -/
noncomputable def actualOmegaHInfinityRational (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  -(RatFunc.X : RatFunc (ZMod p))⁻¹ ^ 2 *
    nativeOmegaDensity p RatFunc.C (RatFunc.X : RatFunc (ZMod p))⁻¹

/-- The actual rank density already has its complete signed reciprocal expansion. -/
theorem actual_rank_complete_infinity_representation (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    ((rankInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
        (-(RatFunc.X : RatFunc (ZMod p))⁻¹ ^ 2 *
          nativeRankDensity p RatFunc.C (RatFunc.X : RatFunc (ZMod p))⁻¹) := by
  simpa only [nativeRankDensity, RatFunc.algebraMap_X, mul_div_assoc] using
    actual_rank_infinity_series_representation p hp

end WPFirstResidue.ConicRankDensity
