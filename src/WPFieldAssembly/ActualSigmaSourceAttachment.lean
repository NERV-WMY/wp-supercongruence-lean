import WPFieldAssembly.ActualSigmaClearedSource
import WPFieldAssembly.ActualComparisonKwAttachment
import WPFieldAssembly.ActualSigmaIntegral

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSigmaClearedSource WPFieldAssembly.ActualComparisonKwAttachment
  WPFieldAssembly.ActualHFTransmutation WPFieldAssembly.ActualSigmaIntegral
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualSB101Trace

namespace WPFieldAssembly.ActualSigmaSourceAttachment

set_option maxHeartbeats 1400000

/- Literal attachment to the original carrier. The SB95 core never defines
the existing sigma or replaces its branch scalar. The later field first-carry
and UW17 primitive attachment remain separate obligations. -/

theorem actualFiniteEvenSquaredQ_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualJointGreen.finiteEvenSquaredQ p = ActualSigmaFiniteEvenSource.finiteEvenSquaredQ p := by
  rw [ActualJointGreen.finiteEvenSquaredQ, ActualJointGreen.finiteEvenLogQ_eq_actual p hp]
  rfl

theorem actualFiniteEvenSquaredIntegral_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualJointGreen.finiteEvenSquaredIntegral p =
      ActualSigmaFiniteEvenSource.finiteEvenSquaredIntegral p := by
  apply Polynomial.map_injective (WPPIntegralReduction.integralRationals p).subtype
    Subtype.val_injective
  rw [ActualJointGreen.finiteEvenSquaredIntegral_value p hp,
    ActualSigmaFiniteEvenSource.finiteEvenSquaredIntegral_value p hp,
    actualFiniteEvenSquaredQ_original p hp]

theorem actual_comparison_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    comparisonRational p hp = originalComparisonQ p (comparisonBranchQ p) := by
  have hcoord : comparisonCoordinateQ =
      (WPFiniteWSource.squaredCoordinate : ℚ[X]) := by
    simp only [comparisonCoordinateQ, WPFiniteWSource.squaredCoordinate, one_div]
  have hmove : movingComparisonQ p = originalMovingQ p := by
    simp only [movingComparisonQ, originalMovingQ,
      actualFiniteEvenSquaredQ_original p hp, hcoord]
  have h17 : LaurentPolynomial.C (17 / 15 : ℚ) =
      LaurentPolynomial.C (1 / 15 : ℚ) * 17 := by
    change LaurentPolynomial.C (17 / 15 : ℚ) =
      LaurentPolynomial.C (1 / 15 : ℚ) * LaurentPolynomial.C (17 : ℚ)
    rw [← map_mul]
    congr 1
    ring
  have h4 : LaurentPolynomial.C (4 / 15 : ℚ) =
      LaurentPolynomial.C (1 / 15 : ℚ) * 4 := by
    change LaurentPolynomial.C (4 / 15 : ℚ) =
      LaurentPolynomial.C (1 / 15 : ℚ) * LaurentPolynomial.C (4 : ℚ)
    rw [← map_mul]
    congr 1
    ring
  rw [comparisonRational_full_form p hp]
  simp only [hmove, T_zero, mul_one, originalComparisonQ,
    originalPhaseQ, originalEvenSumQ]
  rw [h17, h4]
  ring

theorem actual_Bsource_original (p : ℕ) : actualBSourceQ p = originalBQ p := by
  have hcoord : ActualGreenPrimitive.greenCoordinateQ p =
      (WPFiniteWSource.squaredCoordinate : ℚ[X]) := by
    simp only [ActualGreenPrimitive.greenCoordinateQ,
      WPFiniteWSource.squaredCoordinate, one_div]
  simp only [actualBSourceQ, originalBQ, hcoord]

/-- The actual divided rational source is attached coefficientwise, before reduction. -/
theorem actualSigmaQ_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualSigmaQ p hp = LaurentPolynomial.C (1 / (p : ℚ)) *
      (D (originalComparisonQ p (comparisonBranchQ p)) - originalBQ p) := by
  rw [actualSigmaQ, actual_comparison_original p hp, actual_Bsource_original p]

/-- The original integral sigma has exactly the complete SB95 rational cleared source. -/
theorem actualSigmaIntegral_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
          (actualSigmaIntegral p hp) =
      LaurentPolynomial.C (1 / 2 : ℚ) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) * originalNormDifferenceQ p +
      LaurentPolynomial.C (2 * originalFourCarryQ p) * originalPhaseQ p *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        ((4 - T 1) - T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * (4 * T 1 - 1)) -
      LaurentPolynomial.C (4 / 15 : ℚ) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * originalEvenSumQ p := by
  rw [actualSigmaIntegral_value p hp, actualSigmaQ_original p hp]
  exact originalSigma_quotient_cleared p hp (comparisonBranchQ p)

end WPFieldAssembly.ActualSigmaSourceAttachment
