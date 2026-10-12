import WPFieldAssembly.NativeClosureMarkedSource
import WPFieldAssembly.NativeClosureJetSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The complete actual marked source after full-kernel integration by parts of H_J. -/
noncomputable def actualMarkedSigmaDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  ActualGreenResidue.greenPrimitive (K := K) p u * kernelDerivativeNumerator p +
    LaurentPolynomial.C (1 / 3 : K) *
      (literalKB (K := K) p * actualSigmaVK p hp * (33 - 12 * T 1)) -
    literalKB (K := K) p * actualMarkedEndSource p u h4 -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
        (actualEulerBracketDensity p) -
    LaurentPolynomial.C (1 / 3 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (properMetricDensity p)) -
    LaurentPolynomial.C (5 / 24 : K) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent *
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (actualNormI1Density p hp))

/-- Every other term and phase stays unchanged when H_J is replaced inside the residue. -/
theorem actualMarkedGreen_to_Sigma_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    originPole (actualMarkedGreenDensity (K := K) p hp u h4) =
      originPole (actualMarkedSigmaDensity (K := K) p hp u h4) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have hc : (1 / 6 : K) * 2 = 1 / 3 := by
    field_simp [h3, h6]
    ring
  have hg : originPole
      ((ActualGreenResidue.greenPrimitive (K := K) p u -
        LaurentPolynomial.C (1 / 6 : K) * HJetPullK p) *
          kernelDerivativeNumerator p) =
      originPole
        (ActualGreenResidue.greenPrimitive (K := K) p u * kernelDerivativeNumerator p +
          LaurentPolynomial.C (1 / 3 : K) *
            (literalKB p * actualSigmaVK p hp * (33 - 12 * T 1))) := by
    rw [show (ActualGreenResidue.greenPrimitive (K := K) p u -
        LaurentPolynomial.C (1 / 6 : K) * HJetPullK p) * kernelDerivativeNumerator p =
      ActualGreenResidue.greenPrimitive p u * kernelDerivativeNumerator p -
        LaurentPolynomial.C (1 / 6 : K) * (HJetPullK p * kernelDerivativeNumerator p)
      by ring, originPole_sub, originPole_C_mul, actual_HJet_kernel_origin p hp,
      originPole_add, originPole_C_mul]
    linear_combination
      originPole (literalKB (K := K) p * actualSigmaVK p hp * (33 - 12 * T 1)) * hc
  simp only [actualMarkedGreenDensity, actualMarkedSigmaDensity, originPole_sub, hg]

/-- The H_J-free marked residue remains attached to the same original actual scalar. -/
theorem actualNC77Scalar_marked_Sigma_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p
        (actualRetainedTraceScalar p hp + NativeScalarRows.actualGKQ (K := ZMod p) p) +
      originPole (actualMarkedSigmaDensity (K := K) p hp u h4) := by
  rw [actualNC77Scalar_marked_origin_source p hp u hu h4,
    actualMarkedGreen_to_Sigma_origin p hp u h4]

end WPFieldAssembly.ActualBpairContraction
