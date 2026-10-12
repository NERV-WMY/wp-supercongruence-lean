import WPFieldAssembly.NativeClosureTraceEuler
import WPFieldAssembly.NativeClosureProperMetric

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource WPPIntegralReduction WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualGaussBottom
open WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.ResidualProjection WPFieldAssembly.GreenLaurentOperators
  WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.NativeScalarRows

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- Every actual retained trace and high projection outside the marked Green residue. -/
noncomputable def actualRetainedTraceScalar (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  (2 / 3 : ZMod p) *
    (residueHom p (vBalancedDividedIntegral p hp) +
      residueHom p (commonSourceTraceIntegral p hp) +
      residueHom p (balancedTraceIntegral p hp) -
      residueHom p (periodCarryIntegral p hp)) +
    (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
      (actualLegendreJacobi p * properLegendreJacobi p *
        (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
    103 * fieldHarmonic p (p / 6) ^ 2 / 1000

noncomputable def actualEulerBracketDensity (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  (ActualGreenResidue.Hpull p).toLaurent *
    D (substituteOver
      (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p))
      (originalQ : (ZMod p)[T;T⁻¹]))

/-- The original second norm projection has its complete N+p reciprocal phase. -/
noncomputable def actualNormI1Density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[T;T⁻¹] :=
  T ((((p - 1) / 2 + p : ℕ) : ℤ)) *
    NativeScalarRows.reciprocalDensity (actualNormXi p hp)

theorem actual_I1_Xi_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Ij p 1 (actualNormXi p hp) = (actualNormI1Density p hp).coeff (-1) := by
  simpa only [Ij, one_mul, actualNormI1Density, NativeScalarRows.reciprocalDensity] using
    (polar_projection ((p - 1) / 2 + p) (actualNormXi p hp)).symm

/-- The same NC77 scalar, before combining the original proper metric and native remainder. -/
theorem actualNC77Scalar_marked_row (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
      actualRetainedTraceScalar p hp + NativeScalarRows.actualGKQ (K := ZMod p) p -
      (actualEulerBracketDensity p).coeff (-1) -
      (1 / 3 : ZMod p) * (properMetricDensity p).coeff (-1) -
      (5 / 24 : ZMod p) * (actualNormI1Density p hp).coeff (-1) -
      NativeScalarRows.nativeBpair p hp := by
  rw [actualNC77Scalar_GKQ_source p hp,
    ← actual_proper_metric_origin_source p hp, actual_I1_Xi_origin p hp]
  unfold actualRetainedTraceScalar actualEulerBracketDensity
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hh : (2 / 3 : ZMod p) * (1 / 2) = 1 / 3 := by
    calc
      _ = ((2 : ZMod p) * (1 / 2)) * (1 / 3) := by ring
      _ = _ := by rw [mul_one_div_cancel h2, one_mul]
  linear_combination -(residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) * hh

variable {K : Type*} [Field K]

/-- Both original P endpoints are separate terms until the full end cancellation. -/
noncomputable def actualMarkedEndSource (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  WPFiniteZSource.P p u * (33 - 12 * T 1) +
    8 * (T 1 - 4) * LaurentPolynomial.C
      (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
    4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
      (ev 4 h4 (WPFiniteZSource.P p u))

/-- One actual marked source retains the H jet, Euler adjoint, proper metric, and all phases. -/
noncomputable def actualMarkedGreenDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  (ActualGreenResidue.greenPrimitive (K := K) p u -
      LaurentPolynomial.C (1 / 6 : K) * HJetPullK (K := K) p) *
        kernelDerivativeNumerator (K := K) p -
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

/-- The complete marked residue belongs to the same original actual scalar.
The actual divided Vbal and common traces still require their full source values. -/
theorem actualNC77Scalar_marked_origin_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p
        (actualRetainedTraceScalar p hp + NativeScalarRows.actualGKQ (K := ZMod p) p) +
      originPole (actualMarkedGreenDensity (K := K) p hp u h4) := by
  let f : ZMod p →+* K := ActualThreePhase.φ p
  have hb := actual_bpair_complete_origin_source (K := K) p hp u hu h4
  have hg : originPole
      ((ActualGreenResidue.greenPrimitive (K := K) p u -
        LaurentPolynomial.C (1 / 6 : K) * HJetPullK (K := K) p) *
          kernelDerivativeNumerator (K := K) p -
        literalKB (K := K) p * actualMarkedEndSource p u h4) =
      -f (NativeScalarRows.nativeBpair p hp) := by
    rw [actualMarkedEndSource]
    have he :
        (ActualGreenResidue.greenPrimitive (K := K) p u -
          LaurentPolynomial.C (1 / 6 : K) * HJetPullK (K := K) p) *
            kernelDerivativeNumerator (K := K) p -
          literalKB (K := K) p *
            (WPFiniteZSource.P p u * (33 - 12 * T 1) +
              8 * (T 1 - 4) * LaurentPolynomial.C
                (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
              4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
                (ev 4 h4 (WPFiniteZSource.P p u))) =
        -((LaurentPolynomial.C (1 / 6 : K) * HJetPullK (K := K) p -
          ActualGreenResidue.greenPrimitive (K := K) p u) *
            kernelDerivativeNumerator (K := K) p +
          literalKB (K := K) p *
            (WPFiniteZSource.P p u * (33 - 12 * T 1) +
              8 * (T 1 - 4) * LaurentPolynomial.C
                (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
              4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
                (ev 4 h4 (WPFiniteZSource.P p u)))) := by ring
    rw [he, show ∀ L : K[T;T⁻¹], -L = LaurentPolynomial.C (-1 : K) * L from
      fun L => by rw [map_neg, map_one, neg_one_mul], originPole_C_mul, ← hb]
    simp only [neg_one_mul, f]
  rw [actualNC77Scalar_marked_row p hp]
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat]
  rw [actualMarkedGreenDensity, originPole_sub, originPole_sub, originPole_sub,
    originPole_C_mul, originPole_C_mul, originPole_cleared p hp,
    originPole_cleared p hp, originPole_cleared p hp,
    WPActualChiSource.coefficientMap_coeff, WPActualChiSource.coefficientMap_coeff,
    WPActualChiSource.coefficientMap_coeff, hg]
  ring

end WPFieldAssembly.ActualBpairContraction
