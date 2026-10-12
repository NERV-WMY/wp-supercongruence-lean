import WPFieldAssembly.ActualNC77NativeAttachment
import WPFieldAssembly.ActualCauchyCoupled
import WPFieldAssembly.ActualBpairOriginSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualGaussBottom
open WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualJointGreen
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.ResidualProjection
  WPFieldAssembly.ActualSimplePoleResidue WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000

/-- Every actual common-trace, proper, and norm component before the original Bpair.
The rationally divided balanced carry is retained as its original integral element. -/
noncomputable def actualCommonTraceScalar (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  (2 / 3 : ZMod p) *
    (residueHom p (vBalancedDividedIntegral p hp) +
      residueHom p (commonSourceTraceIntegral p hp) +
      residueHom p (balancedTraceIntegral p hp) -
      ActualDeltaUNextSource.QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) -
      residueHom p (periodCarryIntegral p hp) -
      (1 / 2 : ZMod p) *
        residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) +
    (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
      (actualLegendreJacobi p ^ 2 * universalDunivP p +
        actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
    (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
    103 * fieldHarmonic p (p / 6) ^ 2 / 1000

/-- The entire universal D term cancels with the actual Tbar in the original projection. -/
theorem actual_QO_Tbar_cancellation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 * universalDunivP p) -
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 * actualTbarP p) =
      -(2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) -
      (1 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          (WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))) ^ 2) := by
  have h2 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have ht := universalTbar_source_six p (fieldHarmonic p (p / 6)) h2 h3
  have he : Polynomial.C (6 : ZMod p) * (actualLegendreJacobi p ^ 2 * actualTbarP p) =
      Polynomial.C (6 : ZMod p) * (actualLegendreJacobi p ^ 2 *
        WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) +
      Polynomial.C (3 : ZMod p) * (actualLegendreJacobi p ^ 2 *
        (WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))) ^ 2) -
      Polynomial.C (3 * fieldHarmonic p (p / 6) ^ 2) * actualLegendreJacobi p ^ 2 +
      Polynomial.C (6 : ZMod p) * (actualLegendreJacobi p ^ 2 * universalDunivP p) := by
    rw [map_mul]
    change Polynomial.C (6 : ZMod p) * (actualLegendreJacobi p ^ 2 *
      universalTbarP p (fieldHarmonic p (p / 6))) = _
    simp only [map_ofNat]
    linear_combination actualLegendreJacobi p ^ 2 * ht
  have hF : ActualDeltaUNextSource.QO p (actualLegendreJacobi p ^ 2) = 0 := by
    change Ij p 0 (ActualLowEuler.actualF p) = 0
    exact low_correction_both_projections_zero p hp _ (ActualLowEuler.actualF_degree p hp) 0
  have hr := congrArg (ActualDeltaUNextSource.QO p) he
  simp only [ActualDeltaUNextSource.QO_add, ActualBalancedCarry.QO_sub_local,
    ActualDeltaUNextSource.QO_C_mul, hF, mul_zero, sub_zero] at hr
  apply mul_left_cancel₀ h3
  linear_combination (norm := (field_simp [h3]; ring)) -(1 / 3 : ZMod p) * hr

/-- IR63's universal normalization preserves all actual carry and proper components. -/
theorem actualCommonTraceScalar_without_Duniv (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCommonTraceScalar p hp =
      (2 / 3 : ZMod p) *
        (residueHom p (vBalancedDividedIntegral p hp) +
          residueHom p (commonSourceTraceIntegral p hp) +
          residueHom p (balancedTraceIntegral p hp) -
          residueHom p (periodCarryIntegral p hp) -
          (1 / 2 : ZMod p) *
            residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) -
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) -
      (1 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          (WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))) ^ 2) +
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p / 6) ^ 2 / 1000 := by
  unfold actualCommonTraceScalar
  rw [ActualDeltaUNextSource.QO_add]
  linear_combination actual_QO_Tbar_cancellation p hp

/-- This is the same NC77 scalar, using the actual whole common-trace attachment. -/
theorem actualNC77Scalar_common_trace (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
      actualCommonTraceScalar p hp - NativeScalarRows.nativeBpair p hp := by
  rw [ActualNC77NativeAttachment.actualNC77Scalar_native p hp,
    actual_coupled_common_trace_row p hp]
  rfl

/-- The same scalar with its original native remainder replaced by its actual complete
Green source. No common trace, high norm slot, or H jet is assigned a value. -/
theorem actualNC77Scalar_complete_origin_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p
      (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p (actualCommonTraceScalar p hp) -
        originPole
          ((LaurentPolynomial.C (1 / 6 : K) * HJetPullK (K := K) p -
              ActualGreenResidue.greenPrimitive (K := K) p u) *
            kernelDerivativeNumerator (K := K) p +
            literalKB (K := K) p *
              (WPFiniteZSource.P p u * (33 - 12 * T 1) +
                8 * (T 1 - 4) * LaurentPolynomial.C
                  (ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u)) +
                4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * LaurentPolynomial.C
                  (ev 4 h4 (WPFiniteZSource.P p u)))) := by
  rw [actualNC77Scalar_common_trace p hp, map_sub,
    actual_bpair_complete_origin_source p hp u hu h4]

end WPFieldAssembly.ActualBpairContraction
