import WPFieldAssembly.ActualBpairEuler
import WPFieldAssembly.ActualIntegralGreenTrace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualGaussBottom WPFieldAssembly.ActualResidualAssembly
  WPFieldAssembly.ActualJointGreen
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.ResidualProjection
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ActualIntegralGreenTrace
  WPFieldAssembly.ActualR0Node WPActualRankTwoResidueSource

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000

/-- The complete direct SB82e row retains its coupled norm and upper Xi projection. -/
theorem actual_direct_coupled_row (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
      (originalNorm p : ZMod p) - nativeBpair p hp =
    2 * residueHom p (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp) +
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 * universalDunivP p +
          actualLegendreJacobi p * properLegendreJacobi p *
            (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p / 6) ^ 2 / 1000 - nativeBpair p hp := by
  have hr := ActualJointGreen.actual_residual_finite_log_source p hp
  have hc := ActualCauchyTbarAttachment.actual_SB82e p hp
  have hs := ActualJointGreen.actual_Tbar_residual_QO p hp
  have h0 := ActualNormCrossAttachment.actual_proper_band_QO p hp
  have hu : Ij p 1 (quadraticInverse (actualRankDividedField p (by omega) ^ 2)) =
      Ij p 1 (actualNormXi p hp) + 81 * fieldHarmonic p (p / 6) ^ 2 / 125 := by
    have he : quadraticInverse (actualRankDividedField p (by omega) ^ 2) =
        actualNormXi p hp + quadraticInverse (X ^ (2 * p) * properLegendreJacobi p ^ 2) := by
      unfold actualNormXi
      rw [quadraticInverse_sub_local]
      ring
    rw [he, Ij_add, ActualNormCrossAttachment.actual_proper_band_I1 p hp]
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  have h125 : (125 : ZMod p) ≠ 0 := by
    rw [show (125 : ZMod p) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have h1000 : (1000 : ZMod p) ≠ 0 := by
    rw [show (1000 : ZMod p) = 2 ^ 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 3 h5)
  linear_combination (norm := (field_simp [h3, h24, h125, h1000]; ring))
    hr + 2 * hc + (1 / 3 : ZMod p) * hs - (1 / 3 : ZMod p) * h0 - (5 / 24 : ZMod p) * hu

/-- SB98--101 attach to the native row with both common traces still explicit. -/
theorem actual_coupled_common_trace_row (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
      (originalNorm p : ZMod p) - nativeBpair p hp =
    (2 / 3 : ZMod p) *
      (residueHom p (vBalancedDividedIntegral p hp) +
        residueHom p (commonSourceTraceIntegral p hp) + residueHom p (balancedTraceIntegral p hp) -
        ActualDeltaUNextSource.QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) -
        residueHom p (periodCarryIntegral p hp) -
        (1 / 2 : ZMod p) * residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) +
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 * universalDunivP p +
          actualLegendreJacobi p * properLegendreJacobi p *
            (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p / 6) ^ 2 / 1000 - nativeBpair p hp := by
  rw [actual_direct_coupled_row p hp]
  have hc := actual_coupled_trace_field_source p hp
  rw [actual_SB101_field_source p hp] at hc
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  linear_combination (norm := (field_simp [h2, h3]; ring)) (2 / 3 : ZMod p) * hc

end WPFieldAssembly.ActualBpairContraction
