import WPFieldAssembly.NativeClosureScalarSource
import WPFieldAssembly.ActualBpairEuler

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource WPPIntegralReduction WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualGaussBottom
open WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.ResidualProjection WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.NativeScalarRows

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000

/-- The squared literal log is carried through the original even quadratic inverse. -/
theorem actual_QO_log_square_native (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          (WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))) ^ 2) =
      Ij p 0 (actualF p * actualLogMinusH p ^ 2) := by
  let A : (ZMod p)[X] := WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))
  have hA : A.comp (-X) = A := by
    simp only [A, sub_comp, WPFiniteNC122Residue.LPsrc_even, C_comp]
  have hA2 : (A ^ 2).comp (-X) = A ^ 2 := by rw [pow_comp, hA]
  have hqi : quadraticInverse (A ^ 2) = actualLogMinusH p ^ 2 := by
    rw [pow_two, quadraticInverse_mul_even p hp A A hA hA,
      actual_log_minus_h_native p, ← pow_two]
  unfold ActualDeltaUNextSource.QO
  change Ij p 0 (quadraticInverse (actualLegendreJacobi p ^ 2 * A ^ 2)) = _
  rw [quadraticInverse_mul_even p hp _ _ (actual_Y_square_even p hp) hA2, hqi]
  rfl

/-- The universal normalization is the actual bracket projection, with its full log square. -/
theorem actual_QO_universal_bracket (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    -(2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) -
      (1 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p ^ 2 *
          (WPFiniteKSource.LPsrc p - Polynomial.C (fieldHarmonic p (p / 6))) ^ 2) =
      Ij p 0 (actualF p *
        WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p)) := by
  rw [actual_Ksrc_product_attachment p hp, actual_QO_log_square_native p hp]
  have he : actualF p *
      WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p) =
      Polynomial.C (-2 / 3 : ZMod p) * (actualF p * actualKNative p) -
      Polynomial.C (1 / 3 : ZMod p) * (actualF p * actualLogMinusH p ^ 2) +
      Polynomial.C (fieldHarmonic p (p / 6) ^ 2 / 3) * actualF p := by
    rw [actual_bracket_native p hp]
    ring
  have hF : Ij p 0 (actualF p) = 0 :=
    low_correction_both_projections_zero p hp _ (actualF_degree p hp) 0
  rw [he]
  simp only [Ij_add, Ij_sub_local, Ij_C_mul, hF, mul_zero, add_zero]
  ring

/-- The entire common trace reaches GKQ through the actual Euler bracket.
The original norm's I1 projection and the proper product remain explicit. -/
theorem actualCommonTraceScalar_GKQ_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCommonTraceScalar p hp =
      (2 / 3 : ZMod p) *
        (residueHom p (vBalancedDividedIntegral p hp) +
          residueHom p (commonSourceTraceIntegral p hp) +
          residueHom p (balancedTraceIntegral p hp) -
          residueHom p (periodCarryIntegral p hp) -
          (1 / 2 : ZMod p) *
            residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) +
      NativeScalarRows.actualGKQ (K := ZMod p) p -
      ((ActualGreenResidue.Hpull p).toLaurent *
        D (substituteOver
          (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p))
          (originalQ : (ZMod p)[T;T⁻¹]))).coeff (-1) +
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p / 6) ^ 2 / 1000 := by
  have he := actual_QO_universal_bracket p hp
  rw [actual_bracket_Euler_attachment p hp] at he
  rw [actualCommonTraceScalar_without_Duniv p hp]
  linear_combination he

/-- This GKQ source still belongs to the same NC77 scalar and its original native Bpair. -/
theorem actualNC77Scalar_GKQ_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
      (2 / 3 : ZMod p) *
        (residueHom p (vBalancedDividedIntegral p hp) +
          residueHom p (commonSourceTraceIntegral p hp) +
          residueHom p (balancedTraceIntegral p hp) -
          residueHom p (periodCarryIntegral p hp) -
          (1 / 2 : ZMod p) *
            residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) +
      NativeScalarRows.actualGKQ (K := ZMod p) p -
      ((ActualGreenResidue.Hpull p).toLaurent *
        D (substituteOver
          (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h (K := ZMod p) p))
          (originalQ : (ZMod p)[T;T⁻¹]))).coeff (-1) +
      (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
        (actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
      (5 / 24 : ZMod p) * Ij p 1 (actualNormXi p hp) -
      103 * fieldHarmonic p (p / 6) ^ 2 / 1000 - NativeScalarRows.nativeBpair p hp := by
  rw [actualNC77Scalar_common_trace p hp, actualCommonTraceScalar_GKQ_source p hp]

end WPFieldAssembly.ActualBpairContraction
