import WPFieldAssembly.ActualNormCrossAttachment
import WPFieldAssembly.ActualFirstGreen

open scoped Polynomial
open Polynomial

set_option maxHeartbeats 1600000

namespace WPFieldAssembly.ActualBpairContraction

open NativeQuadraticInverse NativeOriginalResidues ActualNormCrossAttachment ActualLowEuler
  WPActualRankTwoLegendreField WPActualRankTwoComparison WPActualNativeJetODE
  WPActualNativeJacobiJet WPFiniteJHighCoefficient WPFiniteCubicLog WPFiniteLVSource
  WPActualRankTwoProper WPActualRankTwoResidueSource

/-- Equality after the actual degree-two conic detects polynomial equality. -/
theorem conic_comp_injective (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P Q : (ZMod p)[X]) (he : P.comp conic = Q.comp conic) : P = Q := by
  have hd : (conic : (ZMod p)[X]).natDegree = 2 := by
    unfold conic
    change (Polynomial.C (5 : ZMod p) * X ^ 2 - 1).natDegree = 2
    compute_degree
    exact WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  exact ConicKernel.comp_injective_nonconstant
    conic (by rw [hd]; norm_num) he

/-- The original native logarithm pulls back to the complete literal LV source. -/
theorem actual_log_V_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogNative p).comp (WPHasseIntegralTransport.fieldV p) =
      (WPFiniteLVSource.LV p : (ZMod p)[X]) := by
  apply conic_comp_injective p hp
  calc
    _ = (actualLogNative p).comp (1 - Tc ^ 2) := by
      rw [comp_assoc, actual_native_V_conic p hp]
    _ = ((actualLogNative p).comp (1 - X ^ 2)).comp Tc := by
      rw [comp_assoc]
      congr 1
      simp only [sub_comp, one_comp, pow_comp, X_comp]
    _ = (WPFiniteKSource.LPsrc p).comp Tc := by
      rw [show (actualLogNative p).comp (1 - X ^ 2) = WPFiniteKSource.LPsrc p from
        even_native_attachment p hp _ (WPFiniteNC122Residue.LPsrc_even p)]
    _ = _ := (WPFiniteLVSource.LV_conic p hp).symm

/-- The whole native jet is twice actual Sigma, including its upper coefficients. -/
theorem actual_jet_twice_Sigma (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeJetField p = 2 * actualSigmaNative p hp := by
  have h := congrArg quadraticInverse (actual_native_Jacobi_jet p hp)
  change quadraticInverse ((nativeJetField p).comp (1 - X ^ 2)) =
    quadraticInverse (2 * actualLegendreJacobi p * actualRankDividedField p (by omega)) at h
  have hm : (2 : (ZMod p)[X]) * actualLegendreJacobi p *
      actualRankDividedField p (by omega) =
    2 * (actualLegendreJacobi p * actualRankDividedField p (by omega)) := by ring
  rw [quadraticInverse_quadratic, hm] at h
  have hs := quadraticInverse_nat_mul_local 2
    (actualLegendreJacobi p * actualRankDividedField p (by omega))
  simp only [Nat.cast_ofNat] at hs
  rw [hs] at h
  exact h

/-- The actual Sigma source retains the entire Frobenius carrier. -/
theorem actual_Sigma_V_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p) =
      (actualF p).comp (WPHasseIntegralTransport.fieldV p) *
        ((WPFiniteLVSource.LV p : (ZMod p)[X]) -
          Polynomial.C (WPActualGaussBottom.fieldHarmonic p (p/6))) -
      (4 * X ^ p - 11) * ActualFirstGreen.CB p := by
  let c : (ZMod p)[X] := 4 * X ^ 2 - 3
  have h5 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat] at h5
  have hp4 : (4 : (ZMod p)[X]) ^ p = 4 := by
    change (Polynomial.C (4 : ZMod p)) ^ p = Polynomial.C 4
    rw [← Polynomial.C_pow, ZMod.pow_card]
  have hp5 : (5 : (ZMod p)[X]) ^ p = 5 := by
    change (Polynomial.C (5 : ZMod p)) ^ p = Polynomial.C 5
    rw [← Polynomial.C_pow, ZMod.pow_card]
  have hp11 : (11 : (ZMod p)[X]) ^ p = 11 := by
    change (Polynomial.C (11 : ZMod p)) ^ p = Polynomial.C 11
    rw [← Polynomial.C_pow, ZMod.pow_card]
  have hu5 : (5 : (ZMod p)[X]) * Polynomial.C (1 / 5 : ZMod p) = 1 := by
    change Polynomial.C (5 : ZMod p) * Polynomial.C (1 / 5 : ZMod p) = Polynomial.C 1
    rw [← Polynomial.C_mul, mul_one_div_cancel h5]
  have hTc : (Tc : (ZMod p)[X]) = X * c := by dsimp only [Tc, c]; ring
  have hbase : (4 * X - 11 : (ZMod p)[X]).comp conic = 5 * c := by
    simp only [conic, mul_comp, sub_comp, ofNat_comp, X_comp]
    dsimp only [c]
    ring
  have hbp : (4 * X ^ p - 11 : (ZMod p)[X]).comp conic = 5 * c ^ p := by
    calc
      _ = ((4 * X - 11 : (ZMod p)[X]) ^ p).comp conic := by
        rw [sub_pow_char, mul_pow, hp4, hp11]
      _ = ((4 * X - 11 : (ZMod p)[X]).comp conic) ^ p := by rw [pow_comp]
      _ = (5 * c) ^ p := by rw [hbase]
      _ = _ := by rw [mul_pow, hp5]
  have hcarrier : ((4 * X ^ p - 11) * ActualFirstGreen.CB p).comp conic =
      Tc ^ p * (actualLegendreJacobi p).comp Tc * (properLegendreJacobi p).comp Tc := by
    rw [mul_comp, hbp, (ActualFirstGreen.actual_carrier_pullbacks p hp).1]
    simp only [ActualFirstGreen.CBt, ActualFirstGreen.B, mul_comp]
    calc
      _ = (5 * Polynomial.C (1 / 5 : ZMod p)) * (X * c) ^ p *
          (actualLegendreJacobi p).comp Tc * (properLegendreJacobi p).comp Tc := by
        rw [mul_pow]
        ring
      _ = _ := by rw [hu5, one_mul, ← hTc]
  have hF : ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).comp conic =
      (actualLegendreJacobi p).comp Tc ^ 2 := by
    calc
      _ = (actualF p).comp (1 - Tc ^ 2) := by
        rw [comp_assoc, actual_native_V_conic p hp]
      _ = ((actualF p).comp (1 - X ^ 2)).comp Tc := by
        rw [comp_assoc]
        congr 1
        simp only [sub_comp, one_comp, pow_comp, X_comp]
      _ = (actualLegendreJacobi p ^ 2).comp Tc := by
        rw [show (actualF p).comp (1 - X ^ 2) = actualLegendreJacobi p ^ 2 from
          even_native_attachment p hp _ (actual_Y_square_even p hp)]
      _ = _ := by rw [pow_comp]
  have hj := actual_native_V_conic_jet p hp
  rw [actual_jet_twice_Sigma p hp] at hj
  simp only [mul_comp, Nat.cast_ofNat, ofNat_comp] at hj
  apply conic_comp_injective p hp
  rw [sub_comp, mul_comp, hF, sub_comp, C_comp, hcarrier]
  have h2 : (2 : (ZMod p)[X]) ≠ 0 := Polynomial.C_ne_zero.mpr
    (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
  apply mul_left_cancel₀ h2
  linear_combination hj

end WPFieldAssembly.ActualBpairContraction
