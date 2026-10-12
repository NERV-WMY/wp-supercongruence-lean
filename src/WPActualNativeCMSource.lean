import WPActualNativeCMParity
import WPActualNativeCMLogValues

open scoped Polynomial
open Polynomial WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualCubicGauge WPActualCubicHasse WPActualNativeCubicJet WPActualNativeCubicInvariant
  WPActualNativeCubicPrimitive WPActualNativeCubicTransport WPActualNativeCMParity
  WPActualNativeCMLogValues WPActualNativeJetODE WPActualNativeHasse

namespace WPActualNativeCMSource

noncomputable def nativeCMRegularNumerator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  nativeUnitPrimitive p + C (-2 * fieldHarmonic p (p / 3)) +
    C (-52 * fieldHarmonic p (p / 3) - (nativeUnitPrimitive p).eval 1) * X ^ p

noncomputable def nativeCMNumerator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  2 * cubicD ^ p * properGauss p + nativeCMRegularNumerator p * actualGauss p

noncomputable def nativeCMDenominator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  cubicH ^ p * actualGauss p

theorem nativeCMNumerator_factor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeRatioNumerator p = actualGauss p * nativeCMNumerator p := by
  rw [actual_native_ratio_numerator_formula p hp]
  simp only [nativeCMNumerator, nativeCMRegularNumerator]
  ring

theorem nativeCM_source_quotient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeJetField p).eval₂ RatFunc.C
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) /
      (nativeField p (p / 6)).eval₂ RatFunc.C
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) =
      algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeCMNumerator p) /
        algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeCMDenominator p) := by
  have hY : actualGauss p ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
    simp [actualGauss_origin] at he
  have hE := RatFunc.algebraMap_ne_zero hY
  have hH := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := ZMod p))
  rw [← nativeRatioNumerator_quotient p hp, nativeCMNumerator_factor p hp,
    nativeCMDenominator, map_mul, map_mul, map_pow, map_pow]
  field_simp

theorem nativeCMRegularNumerator_center (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeCMRegularNumerator p).eval (1 / 2) / 5 = nativeCMSourceConstant p := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  unfold nativeCMRegularNumerator nativeCMSourceConstant
  simp only [eval_add, eval_C, eval_mul, eval_pow, eval_X, ZMod.pow_card]
  field_simp
  ring

theorem nativeCMDenominator_derivative (p : ℕ) [Fact p.Prime] :
    (nativeCMDenominator p).derivative = cubicH ^ p * (actualGauss p).derivative := by
  simp [nativeCMDenominator, derivative_mul, derivative_pow]

theorem nativeCMDenominator_second_derivative (p : ℕ) [Fact p.Prime] :
    (nativeCMDenominator p).derivative.derivative =
      cubicH ^ p * (actualGauss p).derivative.derivative := by
  rw [nativeCMDenominator_derivative]
  simp [derivative_mul, derivative_pow]

theorem nativeCMNumerator_derivative (p : ℕ) [Fact p.Prime] :
    (nativeCMNumerator p).derivative = 2 * cubicD ^ p * (properGauss p).derivative +
      (nativeCMRegularNumerator p).derivative * actualGauss p +
        nativeCMRegularNumerator p * (actualGauss p).derivative := by
  simp [nativeCMNumerator, derivative_add, derivative_mul, derivative_pow]
  ring

end WPActualNativeCMSource
