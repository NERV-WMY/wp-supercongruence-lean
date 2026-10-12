import WPPolynomialSimplePole
import WPActualNativeCMSource

open scoped Polynomial
open Polynomial WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualCubicGauge WPActualCubicHasse WPActualNativeCubicJet WPActualNativeCubicInvariant
  WPActualNativeCubicPrimitive WPActualNativeCubicTransport WPActualNativeCMParity
  WPActualNativeCMLogValues WPActualNativeCMSource WPPolynomialSimplePole
  WPActualNativeJetODE WPActualNativeHasse

namespace WPActualNativeCMFinitePart

noncomputable def nativeCMRational (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  (nativeJetField p).eval₂ RatFunc.C
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) /
    (nativeField p (p / 6)).eval₂ RatFunc.C
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3)

theorem cubicH_center (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicH : (ZMod p)[X]).eval (1 / 2) = 5 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  simp [cubicH]
  field_simp
  ring

theorem cubicD_center (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicD : (ZMod p)[X]).eval (1 / 2) = -11 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  simp [cubicD]
  field_simp
  ring

theorem cubicA_center (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicA : (ZMod p)[X]).eval (1 / 2) = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  simp [cubicA]
  field_simp
  ring

theorem nativeRatioNumerator_center (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeRatioNumerator p).eval (1 / 2) =
      5 * (5 : ZMod p) ^ ((p - 1) / 2) * (nativeJetField p).eval (4 / 125) := by
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  rw [nativeRatioNumerator, eval_mul, nativeCubicJet,
    cubicLift_point_eval ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p)
      (1 / 2) (nativeJetField_degree p) (by omega) (by rw [cubicH_center p hp]; exact h5),
    cubicH_center p hp, cubicA_center p hp,
    show (5 : ZMod p) ^ 3 = 125 by ring]
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hN : 3 * ((p - 1) / 2) + 1 = p + (p - 1) / 2 := by omega
  have he : (5 : ZMod p) * 5 ^ (3 * ((p - 1) / 2)) =
      5 * 5 ^ ((p - 1) / 2) := by
    rw [← pow_succ', hN, pow_add, ZMod.pow_card]
  rw [← mul_assoc, he]

theorem nativeCM_odd_denominator (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (nativeCMDenominator p).eval (1 / 2) = 0 ∧
      (nativeCMDenominator p).derivative.eval (1 / 2) =
        5 * (actualGauss p).derivative.eval (1 / 2) ∧
      (nativeCMDenominator p).derivative.derivative.eval (1 / 2) = 0 := by
  rw [nativeCMDenominator_second_derivative, nativeCMDenominator_derivative]
  simp only [nativeCMDenominator, eval_mul, eval_pow, cubicH_center p hp, ZMod.pow_card,
    actualGauss_CM_odd_zero p hp hk, actualGauss_CM_odd_second_derivative_zero p hp hk,
    mul_zero, and_self]

theorem nativeCM_odd_numerator_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (nativeCMNumerator p).derivative.eval (1 / 2) =
      (nativeCMRegularNumerator p).eval (1 / 2) *
        (actualGauss p).derivative.eval (1 / 2) := by
  rw [nativeCMNumerator_derivative]
  simp only [eval_add, eval_mul, eval_pow, eval_ofNat,
    properGauss_CM_odd_derivative_zero p hp hk, actualGauss_CM_odd_zero p hp hk,
    mul_zero, zero_add]

theorem nativeCM_odd_pole_coefficient (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (nativeCMNumerator p).eval (1 / 2) /
        (nativeCMDenominator p).derivative.eval (1 / 2) =
      44 / (5 * ((actualGauss p).derivative.eval (1 / 2)) ^ 2) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have hY := actualGauss_CM_odd_derivative_ne_zero p hp hk
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2))
    (actual_properGauss_wronskian p hp)
  simp only [eval_mul, eval_ofNat, eval_X, eval_sub, eval_one, eval_pow,
    actualGauss_CM_odd_zero p hp hk, zero_mul, zero_pow (by decide : 2 ≠ 0)] at he
  have hw : (actualGauss p).derivative.eval (1 / 2) *
      (properGauss p).eval (1 / 2) = -2 := by
    field_simp at he
    linear_combination -he
  rw [(nativeCM_odd_denominator p hp hk).2.1]
  simp only [nativeCMNumerator, eval_add, eval_mul, eval_ofNat, eval_pow,
    cubicD_center p hp, ZMod.pow_card, actualGauss_CM_odd_zero p hp hk, mul_zero, add_zero]
  field_simp
  linear_combination -22 * hw

theorem nativeCM_odd_pole_nonzero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (44 : ZMod p) / (5 * ((actualGauss p).derivative.eval (1 / 2)) ^ 2) ≠ 0 := by
  have h4 : (4 : ZMod p) ≠ 0 := small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h11 : (11 : ZMod p) ≠ 0 := small_cast_ne_zero p 11 (by omega) (by omega)
  have h44 : (44 : ZMod p) ≠ 0 := by
    rw [show (44 : ZMod p) = 4 * 11 by ring]
    exact mul_ne_zero h4 h11
  exact div_ne_zero h44 (mul_ne_zero h5
    (pow_ne_zero 2 (actualGauss_CM_odd_derivative_ne_zero p hp hk)))

/-- Actual odd-degree quotient, its nonzero simple pole, and its original regular constant. -/
theorem actual_native_CM_odd_finite_part (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    ∃ U R : (ZMod p)[X], U.eval (1 / 2) ≠ 0 ∧
      nativeCMRational p =
        RatFunc.C (44 / (5 * ((actualGauss p).derivative.eval (1 / 2)) ^ 2)) /
          algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (X - C (1 / 2)) +
        algebraMap (ZMod p)[X] (RatFunc (ZMod p)) R /
          algebraMap (ZMod p)[X] (RatFunc (ZMod p)) U ∧
      R.eval (1 / 2) / U.eval (1 / 2) = -2 * fieldHarmonic p (p / 6) +
        3 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have hY := actualGauss_CM_odd_derivative_ne_zero p hp hk
  have hd := nativeCM_odd_denominator p hp hk
  have hD : (nativeCMDenominator p).derivative.eval (1 / 2) ≠ 0 := by
    rw [hd.2.1]
    exact mul_ne_zero h5 hY
  obtain ⟨U, R, _, hU, hsource, hvalue⟩ := simple_pole_decomposition
    (nativeCMNumerator p) (nativeCMDenominator p) (1 / 2) h2 hd.1 hD
  refine ⟨U, R, hU, ?_, ?_⟩
  · rw [nativeCM_odd_pole_coefficient p hp hk] at hsource
    exact (nativeCM_source_quotient p hp).trans hsource
  · rw [hd.2.2, mul_zero, zero_div, sub_zero,
      nativeCM_odd_numerator_derivative p hp hk, hd.2.1] at hvalue
    have hv : R.eval (1 / 2) / U.eval (1 / 2) =
        (nativeCMRegularNumerator p).eval (1 / 2) / 5 := by
      rw [hvalue]
      field_simp
    rw [hv, nativeCMRegularNumerator_center p hp, actual_native_CM_source_constant p hp]

theorem actual_native_CM_even_regular_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Even (p / 3)) :
    (nativeCMNumerator p).eval (1 / 2) / (nativeCMDenominator p).eval (1 / 2) =
      -2 * fieldHarmonic p (p / 6) +
        3 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have hY := actualGauss_CM_even_ne_zero p hp hk
  simp only [nativeCMNumerator, nativeCMDenominator, eval_add, eval_mul, eval_ofNat,
    eval_pow, properGauss_CM_even_zero p hp hk, mul_zero, zero_add,
    cubicH_center p hp, ZMod.pow_card]
  calc
    _ = (nativeCMRegularNumerator p).eval (1 / 2) / 5 := by field_simp
    _ = _ := (nativeCMRegularNumerator_center p hp).trans
      (actual_native_CM_source_constant p hp)

/-- The actual original J_N/F_d value at the ordinary CM point. -/
theorem actual_native_CM_even_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Even (p / 3)) :
    (nativeJetField p).eval (4 / 125) / (nativeField p (p / 6)).eval (4 / 125) =
      -2 * fieldHarmonic p (p / 6) +
        3 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have hY := actualGauss_CM_even_ne_zero p hp hk
  have hF := actual_cubic_CM_hasse p hp
  have hf : (nativeField p (p / 6)).eval (4 / 125) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hF
    exact (pow_ne_zero 2 hY) hF.symm
  have hW := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2))
    (nativeCMNumerator_factor p hp)
  rw [nativeRatioNumerator_center p hp] at hW
  simp only [nativeCMNumerator, eval_mul, eval_add, eval_ofNat, eval_pow,
    properGauss_CM_even_zero p hp hk, mul_zero, zero_add] at hW
  have he : 5 * (nativeJetField p).eval (4 / 125) =
      (nativeField p (p / 6)).eval (4 / 125) *
        (nativeCMRegularNumerator p).eval (1 / 2) := by
    apply mul_left_cancel₀ (pow_ne_zero ((p - 1) / 2) h5)
    linear_combination hW - (nativeCMRegularNumerator p).eval (1 / 2) * hF
  calc
    _ = (nativeCMRegularNumerator p).eval (1 / 2) / 5 := by
      field_simp
      linear_combination he
    _ = _ := (nativeCMRegularNumerator_center p hp).trans
      (actual_native_CM_source_constant p hp)

end WPActualNativeCMFinitePart
