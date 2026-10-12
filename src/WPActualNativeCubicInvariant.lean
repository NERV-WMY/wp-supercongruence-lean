import WPActualNativeCubicPrimitive

open scoped Polynomial
open Polynomial WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualCubicGauge WPActualCubicHasse WPActualNativeCubicJet WPActualNativeCubicTransport
  WPActualNativeCubicPrimitive WPActualNativeFirstIntegral

namespace WPActualNativeCubicInvariant

noncomputable def nativeRatioRemainder (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  nativeRatioNumerator p - 2 * cubicD ^ p * properGauss p * actualGauss p -
    nativeUnitPrimitive p * actualGauss p ^ 2

theorem nativeRatioRemainder_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeRatioRemainder p).derivative * actualGauss p -
      2 * nativeRatioRemainder p * (actualGauss p).derivative = 0 := by
  have hD : ((cubicD : (ZMod p)[X]) ^ p).derivative = 0 := by
    rw [cubicD_frobenius]
    simp [derivative_X_pow, Nat.cast_mul]
  have he : X * (1 - X) * ((nativeRatioRemainder p).derivative * actualGauss p -
      2 * nativeRatioRemainder p * (actualGauss p).derivative) = 0 := by
    simp only [nativeRatioRemainder, derivative_sub, derivative_mul, derivative_ofNat,
      derivative_sq, C_ofNat, hD, zero_mul, zero_add]
    linear_combination actual_native_cubic_transport p hp -
      cubicD ^ p * actualGauss p * actual_properGauss_wronskian p hp -
      actualGauss p ^ 3 * nativeUnitPrimitive_source p hp
  have hr : (X * (1 - X) : (ZMod p)[X]) ≠ 0 :=
    mul_ne_zero X_ne_zero (sub_ne_zero.mpr (by simpa using (X_ne_C (1 : ZMod p)).symm))
  exact (mul_eq_zero.mp he).resolve_left hr

theorem nativeRatioRemainder_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeRatioRemainder p).natDegree ≤ 2 * p + 2 * (p / 3) - 1 := by
  have hD : (cubicD : (ZMod p)[X]).natDegree ≤ 2 := by unfold cubicD; compute_degree
  have hterm := natDegree_mul_le_of_le
    (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (power_degree_bound (cubicD : (ZMod p)[X]) 2 p hD))
    (properGauss_degree p hp)
  have htermY := natDegree_mul_le_of_le hterm (actualGauss_degree p)
  have hUY := natDegree_mul_le_of_le (nativeUnitPrimitive_degree p)
    (power_degree_bound (actualGauss p) (p / 3) 2 (actualGauss_degree p))
  have hd := natDegree_sub_le_of_le
    (natDegree_sub_le_of_le (nativeRatioNumerator_degree p (by omega)) htermY) hUY
  change (nativeRatioRemainder p).natDegree ≤
    max (max (2 * p - 1) ((0 + p * 2 + (p / 3 - 1)) + p / 3))
      ((2 * p - 1) + 2 * (p / 3)) at hd
  exact hd.trans (by omega)

theorem actualGauss_ne_zero (p : ℕ) [Fact p.Prime] : actualGauss p ≠ 0 := by
  intro hz
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
  simp [actualGauss_origin] at he

/-- The original complete source has only a bounded Frobenius ambiguity. -/
theorem nativeRatioRemainder_factor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ K0 : (ZMod p)[X], nativeRatioRemainder p = actualGauss p ^ 2 * K0 ∧
      K0.derivative = 0 ∧ K0.natDegree < 2 * p := by
  obtain ⟨K0, hfactor, hderiv⟩ := proper_wronskian_square_division
    (actualGauss p) (properGauss p) (nativeRatioRemainder p)
    (actualGauss_ne_zero p) (actual_properGauss_wronskian p hp)
    (nativeRatioRemainder_source p hp)
  refine ⟨K0, hfactor, hderiv, ?_⟩
  by_cases hz : K0 = 0
  · simp only [hz, natDegree_zero]
    omega
  · have hd := nativeRatioRemainder_degree p hp
    rw [hfactor, natDegree_mul (pow_ne_zero 2 (actualGauss_ne_zero p)) hz,
      natDegree_pow, actualGauss_exact_degree p hp] at hd
    omega

theorem derivative_zero_two_digits (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdeg : P.natDegree < 2 * p) (hsource : P.derivative = 0) :
    P = C (P.coeff 0) + C (P.coeff p) * X ^ p := by
  have hp := (Fact.out : p.Prime).pos
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [coeff_C, show 0 ≠ p by omega]
  by_cases hnp : n = p
  · subst n
    simp [coeff_C, hn0]
  have hnz : P.coeff n = 0 := by
    by_cases hn : n < 2 * p
    · have hu : (n : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        rintro ⟨m, hm⟩
        have hmlt : m < 2 := by nlinarith
        interval_cases m <;> simp_all
      have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (n - 1)) hsource
      rw [coeff_derivative, coeff_zero, ← Nat.cast_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ n)] at hc
      exact (mul_eq_zero.mp hc).resolve_right hu
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_C, hnz, hn0, hnp]

theorem properGauss_endpoint_product (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properGauss p).eval 1 * (actualGauss p).eval 1 = -fieldHarmonic p (p / 3) := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) (properGauss_reflection p hp)
  simp only [eval_comp, eval_sub, eval_one, eval_X, sub_zero, eval_mul,
    eval_neg, eval_pow, properGauss_origin, eval_one] at he
  rw [he, actualGauss_endpoint]
  have hs := negative_power_square (K := ZMod p) (p / 3)
  linear_combination -fieldHarmonic p (p / 3) * hs

theorem nativeRatioRemainder_origin (p : ℕ) [Fact p.Prime] :
    (nativeRatioRemainder p).eval 0 = -2 * fieldHarmonic p (p / 3) := by
  simp [nativeRatioRemainder, nativeRatioNumerator_origin, nativeUnitPrimitive_origin,
    actualGauss_origin, properGauss_origin, cubicD]

theorem nativeRatioRemainder_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeRatioRemainder p).eval 1 =
      -54 * fieldHarmonic p (p / 3) - (nativeUnitPrimitive p).eval 1 := by
  have hs := negative_power_square (K := ZMod p) (p / 3)
  have hD : (cubicD : (ZMod p)[X]).eval 1 = -27 := by norm_num [cubicD]
  have hY : ((actualGauss p).eval 1) ^ 2 = 1 := by rw [actualGauss_endpoint]; exact hs
  have hw := properGauss_endpoint_product p hp
  simp only [nativeRatioRemainder, eval_sub, eval_mul, eval_ofNat, eval_pow,
    nativeRatioNumerator_endpoint p hp, hD, ZMod.pow_card, hY]
  linear_combination 54 * hw

/-- Exact original native numerator, with both endpoint constants and every high coefficient fixed. -/
theorem actual_native_ratio_numerator_formula (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeRatioNumerator p = 2 * cubicD ^ p * properGauss p * actualGauss p +
      nativeUnitPrimitive p * actualGauss p ^ 2 + actualGauss p ^ 2 *
        (C (-2 * fieldHarmonic p (p / 3)) +
          C (-52 * fieldHarmonic p (p / 3) - (nativeUnitPrimitive p).eval 1) * X ^ p) := by
  obtain ⟨K0, hfactor, hderiv, hdegree⟩ := nativeRatioRemainder_factor p hp
  have hK := derivative_zero_two_digits p K0 hdegree hderiv
  have h0 := congrArg (fun P : (ZMod p)[X] => P.eval 0) hfactor
  rw [nativeRatioRemainder_origin, eval_mul, eval_pow, actualGauss_origin,
    one_pow, one_mul, hK] at h0
  simp only [eval_add, eval_C, eval_mul, eval_pow, eval_X,
    zero_pow (by omega : p ≠ 0), mul_zero, add_zero] at h0
  have h1 := congrArg (fun P : (ZMod p)[X] => P.eval 1) hfactor
  rw [nativeRatioRemainder_endpoint p hp, eval_mul, eval_pow, actualGauss_endpoint,
    negative_power_square, one_mul, hK] at h1
  simp only [eval_add, eval_C, eval_mul, eval_pow, eval_X, one_pow, mul_one] at h1
  have hc : K0.coeff p = -52 * fieldHarmonic p (p / 3) - (nativeUnitPrimitive p).eval 1 := by
    linear_combination -h1 + h0
  rw [hK, ← h0, hc] at hfactor
  unfold nativeRatioRemainder at hfactor
  linear_combination hfactor

end WPActualNativeCubicInvariant
