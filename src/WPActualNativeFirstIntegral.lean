import WPActualNativeJetODE
import WPHasseCubicSource

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeJetODE WPHasseCubicSource

namespace WPActualNativeFirstIntegral

/-- The native symmetric-square discriminant, with its fixed denominators cleared. -/
noncomputable def nativeDiscriminant {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  72 * X * (1 - X) * (2 * F * F.derivative.derivative - F.derivative ^ 2) +
    72 * (2 - 3 * X) * F * F.derivative - 10 * F ^ 2

theorem nativeDiscriminant_source {K : Type*} [CommRing K] (F : K[X]) :
    X * (nativeDiscriminant F).derivative + nativeDiscriminant F =
      2 * F * regularNative F := by
  simp [nativeDiscriminant, regularNative, derivative_mul, derivative_pow_succ]
  ring

noncomputable def forcedRegular {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  216 * X * (1 - X) * F.derivative.derivative +
    (216 - 432 * X) * F.derivative - 46 * F

theorem forcedOperator_eq_X_regular {K : Type*} [CommRing K] (F : K[X]) :
    forcedOperator F = X * forcedRegular F := by
  simp [forcedOperator, forcedRegular, theta, derivative_mul]
  ring

noncomputable def nativeBilinear {K : Type*} [CommRing K] (F J : K[X]) : K[X] :=
  X * (F * J.derivative - F.derivative * J) + F ^ 2

noncomputable def bilinearOperator {K : Type*} [CommRing K] (F B : K[X]) : K[X] :=
  72 * X * (1 - X) * F * B.derivative.derivative +
    ((72 - 180 * X) * F - 72 * X * (1 - X) * F.derivative) * B.derivative +
    (-46 * F + 72 * (1 - X) * F.derivative +
      72 * X * (1 - X) * F.derivative.derivative) * B

/-- Universal finite source identity for the actual quotient-jet Wronskian. -/
theorem nativeBilinear_source {K : Type*} [CommRing K] (F J : K[X]) :
    bilinearOperator F (nativeBilinear F J) =
      F ^ 2 * (regularNative J + forcedRegular F) - F * J * regularNative F := by
  simp [bilinearOperator, nativeBilinear, regularNative, forcedRegular,
    derivative_mul, derivative_pow_succ]
  ring

theorem bilinear_half_power_source {K : Type*} [CommRing K] (F H : K[X]) :
    bilinearOperator F (F * H) - nativeDiscriminant F * H =
      36 * F * (X * F.derivative + F) * (2 * (1 - X) * H.derivative - H) +
        36 * X * F ^ 2 * (2 * (1 - X) * H.derivative.derivative - 3 * H.derivative) := by
  simp [bilinearOperator, nativeDiscriminant, derivative_mul]
  ring

noncomputable def bilinearE2 {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  72 * (1 - X) * F
noncomputable def bilinearE1 {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  -108 * X * F - 72 * X * (1 - X) * F.derivative
noncomputable def bilinearE0 {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  X * (-46 * F + 72 * (1 - X) * F.derivative +
    72 * X * (1 - X) * F.derivative.derivative)

theorem bilinearOperator_euler {K : Type*} [CommRing K] (F B : K[X]) :
    regularEuler 0 (bilinearE2 F) (bilinearE1 F) (bilinearE0 F) B =
      X * bilinearOperator F B := by
  simp [regularEuler, bilinearE2, bilinearE1, bilinearE0, bilinearOperator,
    theta, derivative_mul]
  ring

theorem bilinearOperator_sub {K : Type*} [CommRing K] (F A B : K[X]) :
    bilinearOperator F (A - B) = bilinearOperator F A - bilinearOperator F B := by
  simp only [bilinearOperator, derivative_sub]
  ring

/-- Finite degree excludes all nonconstant Frobenius solutions at the regular end. -/
theorem finite_secondEuler_uniqueness (p : ℕ) [Fact p.Prime]
    (E2 E1 E0 P : (ZMod p)[X]) (c : ZMod p) (hc : c ≠ 0)
    (hE2 : E2.coeff 0 = c) (hE1 : E1.coeff 0 = 0) (hE0 : E0.coeff 0 = 0)
    (hdegree : P.natDegree < p) (horigin : P.eval 0 = 0)
    (hODE : regularEuler 0 E2 E1 E0 P = 0) : P = 0 := by
  ext n
  rw [coeff_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact (coeff_zero_eq_eval_zero P).trans horigin
    · by_cases hnp : n < p
      · have hnc : (n : ZMod p) ≠ 0 := by
          rw [ne_eq, ZMod.natCast_eq_zero_iff]
          intro hd
          have hle := Nat.le_of_dvd (by omega : 0 < n) hd
          omega
        have hi := regularEuler_indicial 0 E2 E1 E0 P n ih
        rw [hODE, coeff_zero, hE2, hE1, hE0, coeff_zero] at hi
        have hprod : c * (n : ZMod p) ^ 2 * P.coeff n = 0 := by simpa using hi.symm
        exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc (pow_ne_zero 2 hnc))
      · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem derivative_degree_bound {K : Type*} [CommRing K]
    (F : K[X]) (d : ℕ) (hF : F.natDegree ≤ d) : F.derivative.natDegree ≤ d := by
  exact (natDegree_derivative_le F).trans ((Nat.sub_le _ _).trans hF)

theorem nativeDiscriminant_degree {K : Type*} [CommRing K]
    (F : K[X]) (d : ℕ) (hF : F.natDegree ≤ d) :
    (nativeDiscriminant F).natDegree ≤ 2 * d + 2 := by
  have hD := derivative_degree_bound F d hF
  have hDD := derivative_degree_bound F.derivative d hD
  have h72 : (72 : K[X]).natDegree ≤ 0 := by simp
  have h2 : (2 : K[X]).natDegree ≤ 0 := by simp
  have h3 : (3 : K[X]).natDegree ≤ 0 := by simp
  have h10 : (10 : K[X]).natDegree ≤ 0 := by simp
  have h1 : (1 : K[X]).natDegree ≤ 0 := by simp
  have hX : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
  have hA : (1 - X : K[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le h1 hX
  have hB : (2 - 3 * X : K[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le h2 (natDegree_mul_le_of_le h3 hX)
  have hDS : (F.derivative ^ 2).natDegree ≤ d + d := by
    simpa only [pow_two] using natDegree_mul_le_of_le hD hD
  have hprod : (2 * F * F.derivative.derivative).natDegree ≤ d + d := by
    simpa only [zero_add] using natDegree_mul_le_of_le (natDegree_mul_le_of_le h2 hF) hDD
  have hC : (2 * F * F.derivative.derivative - F.derivative ^ 2).natDegree ≤ d + d := by
    simpa only [max_self] using natDegree_sub_le_of_le hprod hDS
  have hT1 : (72 * X * (1 - X) *
      (2 * F * F.derivative.derivative - F.derivative ^ 2)).natDegree ≤ 2 + (d + d) := by
    simpa using natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le h72 hX) hA) hC
  have hT2 : (72 * (2 - 3 * X) * F * F.derivative).natDegree ≤ 1 + d + d := by
    simpa using natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le h72 hB) hF) hD
  have hT3 : (10 * F ^ 2).natDegree ≤ d + d := by
    simpa only [zero_add, pow_two] using natDegree_mul_le_of_le h10
      (natDegree_mul_le_of_le hF hF)
  unfold nativeDiscriminant
  exact (natDegree_sub_le_of_le (natDegree_add_le_of_le hT1 hT2) hT3).trans (by omega)

theorem nativeBilinear_degree {K : Type*} [CommRing K]
    (F J : K[X]) (d N : ℕ) (hF : F.natDegree ≤ d) (hJ : J.natDegree ≤ N) (hd : d ≤ N) :
    (nativeBilinear F J).natDegree ≤ d + N + 1 := by
  have hDF := derivative_degree_bound F d hF
  have hDJ := derivative_degree_bound J N hJ
  have hW : (F * J.derivative - F.derivative * J).natDegree ≤ d + N := by
    simpa using natDegree_sub_le_of_le (natDegree_mul_le_of_le hF hDJ)
      (natDegree_mul_le_of_le hDF hJ)
  have hT : (X * (F * J.derivative - F.derivative * J)).natDegree ≤ 1 + (d + N) :=
    natDegree_mul_le_of_le (natDegree_X_le (R := K)) hW
  have hS : (F ^ 2).natDegree ≤ d + d := by
    simpa only [pow_two] using natDegree_mul_le_of_le hF hF
  unfold nativeBilinear
  exact (natDegree_add_le_of_le hT hS).trans (by omega)

theorem finite_shiftedEuler_zero (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdegree : P.natDegree + 1 < p) (hODE : X * P.derivative + P = 0) : P = 0 := by
  ext n
  rw [coeff_zero]
  by_cases hn : n ≤ P.natDegree
  · have hnc : ((n : ZMod p) + 1) ≠ 0 := by
      rw [← Nat.cast_add_one, ne_eq, ZMod.natCast_eq_zero_iff]
      intro hd
      have hle := Nat.le_of_dvd (by omega : 0 < n + 1) hd
      omega
    have hi := congrArg (fun Q : (ZMod p)[X] => Q.coeff n) hODE
    change (theta P + P).coeff n = (0 : (ZMod p)[X]).coeff n at hi
    rw [coeff_add, theta_coeff, coeff_zero] at hi
    have hprod : ((n : ZMod p) + 1) * P.coeff n = 0 := by linear_combination hi
    exact (mul_eq_zero.mp hprod).resolve_left hnc
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem actual_nativeDiscriminant_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeDiscriminant (nativeField p (p / 6)) = 0 := by
  apply finite_shiftedEuler_zero p
  · have hd := nativeDiscriminant_degree (nativeField p (p / 6)) (p / 6)
      (actual_native_field_degree p)
    omega
  · rw [nativeDiscriminant_source, actual_native_field_regular_ODE p (by omega), mul_zero]

theorem actual_nativeJetField_regular_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    regularNative (nativeJetField p) + forcedRegular (nativeField p (p / 6)) = 0 := by
  have he := actual_nativeJetField_forced_ODE p hp
  rw [clearedOperator_eq_X_regular, forcedOperator_eq_X_regular] at he
  have hmul : X * (regularNative (nativeJetField p) + forcedRegular (nativeField p (p / 6))) = 0 := by
    rw [mul_add, he]
    ring
  exact (mul_eq_zero.mp hmul).resolve_left X_ne_zero

theorem integer_power_derivative {K : Type*} [CommRing K] (n : ℕ) :
    (1 - X : K[X]) * ((1 - X : K[X]) ^ n).derivative = -C (n : K) * (1 - X) ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [derivative_pow_succ, derivative_sub, derivative_one, derivative_X,
      zero_sub, mul_neg_one, Nat.cast_add, Nat.cast_one]
    ring

theorem actual_halfPower_first_order (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * (1 - X : (ZMod p)[X]) * ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).derivative =
      (1 - X) ^ ((p - 1) / 2) := by
  have hhalf := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hc : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    have hh : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
      have he : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = (p : ZMod p) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
          congrArg (fun n : ℕ => (n : ZMod p)) hhalf
      rw [he, ZMod.natCast_self]
    linear_combination hh
  have hpoly : (2 : (ZMod p)[X]) * C (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    simpa only [map_mul, map_ofNat, map_neg, map_one] using congrArg Polynomial.C hc
  calc
    _ = 2 * ((1 - X) * ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).derivative) := by ring
    _ = 2 * (-C (((p - 1) / 2 : ℕ) : ZMod p) * (1 - X) ^ ((p - 1) / 2)) := by
      rw [integer_power_derivative]
    _ = -(2 * C (((p - 1) / 2 : ℕ) : ZMod p)) * (1 - X) ^ ((p - 1) / 2) := by ring
    _ = _ := by rw [hpoly]; ring

theorem actual_halfPower_second_order (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * (1 - X : (ZMod p)[X]) * ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).derivative.derivative =
      3 * ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).derivative := by
  have hd := congrArg Polynomial.derivative (actual_halfPower_first_order p hp)
  simp only [derivative_mul, derivative_ofNat, derivative_sub, derivative_one,
    derivative_X, zero_sub, zero_mul, zero_add, mul_neg_one] at hd
  linear_combination hd

theorem power_degree_bound {K : Type*} [CommRing K] (P : K[X]) (d n : ℕ)
    (hP : P.natDegree ≤ d) : (P ^ n).natDegree ≤ n * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    simpa only [Nat.succ_mul] using natDegree_mul_le_of_le ih hP

/-- NC55's first-order native ratio identity, proved from the actual finite source. -/
theorem actual_native_first_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    X * (nativeField p (p / 6) * (nativeJetField p).derivative -
        (nativeField p (p / 6)).derivative * nativeJetField p) =
      nativeField p (p / 6) * ((1 - X) ^ ((p - 1) / 2) - nativeField p (p / 6)) := by
  let F := nativeField p (p / 6)
  let J := nativeJetField p
  let H : (ZMod p)[X] := (1 - X) ^ ((p - 1) / 2)
  have hF0 : F.eval 0 = 1 := actual_native_field_origin p (p / 6)
  have hB : bilinearOperator F (nativeBilinear F J) = 0 := by
    rw [nativeBilinear_source, actual_nativeJetField_regular_source p hp,
      actual_native_field_regular_ODE p (by omega)]
    ring
  have hH : bilinearOperator F (F * H) = 0 := by
    have he := bilinear_half_power_source F H
    rw [actual_nativeDiscriminant_zero p hp, actual_halfPower_first_order p hp,
      actual_halfPower_second_order p hp] at he
    simpa only [H, zero_mul, sub_zero, sub_self, mul_zero, add_zero] using he
  have hdF := actual_native_field_degree p
  have hdJ := nativeJetField_degree p
  have hdB := nativeBilinear_degree F J (p / 6) ((p - 1) / 2) hdF hdJ (by omega)
  have hbase : (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le
      (show (1 : (ZMod p)[X]).natDegree ≤ 0 by simp) (natDegree_X_le (R := ZMod p))
  have hdH : H.natDegree ≤ (p - 1) / 2 := by
    simpa only [Nat.mul_one] using power_degree_bound (1 - X : (ZMod p)[X]) 1 ((p - 1) / 2) hbase
  have hdDiff : (nativeBilinear F J - F * H).natDegree < p := by
    have hd : (nativeBilinear F J - F * H).natDegree ≤
        max (p / 6 + (p - 1) / 2 + 1) (p / 6 + (p - 1) / 2) :=
      natDegree_sub_le_of_le hdB (natDegree_mul_le_of_le hdF hdH)
    omega
  have h72 : (72 : ZMod p) ≠ 0 := by
    simpa only [WPActualNativeParameter.denominator_eval_zero, pow_one,
      Nat.factorial_one, Nat.cast_one, one_pow, mul_one] using
      WPActualNativeParameter.denominator_origin_residue_ne_zero p 1 (by omega) (by omega)
  have hzero : nativeBilinear F J - F * H = 0 := by
    apply finite_secondEuler_uniqueness p (bilinearE2 F) (bilinearE1 F) (bilinearE0 F)
      _ 72 h72
    · rw [coeff_zero_eq_eval_zero]
      simp [bilinearE2, hF0]
    · rw [coeff_zero_eq_eval_zero]
      simp [bilinearE1]
    · rw [coeff_zero_eq_eval_zero]
      simp [bilinearE0]
    · exact hdDiff
    · simp [nativeBilinear, hF0, H]
    · rw [bilinearOperator_euler, bilinearOperator_sub, hB, hH, sub_self, mul_zero]
  have heq := sub_eq_zero.mp hzero
  dsimp [nativeBilinear, F, J, H] at heq
  linear_combination heq

end WPActualNativeFirstIntegral
