import WPActualGaussBottom

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeFirstIntegral WPActualCMGauss WPActualGaussBottom

namespace WPActualGaussProper

theorem small_cast_ne_zero (p n : ℕ) [Fact p.Prime] (hn : 0 < n) (hbound : n < p) :
    (n : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hd
  have := Nat.le_of_dvd hn hd
  omega

/-- No lower-degree homogeneous polynomial can be hidden in the proper Legendre source. -/
theorem legendre_lower_degree_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p / 3)
    (hsource : legendreRegular (p / 3) P = 0) : P = 0 := by
  by_contra hP
  let m := P.natDegree
  have hm : m < p / 3 := hdegree
  have hu1 := small_cast_ne_zero p (p / 3 - m) (by omega) (by omega)
  have hu2 := small_cast_ne_zero p (m + p / 3 + 1) (by omega) (by omega)
  have hdiff : (m : ZMod p) - ((p / 3 : ℕ) : ZMod p) = -((p / 3 - m : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : m ≤ p / 3)]
    ring
  have hu : ((m : ZMod p) - ((p / 3 : ℕ) : ZMod p)) *
      ((m : ZMod p) + ((p / 3 : ℕ) : ZMod p) + 1) ≠ 0 := by
    rw [hdiff]
    exact mul_ne_zero (neg_ne_zero.mpr hu1) (by simpa only [Nat.cast_add, Nat.cast_one] using hu2)
  have he : legendreEuler (p / 3) P = 0 := by
    rw [legendreEuler_eq_X_regular, hsource, mul_zero]
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (m + 1)) he
  rw [legendreEuler_coeff_succ, coeff_zero,
    coeff_eq_zero_of_natDegree_lt (by dsimp [m]; omega), mul_zero, zero_sub] at hc
  have hz : P.coeff m = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp hc)).resolve_left hu
  exact (leadingCoeff_ne_zero.mpr hP) (by simpa only [m, coeff_natDegree] using hz)

theorem legendreRegular_reflection {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) :
    legendreRegular k (P.comp (1 - X)) = (legendreRegular k P).comp (1 - X) := by
  simp [legendreRegular, derivative_comp]
  ring

theorem negative_power_square {K : Type*} [CommRing K] (n : ℕ) :
    ((-1 : K) ^ n) ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      _ = ((-1 : K) ^ n) ^ 2 := by ring
      _ = 1 := ih

theorem actualGauss_derivative_reflection (p : ℕ) :
    (actualGauss p).derivative.comp (1 - X) =
      -(-1 : (ZMod p)[X]) ^ (p / 3) * (actualGauss p).derivative := by
  have hd := congrArg Polynomial.derivative (actualGauss_reflection p)
  simp [derivative_mul, derivative_comp, derivative_pow] at hd
  have hs := negative_power_square (K := (ZMod p)[X]) (p / 3)
  linear_combination -(-1 : (ZMod p)[X]) ^ (p / 3) * hd -
    (actualGauss p).derivative.comp (1 - X) * hs

theorem properGauss_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properGauss p).comp (1 - X) = -(-1 : (ZMod p)[X]) ^ (p / 3) * properGauss p := by
  let sigma : (ZMod p)[X] := (-1) ^ (p / 3)
  let Q := (properGauss p).comp (1 - X) + sigma * properGauss p
  have hd := properGauss_degree p hp
  have hcomp : (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have hreflect : ((properGauss p).comp (1 - X)).natDegree ≤ p / 3 - 1 := by
    exact (natDegree_comp_le (p := properGauss p) (q := 1 - X)).trans (by nlinarith)
  have hsigma : sigma.natDegree ≤ 0 := by
    simpa only [Nat.mul_zero] using power_degree_bound (-1 : (ZMod p)[X]) 0 (p / 3) (by simp)
  have hQdegree : Q.natDegree < p / 3 := by
    have hh := natDegree_add_le_of_le hreflect (natDegree_mul_le_of_le hsigma hd)
    change Q.natDegree ≤ max (p / 3 - 1) (0 + (p / 3 - 1)) at hh
    exact hh.trans_lt (by omega)
  have hQsource : legendreRegular (p / 3) Q = 0 := by
    have hlinear := legendreRegular_add_C_mul (p / 3)
      ((properGauss p).comp (1 - X)) (properGauss p) ((-1 : ZMod p) ^ (p / 3))
    simp only [map_pow, map_neg, map_one] at hlinear
    dsimp only [Q, sigma]
    rw [hlinear, legendreRegular_reflection, properGauss_regular_source p hp,
      neg_comp, actualGauss_derivative_reflection]
    ring
  have hz := legendre_lower_degree_zero p hp Q hQdegree hQsource
  simpa only [sigma, neg_mul] using eq_neg_of_add_eq_zero_left hz

noncomputable def wronskianPolynomial {K : Type*} [CommRing K] (Y P : K[X]) : K[X] :=
  2 * X * (1 - X) * (Y * P.derivative - Y.derivative * P) + Y ^ 2 - 1

theorem wronskianPolynomial_source {K : Type*} [CommRing K] (k : ℕ) (Y P : K[X]) :
    (wronskianPolynomial Y P).derivative =
      2 * Y * legendreRegular k P - 2 * P * legendreRegular k Y + 2 * Y * Y.derivative := by
  simp [wronskianPolynomial, legendreRegular, derivative_mul, derivative_pow_succ]
  ring

theorem finite_derivative_zero (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdegree : P.natDegree < p) (horigin : P.eval 0 = 0) (hsource : P.derivative = 0) : P = 0 := by
  ext n
  rw [coeff_zero]
  cases n with
  | zero => exact (coeff_zero_eq_eval_zero P).trans horigin
  | succ n =>
    by_cases hn : n + 1 < p
    · have hu := small_cast_ne_zero p (n + 1) (by omega) hn
      have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff n) hsource
      rw [coeff_derivative, coeff_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_right (by simpa only [Nat.cast_add, Nat.cast_one] using hu)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem wronskianPolynomial_degree {K : Type*} [CommRing K] (Y P : K[X]) (k : ℕ)
    (hY : Y.natDegree ≤ k) (hP : P.natDegree ≤ k - 1) :
    (wronskianPolynomial Y P).natDegree ≤ 2 * k + 2 := by
  have hDY := derivative_degree_bound Y k hY
  have hDP := derivative_degree_bound P (k - 1) hP
  have hinner := natDegree_sub_le_of_le (natDegree_mul_le_of_le hY hDP)
    (natDegree_mul_le_of_le hDY hP)
  have hfront : (2 * X * (1 - X) : K[X]).natDegree ≤ 2 := by compute_degree
  have hterm := natDegree_mul_le_of_le hfront hinner
  have hsquare := power_degree_bound Y k 2 hY
  have hone : (1 : K[X]).natDegree ≤ 0 := by simp
  unfold wronskianPolynomial
  exact (natDegree_sub_le_of_le (natDegree_add_le_of_le hterm hsquare) hone).trans (by omega)

/-- The complete proper quotient Wronskian, with its actual constant fixed at z=0. -/
theorem actual_properGauss_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * X * (1 - X) * (actualGauss p * (properGauss p).derivative -
      (actualGauss p).derivative * properGauss p) = 1 - actualGauss p ^ 2 := by
  have hd := wronskianPolynomial_degree (actualGauss p) (properGauss p) (p / 3)
    (actualGauss_degree p) (properGauss_degree p hp)
  have hzero : wronskianPolynomial (actualGauss p) (properGauss p) = 0 := by
    apply finite_derivative_zero p _ (hd.trans_lt (by omega))
    · simp [wronskianPolynomial, actualGauss_origin]
    · rw [wronskianPolynomial_source (p / 3), properGauss_regular_source p hp,
        actualGauss_legendre_regular]
      ring
  unfold wronskianPolynomial at hzero
  linear_combination hzero

theorem actualGauss_exact_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualGauss p).natDegree = p / 3 := by
  have hd := actualGauss_degree p
  by_contra hn
  have hz := legendre_lower_degree_zero p hp (actualGauss p) (by omega)
    (actualGauss_legendre_regular p)
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
  simp [actualGauss_origin] at he

theorem proper_wronskian_bezout {K : Type*} [CommRing K] (Y P : K[X])
    (hW : 2 * X * (1 - X) * (Y * P.derivative - Y.derivative * P) = 1 - Y ^ 2) :
    Y * (Y + 2 * X * (1 - X) * P.derivative) +
      Y.derivative * (-2 * X * (1 - X) * P) = 1 := by
  linear_combination hW

/-- The full proper Wronskian gives square divisibility of the actual ratio-invariant numerator. -/
theorem proper_wronskian_square_division {K : Type*} [Field K] (Y P M : K[X])
    (hY : Y ≠ 0)
    (hW : 2 * X * (1 - X) * (Y * P.derivative - Y.derivative * P) = 1 - Y ^ 2)
    (hM : M.derivative * Y - 2 * M * Y.derivative = 0) :
    ∃ K0 : K[X], M = Y ^ 2 * K0 ∧ K0.derivative = 0 := by
  let r : K[X] := X * (1 - X)
  let T := M * (Y + 2 * r * P.derivative) - r * M.derivative * P
  have hT : M = Y * T := by
    dsimp [T, r]
    linear_combination -M * hW + X * (1 - X) * P * hM
  have hTS : Y * T.derivative - Y.derivative * T = 0 := by
    have hh : Y * (Y * T.derivative - Y.derivative * T) = 0 := by
      rw [hT] at hM
      simp only [derivative_mul] at hM
      linear_combination hM
    exact (mul_eq_zero.mp hh).resolve_left hY
  let K0 := T * (Y + 2 * r * P.derivative) - 2 * r * T.derivative * P
  have hK : T = Y * K0 := by
    dsimp [K0, r]
    linear_combination -T * hW + 2 * X * (1 - X) * P * hTS
  have hfactor : M = Y ^ 2 * K0 := by rw [hT, hK]; ring
  refine ⟨K0, hfactor, ?_⟩
  have hh : Y ^ 3 * K0.derivative = 0 := by
    rw [hfactor] at hM
    simp only [derivative_mul, derivative_sq, C_ofNat] at hM
    linear_combination hM
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 3 hY)

end WPActualGaussProper
