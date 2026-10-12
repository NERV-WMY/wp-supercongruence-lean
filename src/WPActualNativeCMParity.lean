import WPActualNativeCubicInvariant

open scoped Polynomial
open Polynomial WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualCubicGauge WPActualCubicHasse WPActualNativeCubicJet WPActualNativeCubicInvariant

namespace WPActualNativeCMParity

theorem CMcenter_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - (1 / 2 : ZMod p)) = 1 / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  field_simp
  ring

theorem actualGauss_CM_odd_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (actualGauss p).eval (1 / 2) = 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (actualGauss_reflection p)
  simp only [eval_mul, eval_neg, eval_one, eval_comp, eval_sub,
    eval_X, CMcenter_reflection p hp, hk.neg_one_pow] at he
  have hzero : 2 * (actualGauss p).eval (1 / 2) = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hzero).resolve_left (small_cast_ne_zero p 2 (by omega) (by omega))

theorem properGauss_CM_even_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (hk : Even (p / 3)) :
    (properGauss p).eval (1 / 2) = 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (properGauss_reflection p hp)
  simp only [eval_comp, eval_sub, eval_one, eval_X, CMcenter_reflection p hp,
    eval_mul, eval_neg, hk.neg_one_pow] at he
  have hzero : 2 * (properGauss p).eval (1 / 2) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left (small_cast_ne_zero p 2 (by omega) (by omega))

theorem actualGauss_CM_even_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (hk : Even (p / 3)) :
    (actualGauss p).eval (1 / 2) ≠ 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (actual_properGauss_wronskian p hp)
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_ofNat, eval_X,
    properGauss_CM_even_zero p hp hk] at he
  intro hz
  rw [hz] at he
  norm_num at he

theorem actualGauss_CM_odd_derivative_ne_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (actualGauss p).derivative.eval (1 / 2) ≠ 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (actual_properGauss_wronskian p hp)
  simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_ofNat, eval_X,
    actualGauss_CM_odd_zero p hp hk] at he
  intro hz
  rw [hz] at he
  norm_num at he

theorem properGauss_derivative_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properGauss p).derivative.comp (1 - X) =
      (-1 : (ZMod p)[X]) ^ (p / 3) * (properGauss p).derivative := by
  have hd := congrArg Polynomial.derivative (properGauss_reflection p hp)
  simp [derivative_mul, derivative_comp, derivative_pow] at hd
  exact hd

theorem properGauss_CM_odd_derivative_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (properGauss p).derivative.eval (1 / 2) = 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2))
    (properGauss_derivative_reflection p hp)
  simp only [eval_comp, eval_sub, eval_one, eval_X, CMcenter_reflection p hp,
    eval_mul, eval_neg, hk.neg_one_pow] at he
  have hzero : 2 * (properGauss p).derivative.eval (1 / 2) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left (small_cast_ne_zero p 2 (by omega) (by omega))

theorem actualGauss_CM_odd_second_derivative_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (actualGauss p).derivative.derivative.eval (1 / 2) = 0 := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (actualGauss_cleared_ODE p (by omega))
  simp only [eval_add, eval_sub, eval_mul, eval_ofNat, eval_X, eval_pow,
    eval_one, eval_zero, actualGauss_CM_odd_zero p hp hk] at he
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 := small_cast_ne_zero p 9 (by omega) (by omega)
  field_simp at he
  norm_num at he
  simpa only [one_div] using he.resolve_left h9

end WPActualNativeCMParity
