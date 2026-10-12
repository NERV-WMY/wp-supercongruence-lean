import WPActualNativeCubicTransport
import WPFiniteAffineLog

open scoped Polynomial
open Polynomial WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualCubicGauge WPActualCubicHasse WPActualNativeCubicJet WPActualNativeCubicTransport
  WPFiniteAffineLog WPActualNativeFirstIntegral

namespace WPActualNativeCubicPrimitive

/-- The complete finite-log primitive, including its actual band above p. -/
noncomputable def nativeUnitPrimitive (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (4 + 8 * X ^ p) * LP p - 3 * (LP p).comp (-8 * X)

theorem cubicH_frobenius (p : ℕ) [Fact p.Prime] :
    (cubicH : (ZMod p)[X]) ^ p = 1 + 8 * X ^ p := by
  have hc : (8 : (ZMod p)[X]) ^ p = 8 := by
    change (C (8 : ZMod p)) ^ p = C (8 : ZMod p)
    rw [← map_pow, ZMod.pow_card]
  unfold cubicH
  rw [add_pow_char, one_pow, mul_pow, hc]

theorem cubicD_frobenius (p : ℕ) [Fact p.Prime] :
    (cubicD : (ZMod p)[X]) ^ p = 1 - 20 * X ^ p - 8 * X ^ (2 * p) := by
  have hc (m : ZMod p) : (C m) ^ p = C m := by rw [← map_pow, ZMod.pow_card]
  unfold cubicD
  rw [sub_pow_char, sub_pow_char, one_pow, mul_pow, mul_pow]
  rw [show (20 : (ZMod p)[X]) ^ p = 20 from hc 20,
    show (8 : (ZMod p)[X]) ^ p = 8 from hc 8, ← pow_mul]

theorem scaled_log_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((LP p : (ZMod p)[X]).comp (-8 * X)).derivative =
      -8 * (cubicH ^ (p - 1) - X ^ (p - 1)) := by
  have h8 : (-8 : ZMod p) ≠ 0 := neg_ne_zero.mpr (small_cast_ne_zero p 8 (by omega) (by omega))
  have hc : (-8 : (ZMod p)[X]) ^ (p - 1) = 1 := by
    simpa only [map_pow, map_neg, C_ofNat, map_one] using
      congrArg (Polynomial.C (R := ZMod p)) (ZMod.pow_card_sub_one_eq_one h8)
  rw [derivative_comp, LP_derivative_closed_eq]
  simp only [derivative_mul, derivative_neg, derivative_ofNat, derivative_X,
    zero_mul, neg_zero, zero_add, mul_one, sub_comp, pow_comp, one_comp, X_comp, mul_pow]
  rw [hc, one_mul]
  have hh : (1 - -8 * X : (ZMod p)[X]) = cubicH := by unfold cubicH; ring
  rw [hh]

theorem nativeUnitPrimitive_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeUnitPrimitive p).derivative =
      (4 + 8 * X ^ p) * ((1 - X) ^ (p - 1) - X ^ (p - 1)) +
        24 * (cubicH ^ (p - 1) - X ^ (p - 1)) := by
  have hz : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by simp [derivative_X_pow]
  simp only [nativeUnitPrimitive, derivative_sub, derivative_mul, derivative_add,
    derivative_ofNat, zero_mul, zero_add, derivative_ofNat, hz, mul_zero,
    LP_derivative_closed_eq, scaled_log_derivative p hp]
  ring

/-- Both resonant slots cancel in the actual source before integration. -/
theorem nativeUnitPrimitive_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    X * (1 - X) * (nativeUnitPrimitive p).derivative = cubicD ^ p - cubicD * cubicH ^ (p - 1) := by
  have hh := cubicH_frobenius p
  have hd := cubicD_frobenius p
  have hx : (1 - X : (ZMod p)[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char, one_pow]
  have hr1 : (X * (1 - X) : (ZMod p)[X]) * (1 - X) ^ (p - 1) = X * (1 - X ^ p) := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), hx]
  have hr2 : (X * (1 - X) : (ZMod p)[X]) * X ^ (p - 1) = X ^ p * (1 - X) := by
    rw [show (X * (1 - X) : (ZMod p)[X]) * X ^ (p - 1) =
      (X * X ^ (p - 1)) * (1 - X) by ring, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hclear : cubicH * (X * (1 - X) * (nativeUnitPrimitive p).derivative) =
      cubicH * (cubicD ^ p - cubicD * cubicH ^ (p - 1)) := by
    rw [nativeUnitPrimitive_derivative p hp]
    have hpow : (cubicH : (ZMod p)[X]) * cubicH ^ (p - 1) = cubicH ^ p := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
    calc
      _ = cubicH * ((4 + 8 * X ^ p) * X * (1 - X ^ p) -
          (28 + 8 * X ^ p) * X ^ p * (1 - X)) + 24 * X * (1 - X) * cubicH ^ p := by
        linear_combination cubicH * (4 + 8 * X ^ p) * hr1 -
          cubicH * (28 + 8 * X ^ p) * hr2 + 24 * X * (1 - X) * hpow
      _ = cubicH * (cubicD ^ p - cubicD * cubicH ^ (p - 1)) := by
        rw [hh, hd]
        rw [show (cubicH : (ZMod p)[X]) *
            (1 - 20 * X ^ p - 8 * X ^ (2 * p) - cubicD * cubicH ^ (p - 1)) =
            cubicH * (1 - 20 * X ^ p - 8 * X ^ (2 * p)) -
              cubicD * (cubicH * cubicH ^ (p - 1)) by ring, hpow, hh]
        unfold cubicH cubicD
        rw [show (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 by rw [Nat.mul_comm 2 p, pow_mul]]
        ring
  exact mul_left_cancel₀ (cubicH_ne_zero (K := ZMod p)) hclear

theorem nativeUnitPrimitive_origin (p : ℕ) [Fact p.Prime] :
    (nativeUnitPrimitive p).eval 0 = 0 := by
  have hL : (LP p : (ZMod p)[X]).eval 0 = 0 := by
    simp only [LP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero_pow (by have := (Finset.mem_Ico.mp hj).1; omega : j ≠ 0), mul_zero]
  simp [nativeUnitPrimitive, eval_comp, hL]

theorem nativeUnitPrimitive_degree (p : ℕ) [Fact p.Prime] :
    (nativeUnitPrimitive p).natDegree ≤ 2 * p - 1 := by
  have hP : (4 + 8 * X ^ p : (ZMod p)[X]).natDegree ≤ p := by
    compute_degree
  have hs : (-8 * X : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have hc := (natDegree_comp_le (p := LP p) (q := (-8 * X : (ZMod p)[X]))).trans
    (Nat.mul_le_mul (LP_natDegree_le p) hs)
  have hthree := natDegree_C_mul_le (3 : ZMod p) ((LP p).comp (-8 * X))
  have hd := natDegree_sub_le_of_le
    (natDegree_mul_le_of_le hP (LP_natDegree_le p)) (hthree.trans hc)
  change (nativeUnitPrimitive p).natDegree ≤ max (p + (p - 1)) ((p - 1) * 1) at hd
  have := (Fact.out : p.Prime).pos
  exact hd.trans (by omega)

end WPActualNativeCubicPrimitive
