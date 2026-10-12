import WPNativeParameterTaylor
import Mathlib.Data.Nat.Prime.Factorial

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPNativeParameterTaylor WPActualNativeHasse

namespace WPActualNativeParameter

/-- Original three upper parameters after clearing only their fixed denominators. -/
noncomputable def clearedNumerator (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.range n,
    (C (6 * (j : R) + 1) + 6 * X) *
      (C (2 * (j : R) + 1) + 2 * X) * (C (6 * (j : R) + 5) + 6 * X)

/-- The exact lower parameters 1,1+epsilon,1+2epsilon, including the factor 72. -/
noncomputable def clearedDenominator (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∏ j ∈ Finset.range n,
    C (72 * ((j : R) + 1)) * (C ((j : R) + 1) + X) *
      (C ((j : R) + 1) + 2 * X)

theorem clearedNumerator_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (clearedNumerator R n).map f = clearedNumerator S n := by
  simp only [clearedNumerator, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

theorem clearedDenominator_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) : (clearedDenominator R n).map f = clearedDenominator S n := by
  simp only [clearedDenominator, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_natCast, Polynomial.map_one,
    map_add, map_mul, map_ofNat, map_natCast, map_one]

theorem numerator_eval_zero_succ (R : Type*) [CommRing R] (n : ℕ) :
    (clearedNumerator R (n + 1)).eval 0 = (clearedNumerator R n).eval 0 *
      ((6 * (n : R) + 1) * (2 * (n : R) + 1) * (6 * (n : R) + 5)) := by
  simp [clearedNumerator, Finset.prod_range_succ]

theorem denominator_eval_zero_succ (R : Type*) [CommRing R] (n : ℕ) :
    (clearedDenominator R (n + 1)).eval 0 =
      (clearedDenominator R n).eval 0 * (72 * ((n : R) + 1) ^ 3) := by
  simp only [clearedDenominator, Finset.prod_range_succ, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero,
    Polynomial.eval_ofNat, mul_zero]
  ring

theorem denominator_eval_zero (R : Type*) [CommRing R] (n : ℕ) :
    (clearedDenominator R n).eval 0 = (72 : R) ^ n * (n.factorial : R) ^ 3 := by
  induction n with
  | zero => simp [clearedDenominator]
  | succ n ih =>
    rw [denominator_eval_zero_succ, ih, pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

theorem native_cleared_parameter_origin (n : ℕ) :
    (clearedNumerator ℚ n).eval 0 =
      WPReview.nativeCoefficient n * (clearedDenominator ℚ n).eval 0 := by
  induction n with
  | zero => simp [clearedNumerator, clearedDenominator, WPReview.nativeCoefficient_zero]
  | succ n ih =>
    rw [numerator_eval_zero_succ, denominator_eval_zero_succ, ih]
    linear_combination -(clearedDenominator ℚ n).eval 0 * actual_native_cleared_recurrence n

noncomputable def parameterCoefficient (n : ℕ) (t : ℚ) : ℚ :=
  (clearedNumerator ℚ n).eval t / (clearedDenominator ℚ n).eval t

noncomputable def parameterJet (n : ℕ) (t : ℚ) : ℚ :=
  quotientJet (clearedNumerator ℚ n) (clearedDenominator ℚ n) t

theorem parameterCoefficient_origin (n : ℕ) : parameterCoefficient n 0 = WPReview.nativeCoefficient n := by
  have hd : (clearedDenominator ℚ n).eval 0 ≠ 0 := by
    rw [denominator_eval_zero]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
  rw [parameterCoefficient, native_cleared_parameter_origin, mul_div_cancel_right₀ _ hd]

theorem prime_six_classes (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    p = 6 * (p / 6) + 1 ∨ p = 6 * (p / 6) + 5 := by
  have hp3 : ¬3 ∣ p := by
    intro hd
    have h := (Nat.dvd_prime (Fact.out : p.Prime)).mp hd
    omega
  have hm3 : p % 3 ≠ 0 := by
    intro hz
    exact hp3 (Nat.dvd_of_mod_eq_zero hz)
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hm := Nat.mod_lt p (by omega : 0 < 6)
  have hd := Nat.mod_add_div p 6
  omega

theorem terminating_numerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p / 6 < n) :
    (clearedNumerator ℚ n).eval (-(p : ℚ) / 6) = 0 := by
  rw [clearedNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  rcases prime_six_classes p hp with hp1 | hp5
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [hq]
    ring
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [hq]
    ring

noncomputable def integralNode (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : integralRationals p :=
  -(p : integralRationals p) * ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩

theorem integralNode_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralNode p hp).val = -(p : ℚ) / 6 := by
  simp only [integralNode, Subring.coe_mul, Subring.coe_neg, Subring.coe_natCast]
  ring

theorem integralNode_residue (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p (integralNode p hp) = 0 := by
  rw [integralNode, map_mul, map_neg, map_natCast, ZMod.natCast_self, neg_zero, zero_mul]

theorem denominator_origin_residue_ne_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (clearedDenominator (ZMod p) n).eval 0 ≠ 0 := by
  rw [denominator_eval_zero]
  have hsmall (a : ℕ) (ha : 0 < a) (hlt : a < p) : (a : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have := Nat.le_of_dvd ha hd
    omega
  have h72 : (72 : ZMod p) ≠ 0 := by
    rw [show (72 : ZMod p) = 2 ^ 3 * 3 ^ 2 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ (hsmall 2 (by omega) (by omega)))
      (pow_ne_zero _ (hsmall 3 (by omega) (by omega)))
  have hfac : (n.factorial : ZMod p) ≠ 0 := by
    intro hz
    have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    omega
  exact mul_ne_zero (pow_ne_zero _ h72) (pow_ne_zero _ hfac)

theorem denominator_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((clearedDenominator (integralRationals p) n).eval (integralNode p hp)) =
      (clearedDenominator (ZMod p) n).eval 0 := by
  rw [← Polynomial.eval_map_apply, clearedDenominator_map, integralNode_residue]

theorem denominator_node_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val ≠ 0 ∧
      (((clearedDenominator (integralRationals p) n).eval (integralNode p hp)).val)⁻¹ ∈
        integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [denominator_node_residue]
  exact denominator_origin_residue_ne_zero p n hp hn

theorem parameterJet_empty (t : ℚ) : parameterJet 0 t = 0 := by
  simp [parameterJet, quotientJet, clearedNumerator, clearedDenominator]

end WPActualNativeParameter
