import WPFieldAssembly.NativeSecondGreen
import WPFieldAssembly.NativeTerminatingNodes

open scoped Polynomial
open Polynomial WPActualNativeSecondJet

namespace WPFieldAssembly.NativeSecondBridge

set_option maxHeartbeats 1000000

/-- Shifted quotient division retains its literal integral cubic remainder. -/
theorem integral_shifted_second_expansion
    {R : Type*} [CommRing R]
    (A D : R[X]) (a b ua ub : R)
    (ha : D.eval a * ua = 1) (hb : D.eval b * ub = 1) :
    ∃ E : R,
      A.eval b * ub - A.eval a * ua -
        (b - a) * firstJetOver A D a ua -
        (b - a) ^ 2 * secondJetOver A D a ua =
      (b - a) ^ 3 * E := by
  obtain ⟨E, hE⟩ := quotient_taylor_divisible A D a ua ha
  have he := congrArg (Polynomial.eval (b - a)) hE
  simp only [eval_sub, eval_mul, eval_add, eval_C, eval_pow,
    eval_X, taylor_eval, sub_add_cancel] at he
  refine ⟨-E.eval (b - a) * ub, ?_⟩
  linear_combination
    -ub * he +
      (A.eval a * ua +
        (b - a) * firstJetOver A D a ua +
        (b - a) ^ 2 * secondJetOver A D a ua) * hb

theorem double_zero_second_jet
    {R : Type*} [CommRing R]
    (A D : R[X]) (a s b0 b1 u : R)
    (h0 : A.eval a = 0)
    (h1 : A.derivative.eval a = s * b0)
    (h2 : (taylor a A).coeff 2 = b0 + s * b1) :
    firstJetOver A D a u - s * secondJetOver A D a u =
      -s ^ 2 * (b1 * u - b0 * D.derivative.eval a * u ^ 2) := by
  simp only [firstJetOver, secondJetOver, h0, h1, h2,
    zero_mul, sub_zero]
  ring

/-- Exact algebra for the two actual terminating squares; attachment is separate. -/
theorem two_terminating_squares_second_bridge
    (r : ℚ) (hr : r ≠ 0)
    (a b R J C2 U : ℚ[X])
    (hd : a - b = C (4 * r) * R)
    (ht :
      b ^ 2 - a ^ 2 + C (4 * r) * J -
        C (16 * r ^ 2) * C2 = C (-64 * r ^ 3) * U) :
    J - 2 * a * R - C (2 * r) * (2 * C2 - 2 * R ^ 2) =
      C (-16 * r ^ 2) * U := by
  have hb : b = a - C (4 * r) * R := by
    linear_combination -hd
  rw [hb] at ht
  apply mul_left_cancel₀
    (Polynomial.C_ne_zero.mpr
      (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) hr))
  simp only [map_mul, map_pow, map_neg, map_ofNat] at ht ⊢
  linear_combination ht

theorem second_carry_attachment_algebra
    (p : ℚ) (a R Rh J Q E S : ℚ[X])
    (hD : J - 2 * a * R - C (p / 3) * Q = C (p ^ 2) * E)
    (hS : R - Rh = C p * S) :
    J - 2 * a * Rh =
      C p * (2 * a * S + C (1 / 3 : ℚ) * Q) +
        C (p ^ 2) * E := by
  have hthird : C (p / 3) = C p * C (1 / 3 : ℚ) := by
    rw [← C_mul]
    congr 1
    ring
  rw [hthird] at hD
  linear_combination hD + 2 * a * hS

open WPPIntegralReduction WPActualNativeParameter WPActualNativeFirstJet
  WPActualNativeSecondTaylor WPActualRankTwoParameter
  WPActualRankTwoDividedDifference WPActualRankTwoLegendreField
  WPFieldAssembly.NativeTerminatingNodes

theorem actual_shifted_native_coefficient (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ u : integralRationals p,
      parameterCoefficient n (-(5 : ℚ) * (p : ℚ) / 6) -
        parameterCoefficient n (-(p : ℚ) / 6) +
        (2 * (p : ℚ) / 3) * parameterJet n (-(p : ℚ) / 6) -
        (4 * (p : ℚ) ^ 2 / 9) * parameterSecondJet p n =
      (-8 * (p : ℚ) ^ 3 / 27) * u.val := by
  let R := integralRationals p
  let A := clearedNumerator R n
  let D := clearedDenominator R n
  let a := integralNode p hp
  let b := rankNode p hp 5
  have haunit := denominator_node_unit p n hp hn
  have hbunit := nativeDenominator_node_unit p n hp hn 5
  let ua : R := ⟨(D.eval a).val⁻¹, haunit.2⟩
  let ub : R := ⟨(D.eval b).val⁻¹, hbunit.2⟩
  have ha : D.eval a * ua = 1 := by
    apply Subtype.ext
    change (D.eval a).val * (D.eval a).val⁻¹ = 1
    exact mul_inv_cancel₀ haunit.1
  have hb : D.eval b * ub = 1 := by
    apply Subtype.ext
    change (D.eval b).val * (D.eval b).val⁻¹ = 1
    exact mul_inv_cancel₀ hbunit.1
  obtain ⟨u, hu⟩ := integral_shifted_second_expansion A D a b ua ub ha hb
  have hA : (A.eval a * ua).val = parameterCoefficient n (-(p : ℚ) / 6) := by
    change (A.eval a).val * (D.eval a).val⁻¹ = _
    simp only [A, D, R, a, evaluate_subtype, clearedNumerator_map,
      clearedDenominator_map, integralNode_value, parameterCoefficient, div_eq_mul_inv]
  have hB : (A.eval b * ub).val =
      parameterCoefficient n (-(5 : ℚ) * (p : ℚ) / 6) := by
    change (A.eval b).val * (D.eval b).val⁻¹ = _
    simp only [A, D, R, b, evaluate_subtype, clearedNumerator_map,
      clearedDenominator_map, rankNode_value, Nat.cast_ofNat,
      parameterCoefficient, div_eq_mul_inv]
  have hJ0 : firstJetOver A D a ua =
      (A.derivative.eval a * D.eval a -
        A.eval a * D.derivative.eval a) * ua ^ 2 := by
    unfold firstJetOver
    linear_combination -(A.derivative.eval a * ua) * ha
  have hJ : (firstJetOver A D a ua).val = parameterJet n (-(p : ℚ) / 6) := by
    rw [hJ0]
    change (integralParameterJet p n hp hn).val = _
    exact integralParameterJet_value p n hp hn
  have hK : (secondJetOver A D a ua).val = parameterSecondJet p n := by
    change (integralParameterSecondJet p n hp hn).val = _
    exact integralParameterSecondJet_value p n hp hn
  have hdelta : (b - a).val = -2 * (p : ℚ) / 3 := by
    change b.val - a.val = _
    simp only [b, a, rankNode_value, integralNode_value, Nat.cast_ofNat]
    ring
  have hv := congrArg (fun x : R => x.val) hu
  change (A.eval b * ub).val - (A.eval a * ua).val -
      (b - a).val * (firstJetOver A D a ua).val -
      (b - a).val ^ 2 * (secondJetOver A D a ua).val =
        (b - a).val ^ 3 * u.val at hv
  rw [hB, hA, hJ, hK, hdelta] at hv
  refine ⟨u, ?_⟩
  linear_combination hv

theorem actual_shifted_native_polynomial (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    ∃ U : (integralRationals p)[X],
      nativeNodeAt p 5 - nativeNodeAt p 1 +
        C (2 * (p : ℚ) / 3) * nativeFirstJetAt p (p - 1 - p / 6) -
        C (4 * (p : ℚ) ^ 2 / 9) * nativeSecondJetAt p (p - 1 - p / 6) =
      C (-8 * (p : ℚ) ^ 3 / 27) * U.map (integralRationals p).subtype := by
  classical
  let e := p - 1 - p / 6
  have he : e + 1 ≤ p := by dsimp only [e]; omega
  choose u hu using
    (fun n (hn : n < p) => actual_shifted_native_coefficient p n (by omega) hn)
  let U : (integralRationals p)[X] :=
    rankCoefficientPolynomial e (fun n => if hn : n < p then u n hn else 0)
  refine ⟨U, ?_⟩
  ext n
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_map,
    nativeNodeAt, nativeFirstJetAt, nativeSecondJetAt,
    coefficientPolynomial_coeff, U, rankCoefficientPolynomial_coeff]
  dsimp only [e]
  by_cases hn : n < p - 1 - p / 6 + 1
  · have hnp : n < p := by omega
    simpa only [if_pos hn, dif_pos hnp, Nat.cast_one, neg_one_mul,
      Nat.cast_ofNat, Subring.subtype_apply] using hu n hnp
  · simp only [if_neg hn, mul_zero, sub_zero, add_zero, map_zero]

/-- Actual full-cutoff p² error; the second jet retains its Hasse convention K/2. -/
theorem actual_full_native_second_bridge (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    ∃ E : (integralRationals p)[X],
      (nativeFirstJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2) -
        2 * rankJacobiNode p 1 * rankDividedJacobi p -
        C ((p : ℚ) / 3) *
          (2 * (nativeSecondJetAt p (p - 1 - p / 6)).comp (1 - X ^ 2) -
            2 * rankDividedJacobi p ^ 2) =
      C ((p : ℚ) ^ 2) * E.map (integralRationals p).subtype := by
  obtain ⟨U, hU⟩ := actual_shifted_native_polynomial p hp
  let q : ℚ[X] := 1 - X ^ 2
  let a := rankJacobiNode p 1
  let b := rankJacobiNode p 5
  let R := rankDividedJacobi p
  let J := (nativeFirstJetAt p (p - 1 - p / 6)).comp q
  let C2 := (nativeSecondJetAt p (p - 1 - p / 6)).comp q
  let r : ℚ := (p : ℚ) / 6
  have hr : r ≠ 0 := by change (p : ℚ) / 6 ≠ 0; positivity
  have hd : a - b = C (4 * r) * R := by
    change rankJacobiNode p 1 - rankJacobiNode p 5 =
      C (4 * ((p : ℚ) / 6)) * rankDividedJacobi p
    rw [show 4 * ((p : ℚ) / 6) = 2 * (p : ℚ) / 3 by ring]
    exact actual_two_jacobi_node_difference p (by omega)
  have ht := congrArg (fun P : ℚ[X] => P.comp q) hU
  simp only [sub_comp, add_comp, mul_comp, C_comp] at ht
  rw [actual_terminating_native_node_square p 5 hp (Or.inr rfl),
    actual_terminating_native_node_square p 1 hp (Or.inl rfl)] at ht
  change b ^ 2 - a ^ 2 + C (2 * (p : ℚ) / 3) * J -
      C (4 * (p : ℚ) ^ 2 / 9) * C2 =
        C (-8 * (p : ℚ) ^ 3 / 27) *
          (U.map (integralRationals p).subtype).comp q at ht
  rw [show 2 * (p : ℚ) / 3 = 4 * r by dsimp only [r]; ring,
    show 4 * (p : ℚ) ^ 2 / 9 = 16 * r ^ 2 by dsimp only [r]; ring,
    show -8 * (p : ℚ) ^ 3 / 27 = -64 * r ^ 3 by dsimp only [r]; ring] at ht
  have hD := two_terminating_squares_second_bridge r hr a b R J C2
    ((U.map (integralRationals p).subtype).comp q) hd ht
  let ninth : integralRationals p :=
    ⟨1 / 9, WPFiniteConductorPolynomial.small_inverse_integral p 9 (by norm_num) (by omega)⟩
  let s : integralRationals p := -4 * ninth
  have hs : s.val = (-4 / 9 : ℚ) := by change -(4 : ℚ) * (1 / 9 : ℚ) = -4 / 9; ring
  let E : (integralRationals p)[X] := C s * U.comp (1 - X ^ 2)
  have hEmap : E.map (integralRationals p).subtype =
      C (-4 / 9 : ℚ) * (U.map (integralRationals p).subtype).comp q := by
    dsimp only [E]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp]
    rw [show (integralRationals p).subtype s = (-4 / 9 : ℚ) from hs]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    rfl
  refine ⟨E, ?_⟩
  change J - 2 * a * R - C ((p : ℚ) / 3) * (2 * C2 - 2 * R ^ 2) =
    C ((p : ℚ) ^ 2) * E.map (integralRationals p).subtype
  rw [hEmap, show (p : ℚ) / 3 = 2 * r by dsimp only [r]; ring]
  have hc : -16 * r ^ 2 = (p : ℚ) ^ 2 * (-4 / 9 : ℚ) := by dsimp only [r]; ring
  rw [← mul_assoc, ← C_mul, ← hc]
  exact hD

end WPFieldAssembly.NativeSecondBridge
