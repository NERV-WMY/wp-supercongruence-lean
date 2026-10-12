import WPMomentPrecision.SecondLift.TerminatingSquare

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondTaylor WPActualRankTwoParameter
  WPActualRankTwoGaussODE WPActualTerminatingSquare

namespace WPMomentPrecision.TwoNodeSquare

set_option maxHeartbeats 1200000

/-- The original native coefficient family at either terminating node, through e. -/
noncomputable def nativeNodePolynomial (p k : ℕ) : ℚ[X] :=
  coefficientPolynomial (p - 1 - p / 6)
    (fun n => parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6))

theorem native_denominator_node_unit (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((clearedDenominator (integralRationals p) n).eval (rankNode p hp k)).val ≠ 0 ∧
      (((clearedDenominator (integralRationals p) n).eval
        (rankNode p hp k)).val)⁻¹ ∈ integralRationals p := by
  apply WPNativeParameterTaylor.integral_inverse_of_residue_ne_zero
  rw [← Polynomial.eval_map_apply, clearedDenominator_map, rankNode_residue]
  exact denominator_origin_residue_ne_zero p n hp hn

theorem native_denominator_rational_node_ne_zero (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (clearedDenominator ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6) ≠ 0 := by
  have h := (native_denominator_node_unit p n k hp hn).1
  rwa [evaluate_subtype, clearedDenominator_map, rankNode_value] at h

/-- The recurrence at either actual node keeps every lower-parameter factor. -/
theorem native_coefficient_node_recurrence (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    (WPActualNativeJetRecurrence.lowerFactor ℚ n).eval
        (-(k : ℚ) * (p : ℚ) / 6) *
        parameterCoefficient (n + 1) (-(k : ℚ) * (p : ℚ) / 6) =
      (WPActualNativeJetRecurrence.upperFactor ℚ n).eval
        (-(k : ℚ) * (p : ℚ) / 6) *
        parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6) := by
  have hD := native_denominator_rational_node_ne_zero p n k hp (by omega)
  have hDn := native_denominator_rational_node_ne_zero p (n + 1) k hp hn
  rw [WPActualNativeJetRecurrence.actual_parameter_denominator_succ, eval_mul] at hDn
  have hL := (mul_ne_zero_iff.mp hDn).2
  have hf (a u d b : ℚ) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by
    field_simp [hd, hb]
  unfold parameterCoefficient
  rw [WPActualNativeJetRecurrence.actual_parameter_numerator_succ,
    WPActualNativeJetRecurrence.actual_parameter_denominator_succ, eval_mul, eval_mul]
  exact hf _ _ _ _ hD hL

theorem native_high_numerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p - 1 - p / 6 < n) :
    (clearedNumerator ℚ n).eval (-5 * (p : ℚ) / 6) = 0 := by
  rw [clearedNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  simp only [eval_mul, eval_add, eval_C, eval_ofNat, eval_X]
  rcases prime_six_classes p hp with hp1 | hp5
  · have he : p - 1 - p / 6 = 5 * (p / 6) := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [he, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring
  · have he : p - 1 - p / 6 = 5 * (p / 6) + 4 := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [he, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring

theorem native_coefficient_node_termination (p k n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hk : k = 1 ∨ k = 5) (hn : p - 1 - p / 6 < n) :
    parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6) = 0 := by
  rcases hk with rfl | rfl
  · simp only [Nat.cast_one, neg_one_mul, parameterCoefficient]
    rw [terminating_numerator_zero p n hp (by omega), zero_div]
  · simp only [Nat.cast_ofNat, parameterCoefficient]
    rw [native_high_numerator_zero p n hp hn, zero_div]

theorem actual_nativeNodeEuler_ODE (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    termEuler (-(k : ℚ) * (p : ℚ) / 6) (nativeNodePolynomial p k) = 0 := by
  have hd := Nat.div_mul_le_self p 6
  ext j
  cases j with
  | zero => rw [termEuler_coeff_zero, Polynomial.coeff_zero]
  | succ n =>
    rw [termEuler_coeff_succ, Polynomial.coeff_zero]
    simp only [nativeNodePolynomial, coefficientPolynomial_coeff]
    by_cases hn : n + 1 < p - 1 - p / 6 + 1
    · rw [if_pos hn, if_pos (by omega)]
      have h := native_coefficient_node_recurrence p n k (by omega) (by omega)
      simp only [WPActualNativeJetRecurrence.lowerFactor,
        WPActualNativeJetRecurrence.upperFactor, eval_mul, eval_C, eval_add,
        eval_ofNat, eval_X] at h
      linear_combination h
    · rw [if_neg hn]
      by_cases hn0 : n < p - 1 - p / 6 + 1
      · rw [if_pos hn0]
        have h := native_coefficient_node_recurrence p n k (by omega) (by omega)
        rw [native_coefficient_node_termination p k (n + 1) (by omega) hk
          (by omega), mul_zero] at h
        simp only [WPActualNativeJetRecurrence.upperFactor, eval_mul,
          eval_C, eval_add, eval_ofNat, eval_X] at h
        linear_combination h
      · rw [if_neg hn0]
        ring

theorem actual_nativeNodeRegular_ODE (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    termRegular (-(k : ℚ) * (p : ℚ) / 6) (nativeNodePolynomial p k) = 0 := by
  have h : X * termRegular (-(k : ℚ) * (p : ℚ) / 6)
      (nativeNodePolynomial p k) = 0 := by
    rw [← termEuler_eq_X_regular, actual_nativeNodeEuler_ODE p k hp hk]
  exact (mul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero

/-- At either rational node the regular-end indicial factors never vanish. -/
theorem rational_node_square_unique (p k : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hk : k = 1 ∨ k = 5) (P : ℚ[X]) (h1 : P.eval 1 = 0)
    (hODE : jacobiSquare (-(k : ℚ) * (p : ℚ) / 6) P = 0) : P = 0 := by
  let H := P.comp (1 - X)
  have hH : H = 0 := by
    have he : WPHasseCubicSource.regularEuler squareE3
        (squareE2 (-(k : ℚ) * (p : ℚ) / 6))
        (squareE1 (-(k : ℚ) * (p : ℚ) / 6))
        (squareE0 (-(k : ℚ) * (p : ℚ) / 6)) H = 0 := by
      dsimp only [H]
      rw [jacobiSquare_euler, hODE, zero_comp, mul_zero]
    ext n
    rw [coeff_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [H, coeff_zero_eq_eval_zero, eval_comp] using h1
      · have h6n : (n : ℚ) + -(k : ℚ) * (p : ℚ) / 6 ≠ 0 := by
          intro hz
          have hh : 6 * (n : ℚ) = (k : ℚ) * (p : ℚ) := by linarith
          have hi : 6 * n = k * p := by exact_mod_cast hh
          rcases prime_six_classes p (by omega) with hp1 | hp5 <;>
            rcases hk with rfl | rfl <;> omega
        have h3n : (n : ℚ) + 2 * (-(k : ℚ) * (p : ℚ) / 6) ≠ 0 := by
          intro hz
          have hh : 3 * (n : ℚ) = (k : ℚ) * (p : ℚ) := by linarith
          have hi : 3 * n = k * p := by exact_mod_cast hh
          rcases prime_six_classes p (by omega) with hp1 | hp5 <;>
            rcases hk with rfl | rfl <;> omega
        have hc : -144 * (n : ℚ) * ((n : ℚ) + -(k : ℚ) * (p : ℚ) / 6) *
            ((n : ℚ) + 2 * (-(k : ℚ) * (p : ℚ) / 6)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
            (Nat.cast_ne_zero.mpr hn)) h6n) h3n
        have hi := squareEuler_indicial (-(k : ℚ) * (p : ℚ) / 6) H n ih
        rw [he, coeff_zero] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left hc
  have hi := congrArg (fun F : ℚ[X] => F.comp (1 - X)) hH
  dsimp only [H] at hi
  rw [comp_assoc, show (1 - X : ℚ[X]).comp (1 - X) = X by simp,
    comp_X, zero_comp] at hi
  exact hi

/-- Exact Clausen at both original terminating nodes, retaining the whole e cutoff. -/
theorem actual_two_node_Jacobi_square (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    (nativeNodePolynomial p k).comp (1 - X ^ 2) = rankJacobiNode p k ^ 2 := by
  apply sub_eq_zero.mp
  apply rational_node_square_unique p k hp hk
  · simp [eval_sub, eval_comp, nativeNodePolynomial, coefficientPolynomial_origin,
      parameterCoefficient, clearedNumerator, clearedDenominator,
      rankJacobiNode_endpoint_one]
  · have hY := actual_rankJacobi_ODE p k (by omega) hk
    rw [jacobiSquare_sub, termRegular_jacobi_source,
      actual_nativeNodeRegular_ODE p k hp hk, zero_comp, mul_zero,
      jacobiSquare_source, hY, derivative_zero]
    ring

end WPMomentPrecision.TwoNodeSquare
