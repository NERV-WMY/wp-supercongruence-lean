import WPFieldAssembly.TerminatingSquare
import WPActualNativeSecondTaylor

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeParameter WPActualNativeJetRecurrence
  WPActualNativeChiTaylor WPActualRankTwoParameter WPActualRankTwoGaussODE
  WPHasseCubicSource WPPIntegralReduction WPNativeParameterTaylor WPActualNativeFirstJet
  WPActualNativeSecondTaylor WPFieldAssembly.TerminatingSquare

namespace WPFieldAssembly.NativeTerminatingNodes

set_option maxHeartbeats 1200000

/-- Literal native quotient at each actual node, with the full upper cutoff. -/
noncomputable def nativeNodeAt (p k : ℕ) : ℚ[X] :=
  coefficientPolynomial (p - 1 - p / 6)
    (fun n => parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6))

theorem nativeNodeAt_coeff (p k n : ℕ) :
    (nativeNodeAt p k).coeff n =
      if n < p - 1 - p / 6 + 1 then
        parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6)
      else 0 := by
  rw [nativeNodeAt, coefficientPolynomial_coeff]

theorem nativeNodeAt_origin (p k : ℕ) :
    (nativeNodeAt p k).eval 0 = 1 := by
  rw [nativeNodeAt, coefficientPolynomial_origin]
  simp [parameterCoefficient, clearedNumerator, clearedDenominator]

theorem nativeDenominator_node_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (k : ℕ) :
    ((clearedDenominator (integralRationals p) n).eval
      (rankNode p hp k)).val ≠ 0 ∧
    (((clearedDenominator (integralRationals p) n).eval
      (rankNode p hp k)).val)⁻¹ ∈ integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [← Polynomial.eval_map_apply, clearedDenominator_map, rankNode_residue]
  exact denominator_origin_residue_ne_zero p n hp hn

theorem nativeDenominator_rational_node_ne_zero (p n k : ℕ)
    [Fact p.Prime] (hp : 7 ≤ p) (hn : n < p) :
    (clearedDenominator ℚ n).eval
      (-(k : ℚ) * (p : ℚ) / 6) ≠ 0 := by
  have h := (nativeDenominator_node_unit p n hp hn k).1
  rwa [evaluate_subtype, clearedDenominator_map, rankNode_value] at h

theorem actual_native_node_coefficient_recurrence (p n k : ℕ)
    [Fact p.Prime] (hp : 7 ≤ p) (hn : n + 1 < p) :
    (lowerFactor ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6) *
        parameterCoefficient (n + 1) (-(k : ℚ) * (p : ℚ) / 6) =
      (upperFactor ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6) *
        parameterCoefficient n (-(k : ℚ) * (p : ℚ) / 6) := by
  have hD := nativeDenominator_rational_node_ne_zero p n k hp (by omega)
  have hDn := nativeDenominator_rational_node_ne_zero p (n + 1) k hp hn
  rw [actual_parameter_denominator_succ, eval_mul] at hDn
  have hL := (mul_ne_zero_iff.mp hDn).2
  have hf (a u d b : ℚ) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by
    field_simp [hd, hb]
  unfold parameterCoefficient
  rw [actual_parameter_numerator_succ, actual_parameter_denominator_succ,
    eval_mul, eval_mul]
  exact hf _ _ _ _ hD hL

/-- High-node termination includes its actual middle native upper factor. -/
theorem actual_high_nativeNumerator_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p - 1 - p / 6 < n) :
    (clearedNumerator ℚ n).eval (-(5 : ℚ) * (p : ℚ) / 6) = 0 := by
  rw [clearedNumerator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X]
  rcases prime_six_classes p hp with hp1 | hp5
  · have he : p - 1 - p / 6 = 5 * (p / 6) := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast hp1
    rw [he, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring
  · have he : p - 1 - p / 6 = 5 * (p / 6) + 4 := by omega
    have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast hp5
    rw [he, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hq]
    ring

theorem actual_high_nativeCoefficient_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : p - 1 - p / 6 < n) :
    parameterCoefficient n (-(5 : ℚ) * (p : ℚ) / 6) = 0 := by
  rw [parameterCoefficient, actual_high_nativeNumerator_zero p n hp hn, zero_div]

/-- The full high cutoff checks the recurrence at its terminal index. -/
theorem actual_high_nativeNodeEuler_ODE (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    termEuler (-(5 : ℚ) * (p : ℚ) / 6) (nativeNodeAt p 5) = 0 := by
  have he : p - 1 - p / 6 + 1 < p := by
    rcases prime_six_classes p (by omega) with h1 | h5 <;> omega
  ext j
  cases j with
  | zero => rw [termEuler_coeff_zero, Polynomial.coeff_zero]
  | succ n =>
      rw [termEuler_coeff_succ, Polynomial.coeff_zero]
      simp only [nativeNodeAt, coefficientPolynomial_coeff, Nat.cast_ofNat]
      by_cases hn : n + 1 < p - 1 - p / 6 + 1
      · rw [if_pos hn, if_pos (by omega)]
        have h := actual_native_node_coefficient_recurrence p n 5 (by omega) (by omega)
        simp only [lowerFactor, upperFactor, eval_mul, eval_C, eval_add,
          eval_ofNat, eval_X, Nat.cast_ofNat] at h
        linear_combination h
      · rw [if_neg hn]
        by_cases hn0 : n < p - 1 - p / 6 + 1
        · rw [if_pos hn0]
          have hterminal : n = p - 1 - p / 6 := by omega
          have h := actual_native_node_coefficient_recurrence p n 5 (by omega) (by omega)
          simp only [Nat.cast_ofNat] at h
          rw [actual_high_nativeCoefficient_zero p (n + 1)
            (by omega) (by omega), mul_zero] at h
          simp only [upperFactor, eval_mul, eval_C, eval_add,
            eval_ofNat, eval_X] at h
          linear_combination h
        · rw [if_neg hn0]
          ring

theorem actual_high_nativeNodeRegular_ODE (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    termRegular (-(5 : ℚ) * (p : ℚ) / 6) (nativeNodeAt p 5) = 0 := by
  have h : X * termRegular (-(5 : ℚ) * (p : ℚ) / 6) (nativeNodeAt p 5) = 0 := by
    rw [← termEuler_eq_X_regular, actual_high_nativeNodeEuler_ODE p hp]
  exact (mul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero

/-- Rational uniqueness at the actual high node uses the nonzero indicial pivot. -/
theorem rational_high_jacobi_square_unique (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (P : ℚ[X]) (h1 : P.eval 1 = 0)
    (hODE : jacobiSquare (-(5 : ℚ) * (p : ℚ) / 6) P = 0) :
    P = 0 := by
  let H := P.comp (1 - X)
  have hH : H = 0 := by
    have he : regularEuler squareE3
        (squareE2 (-(5 : ℚ) * (p : ℚ) / 6))
        (squareE1 (-(5 : ℚ) * (p : ℚ) / 6))
        (squareE0 (-(5 : ℚ) * (p : ℚ) / 6)) H = 0 := by
      dsimp only [H]
      rw [jacobiSquare_euler, hODE, zero_comp, mul_zero]
    ext n
    rw [coeff_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [H, coeff_zero_eq_eval_zero, eval_comp] using h1
      · have h2p : ¬2 ∣ p := by
          intro hd
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h <;> omega
        have h3p : ¬3 ∣ p := by
          intro hd
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h <;> omega
        have h2 : ¬2 ∣ 5 * p := by
          intro hd
          rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h5 | hp2
          · norm_num at h5
          · exact h2p hp2
        have h3 : ¬3 ∣ 5 * p := by
          intro hd
          rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h5 | hp3
          · norm_num at h5
          · exact h3p hp3
        have h6n : (n : ℚ) + -(5 : ℚ) * (p : ℚ) / 6 ≠ 0 := by
          intro hz
          have hh : 6 * (n : ℚ) = 5 * (p : ℚ) := by linarith
          have hi : 6 * n = 5 * p := by exact_mod_cast hh
          apply h2
          exact ⟨3 * n, by omega⟩
        have h3n : (n : ℚ) + 2 * (-(5 : ℚ) * (p : ℚ) / 6) ≠ 0 := by
          intro hz
          have hh : 3 * (n : ℚ) = 5 * (p : ℚ) := by linarith
          have hi : 3 * n = 5 * p := by exact_mod_cast hh
          exact h3 ⟨n, hi.symm⟩
        have hc : -144 * (n : ℚ) *
            ((n : ℚ) + -(5 : ℚ) * (p : ℚ) / 6) *
            ((n : ℚ) + 2 * (-(5 : ℚ) * (p : ℚ) / 6)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero
            (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn)) h6n) h3n
        have hi := squareEuler_indicial (-(5 : ℚ) * (p : ℚ) / 6) H n ih
        rw [he, coeff_zero] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left hc
  have hi := congrArg (fun F : ℚ[X] => F.comp (1 - X)) hH
  dsimp only [H] at hi
  rw [comp_assoc, show (1 - X : ℚ[X]).comp (1 - X) = X by simp,
    comp_X, zero_comp] at hi
  exact hi

theorem actual_nativeNodeAt_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeNodeAt p 1 = nativeTermPolynomial p := by
  have hcuts : p / 6 ≤ (p - 1) / 2 ∧
      (p - 1) / 2 ≤ p - 1 - p / 6 := by
    have hdiv := Nat.div_mul_le_self p 6
    have hhalf := WPFiniteWSource.half_exponent p hp
    omega
  ext n
  rw [nativeNodeAt_coeff, nativeTermPolynomial_coeff]
  simp only [Nat.cast_one, neg_one_mul]
  by_cases he : n < p - 1 - p / 6 + 1
  · rw [if_pos he]
    by_cases hN : n < (p - 1) / 2 + 1
    · rw [if_pos hN]
    · rw [if_neg hN, parameterCoefficient,
        terminating_numerator_zero p n (by omega) (by omega), zero_div]
  · rw [if_neg he, if_neg (by omega)]

/-- Exact rational square attachment for both original terminating nodes. -/
theorem actual_terminating_native_node_square (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    (nativeNodeAt p k).comp (1 - X ^ 2) = rankJacobiNode p k ^ 2 := by
  rcases hk with rfl | rfl
  · rw [actual_nativeNodeAt_one p hp]
    exact actual_terminating_Jacobi_square p hp
  · apply sub_eq_zero.mp
    apply rational_high_jacobi_square_unique p hp
    · simp [eval_sub, eval_comp, nativeNodeAt_origin, rankJacobiNode_endpoint_one]
    · have hY : rankJacobiClear (-(5 : ℚ) * (p : ℚ) / 6) (rankJacobiNode p 5) = 0 := by
        simpa only [Nat.cast_ofNat] using actual_rankJacobi_ODE p 5 (by omega) (Or.inr rfl)
      rw [jacobiSquare_sub, termRegular_jacobi_source,
        actual_high_nativeNodeRegular_ODE p hp, zero_comp, mul_zero,
        jacobiSquare_source, hY, derivative_zero]
      ring

end WPFieldAssembly.NativeTerminatingNodes
