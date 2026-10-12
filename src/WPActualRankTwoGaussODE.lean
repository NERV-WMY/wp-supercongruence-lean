import WPActualRankTwoDividedDifference

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualRankTwoParameter WPActualNativeFirstJet
  WPActualNativeSecondTaylor WPActualRankTwoDividedDifference

namespace WPActualRankTwoGaussODE

noncomputable def rankEuler {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  36 * theta (integerShift 1 t P) -
    X * integerShift 6 (1 + 6 * t) (integerShift 6 (5 + 6 * t) P)

noncomputable def rankRegular {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  36 * X * (1 - X) * P.derivative.derivative +
    36 * (C (1 + t) - C (2 + 2 * t) * X) * P.derivative -
    C ((1 + 6 * t) * (5 + 6 * t)) * P

theorem rankEuler_eq_X_regular {K : Type*} [CommRing K] (t : K) (P : K[X]) :
    rankEuler t P = X * rankRegular t P := by
  simp [rankEuler, rankRegular, theta, integerShift, derivative_mul, map_ofNat]
  ring

theorem rankEuler_coeff_zero {K : Type*} [CommRing K] (t : K) (P : K[X]) :
    (rankEuler t P).coeff 0 = 0 := by
  simp [rankEuler, theta_coeff]

theorem rankEuler_coeff_succ {K : Type*} [CommRing K] (t : K) (P : K[X]) (n : ℕ) :
    (rankEuler t P).coeff (n + 1) =
      36 * ((n : K) + 1) * ((n : K) + 1 + t) * P.coeff (n + 1) -
      (6 * (n : K) + 1 + 6 * t) * (6 * (n : K) + 5 + 6 * t) * P.coeff n := by
  simp only [rankEuler, coeff_sub, coeff_ofNat_mul, theta_coeff,
    coeff_X_mul, integerShift_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem rankDenominator_rational_node_ne_zero (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (rankDenominator ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6) ≠ 0 := by
  have h := (rankDenominator_node_unit p n hp hn k).1
  rwa [evaluate_subtype, rankDenominator_map, rankNode_value] at h

/-- The literal finite quotient recurrence, with actual denominator units. -/
theorem actual_rankCoefficient_recurrence (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    36 * ((n : ℚ) + 1) * ((n : ℚ) + 1 - (k : ℚ) * (p : ℚ) / 6) *
      rankCoefficient (n + 1) (-(k : ℚ) * (p : ℚ) / 6) =
    (6 * (n : ℚ) + 1 - (k : ℚ) * (p : ℚ)) *
      (6 * (n : ℚ) + 5 - (k : ℚ) * (p : ℚ)) *
      rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6) := by
  have hD := rankDenominator_rational_node_ne_zero p n k hp (by omega)
  have hDnext := rankDenominator_rational_node_ne_zero p (n + 1) k hp hn
  rw [rankDenominator_eval_succ] at hDnext
  have hB := (mul_ne_zero_iff.mp hDnext).2
  have hf (a u d b : ℚ) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by
    field_simp [hd, hb]
  unfold rankCoefficient
  rw [rankNumerator_eval_succ, rankDenominator_eval_succ]
  convert hf ((rankNumerator ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6))
    ((6 * (n : ℚ) + 1 + 6 * (-(k : ℚ) * (p : ℚ) / 6)) *
      (6 * (n : ℚ) + 5 + 6 * (-(k : ℚ) * (p : ℚ) / 6)))
    ((rankDenominator ℚ n).eval (-(k : ℚ) * (p : ℚ) / 6))
    (36 * ((n : ℚ) + 1) * ((n : ℚ) + 1 + (-(k : ℚ) * (p : ℚ) / 6))) hD hB using 1 <;> ring

theorem actual_rankCoefficient_termination (p k n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hk : k = 1 ∨ k = 5) (hn : p - 1 - p / 6 < n) :
    rankCoefficient n (-(k : ℚ) * (p : ℚ) / 6) = 0 := by
  rcases hk with rfl | rfl
  · simp only [Nat.cast_one, neg_one_mul, rankCoefficient]
    rw [actual_low_rankNumerator_zero p n hp (by omega), zero_div]
  · simp only [Nat.cast_ofNat, rankCoefficient]
    rw [actual_high_rankNumerator_zero p n hp hn, zero_div]

/-- The terminal recurrence coefficient is checked for both actual terminating nodes. -/
theorem actual_rankNodeEuler_ODE (p k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hk : k = 1 ∨ k = 5) :
    rankEuler (-(k : ℚ) * (p : ℚ) / 6) (rankNodePolynomial p k) = 0 := by
  ext j
  cases j with
  | zero => rw [rankEuler_coeff_zero, Polynomial.coeff_zero]
  | succ n =>
    rw [rankEuler_coeff_succ, Polynomial.coeff_zero]
    simp only [rankNodePolynomial, coefficientPolynomial_coeff]
    by_cases hn : n + 1 < p - 1 - p / 6 + 1
    · rw [if_pos hn, if_pos (by omega)]
      have h := actual_rankCoefficient_recurrence p n k hp (by omega)
      linear_combination h
    · rw [if_neg hn]
      by_cases hn0 : n < p - 1 - p / 6 + 1
      · rw [if_pos hn0]
        have he : n = p - 1 - p / 6 := by omega
        have h := actual_rankCoefficient_recurrence p n k hp (by omega)
        rw [actual_rankCoefficient_termination p k (n + 1) hp hk (by omega), mul_zero] at h
        linear_combination h
      · rw [if_neg hn0]
        ring

theorem actual_rankNodeRegular_ODE (p k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hk : k = 1 ∨ k = 5) :
    rankRegular (-(k : ℚ) * (p : ℚ) / 6) (rankNodePolynomial p k) = 0 := by
  have h : X * rankRegular (-(k : ℚ) * (p : ℚ) / 6) (rankNodePolynomial p k) = 0 := by
    rw [← rankEuler_eq_X_regular, actual_rankNodeEuler_ODE p k hp hk]
  exact (mul_eq_zero.mp h).resolve_left Polynomial.X_ne_zero

noncomputable def rankJacobiClear {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  36 * (1 - X ^ 2) * P.derivative.derivative -
    72 * C (1 + t) * X * P.derivative - C ((1 + 6 * t) * (5 + 6 * t)) * P

theorem derivative_jacobi_comp (P : ℚ[X]) :
    (P.comp (C (1 / 2) * (1 - X))).derivative =
      C (-1 / 2) * P.derivative.comp (C (1 / 2) * (1 - X)) := by
  rw [show (-1 / 2 : ℚ) = -(1 / 2 : ℚ) by ring, map_neg]
  simp [Polynomial.derivative_comp, Polynomial.derivative_mul]

theorem second_derivative_jacobi_comp (P : ℚ[X]) :
    (P.comp (C (1 / 2) * (1 - X))).derivative.derivative =
      C (1 / 4) * P.derivative.derivative.comp (C (1 / 2) * (1 - X)) := by
  rw [derivative_jacobi_comp, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_jacobi_comp]
  rw [← mul_assoc, ← map_mul]
  norm_num

theorem rankRegular_jacobi_comp (t : ℚ) (P : ℚ[X]) :
    (rankRegular t P).comp (C (1 / 2) * (1 - X)) =
      rankJacobiClear t (P.comp (C (1 / 2) * (1 - X))) := by
  unfold rankJacobiClear
  rw [second_derivative_jacobi_comp, derivative_jacobi_comp]
  simp [rankRegular, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp,
    map_ofNat, show (-1 / 2 : ℚ) = -(1 / 2 : ℚ) by ring]
  ring_nf
  simp only [← map_mul, ← map_pow]
  norm_num
  have hab : C (1 / 2 : ℚ) = (2 : ℚ[X]) * C (1 / 4 : ℚ) := by
    rw [show (1 / 2 : ℚ) = 2 * (1 / 4 : ℚ) by norm_num, map_mul, map_ofNat]
  have h2 : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    rw [show (2 : ℚ[X]) = C (2 : ℚ) by rfl, ← map_mul]
    norm_num
  linear_combination
    (36 * (1 - X) * P.derivative.derivative.comp (C (1 / 2) - C (1 / 2) * X)) * hab -
    (36 * (1 + C t) * P.derivative.comp (C (1 / 2) - C (1 / 2) * X)) * h2

theorem actual_rankJacobi_ODE (p k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hk : k = 1 ∨ k = 5) :
    rankJacobiClear (-(k : ℚ) * (p : ℚ) / 6) (rankJacobiNode p k) = 0 := by
  rw [rankJacobiNode, ← rankRegular_jacobi_comp,
    actual_rankNodeRegular_ODE p k hp hk, Polynomial.zero_comp]

theorem rankJacobiClear_sub {K : Type*} [CommRing K] (t : K) (P Q : K[X]) :
    rankJacobiClear t (P - Q) = rankJacobiClear t P - rankJacobiClear t Q := by
  simp [rankJacobiClear, Polynomial.derivative_sub]
  ring

theorem rankJacobiClear_C_mul {K : Type*} [CommRing K] (t a : K) (P : K[X]) :
    rankJacobiClear t (C a * P) = C a * rankJacobiClear t P := by
  simp [rankJacobiClear, Polynomial.derivative_mul]
  ring

/-- The full change of operator between the two actual nodes. -/
theorem rankJacobiClear_two_parameters (p : ℕ) (P : ℚ[X]) :
    rankJacobiClear (-5 * (p : ℚ) / 6) P - rankJacobiClear (-(p : ℚ) / 6) P =
      C (24 * (p : ℚ)) * (2 * X * P.derivative + C (1 - (p : ℚ)) * P) := by
  have h5 : (-5 * (p : ℚ) / 6) = -5 * ((p : ℚ) / 6) := by ring
  have h1 : (-(p : ℚ) / 6) = -((p : ℚ) / 6) := by ring
  have hp6 : (p : ℚ) = 6 * ((p : ℚ) / 6) := by ring
  rw [h5, h1]
  conv_rhs => rw [hp6]
  simp [rankJacobiClear, map_mul, map_add, map_sub, map_neg, map_ofNat]
  ring

/-- The actual NC80 divided source. Every term proportional to p is retained. -/
theorem actual_rankDividedJacobi_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankJacobiClear (-(p : ℚ) / 6) (rankDividedJacobi p) =
      36 * (2 * X * (rankJacobiNode p 5).derivative +
        C (1 - (p : ℚ)) * rankJacobiNode p 5) := by
  have h1 := actual_rankJacobi_ODE p 1 hp (Or.inl rfl)
  have h5 := actual_rankJacobi_ODE p 5 hp (Or.inr rfl)
  norm_num only [Nat.cast_one, Nat.cast_ofNat, neg_one_mul] at h1 h5
  have hd := congrArg (rankJacobiClear (-(p : ℚ) / 6))
    (actual_two_jacobi_node_difference p hp)
  rw [rankJacobiClear_sub, rankJacobiClear_C_mul, h1, zero_sub] at hd
  have ho := rankJacobiClear_two_parameters p (rankJacobiNode p 5)
  rw [h5, zero_sub] at ho
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hc : C (2 * (p : ℚ) / 3) ≠ (0 : ℚ[X]) := by simp [hpq]
  apply mul_left_cancel₀ hc
  rw [← hd, ho]
  have h24 : (24 * (p : ℚ)) = (2 * (p : ℚ) / 3) * 36 := by ring
  rw [h24, map_mul]
  simp only [map_ofNat]
  ring

noncomputable def legendreJacobi {K : Type*} [CommRing K] (d : ℕ) (P : K[X]) : K[X] :=
  (1 - X ^ 2) * P.derivative.derivative - 2 * X * P.derivative +
    C ((d : K) * ((d : K) + 1)) * P

/-- The actual low operator in NC80, valid in both prime classes modulo six. -/
theorem actual_low_rankJacobi_operator (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (P : ℚ[X]) :
    rankJacobiClear (-(p : ℚ) / 6) P =
      36 * legendreJacobi (p / 6) P +
        C (12 * (p : ℚ)) * (X * P.derivative - C ((p / 6 : ℕ) : ℚ) * P) := by
  have hs : (1 - (p : ℚ)) * (5 - (p : ℚ)) =
      12 * (p : ℚ) * ((p / 6 : ℕ) : ℚ) -
        36 * ((p / 6 : ℕ) : ℚ) * (((p / 6 : ℕ) : ℚ) + 1) := by
    rcases WPActualNativeParameter.prime_six_classes p hp with h1 | h5
    · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast h1
      rw [hq]
      ring
    · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast h5
      rw [hq]
      ring
  have hd := congrArg (C : ℚ → ℚ[X])
    (show 72 * (1 - (p : ℚ) / 6) = 72 - 12 * (p : ℚ) by ring)
  have hc := congrArg (C : ℚ → ℚ[X]) hs
  unfold rankJacobiClear legendreJacobi
  rw [show 1 + 6 * (-(p : ℚ) / 6) = 1 - (p : ℚ) by ring,
    show 5 + 6 * (-(p : ℚ) / 6) = 5 - (p : ℚ) by ring,
    show 1 + (-(p : ℚ) / 6) = 1 - (p : ℚ) / 6 by ring]
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat] at hd hc ⊢
  linear_combination -(X * P.derivative) * hd - P * hc

theorem actual_low_rankJacobi_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (rankJacobiNode p 1) +
      C (12 * (p : ℚ)) * (X * (rankJacobiNode p 1).derivative -
        C ((p / 6 : ℕ) : ℚ) * rankJacobiNode p 1) = 0 := by
  rw [← actual_low_rankJacobi_operator p hp]
  simpa only [Nat.cast_one, neg_one_mul] using actual_rankJacobi_ODE p 1 hp (Or.inl rfl)

end WPActualRankTwoGaussODE
