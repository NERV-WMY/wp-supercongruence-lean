import WPActualNativeJacobiJet
import WPActualNativeChiTaylor
import WPActualRankTwoGaussODE

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeParameter WPActualNativeJetRecurrence
  WPActualNativeChiTaylor WPActualRankTwoParameter WPActualRankTwoGaussODE
  WPHasseCubicSource WPPIntegralReduction WPNativeParameterTaylor WPActualNativeFirstJet

namespace WPFieldAssembly.TerminatingSquare

set_option maxHeartbeats 1200000

/-- The exact deformed native operator, including both lower parameter shifts. -/
noncomputable def termEuler {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  72 * theta (integerShift 1 t (integerShift 1 (2 * t) P)) -
    X * integerShift 6 (1 + 6 * t)
      (integerShift 2 (1 + 2 * t) (integerShift 6 (5 + 6 * t) P))

noncomputable def termRegular {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  72 * X ^ 2 * (1 - X) * P.derivative.derivative.derivative +
    (216 * C (1 + t) * X * (1 - X) - 108 * X ^ 2) * P.derivative.derivative +
    (C (72 * (1 + t) * (1 + 2 * t)) -
      C (226 + 432 * t + 216 * t ^ 2) * X) * P.derivative -
    C ((1 + 6 * t) * (5 + 6 * t) * (1 + 2 * t)) * P

theorem termEuler_eq_X_regular {K : Type*} [CommRing K] (t : K) (P : K[X]) :
    termEuler t P = X * termRegular t P := by
  simp [termEuler, termRegular, integerShift, theta, derivative_mul, map_mul,
    map_add, map_pow, map_ofNat]
  ring

theorem termEuler_coeff_zero {K : Type*} [CommRing K] (t : K) (P : K[X]) :
    (termEuler t P).coeff 0 = 0 := by
  simp [termEuler, theta_coeff]

theorem termEuler_coeff_succ {K : Type*} [CommRing K] (t : K) (P : K[X]) (n : ℕ) :
    (termEuler t P).coeff (n + 1) =
      72 * ((n : K) + 1) * ((n : K) + 1 + t) * ((n : K) + 1 + 2 * t) * P.coeff (n + 1) -
      (6 * (n : K) + 1 + 6 * t) * (2 * (n : K) + 1 + 2 * t) *
        (6 * (n : K) + 5 + 6 * t) * P.coeff n := by
  simp only [termEuler, coeff_sub, coeff_ofNat_mul, theta_coeff, coeff_X_mul,
    integerShift_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem actual_parameterCoefficient_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n + 1 < p) :
    (lowerFactor ℚ n).eval (-(p : ℚ) / 6) * parameterCoefficient (n + 1) (-(p : ℚ) / 6) =
      (upperFactor ℚ n).eval (-(p : ℚ) / 6) * parameterCoefficient n (-(p : ℚ) / 6) := by
  have hD : (clearedDenominator ℚ n).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p n (by omega) (by omega)).1
    rwa [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
  have hDn : (clearedDenominator ℚ (n + 1)).eval (-(p : ℚ) / 6) ≠ 0 := by
    have h := (denominator_node_unit p (n + 1) (by omega) hn).1
    rwa [evaluate_subtype, clearedDenominator_map, integralNode_value] at h
  rw [actual_parameter_denominator_succ, eval_mul] at hDn
  have hL := (mul_ne_zero_iff.mp hDn).2
  have hf (a u d b : ℚ) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by
    field_simp [hd, hb]
  unfold parameterCoefficient
  rw [actual_parameter_numerator_succ, actual_parameter_denominator_succ, eval_mul, eval_mul]
  exact hf _ _ _ _ hD hL

/-- The complete terminating cutoff has no discarded terminal source. -/
theorem actual_nativeTermEuler_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    termEuler (-(p : ℚ) / 6) (nativeTermPolynomial p) = 0 := by
  have hd := nativeTermPolynomial_degree p (by omega)
  have hN : p / 6 < (p - 1) / 2 := by
    have hdiv := Nat.div_mul_le_self p 6
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  ext j
  cases j with
  | zero => rw [termEuler_coeff_zero, coeff_zero]
  | succ n =>
    rw [termEuler_coeff_succ, coeff_zero]
    by_cases hn : n + 1 ≤ (p - 1) / 2
    · rw [nativeTermPolynomial_coeff, nativeTermPolynomial_coeff,
        if_pos (by omega), if_pos (by omega)]
      have he := actual_parameterCoefficient_recurrence p n hp (by
        have := WPFiniteWSource.half_exponent p hp
        omega)
      simp only [lowerFactor, upperFactor, eval_mul, eval_C, eval_add, eval_ofNat,
        eval_X] at he
      linear_combination he
    · rw [coeff_eq_zero_of_natDegree_lt (by omega :
          (nativeTermPolynomial p).natDegree < n + 1),
        coeff_eq_zero_of_natDegree_lt (by omega : (nativeTermPolynomial p).natDegree < n)]
      ring

theorem actual_nativeTermRegular_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    termRegular (-(p : ℚ) / 6) (nativeTermPolynomial p) = 0 := by
  have he : X * termRegular (-(p : ℚ) / 6) (nativeTermPolynomial p) = 0 := by
    rw [← termEuler_eq_X_regular, actual_nativeTermEuler_ODE p hp]
  exact (mul_eq_zero.mp he).resolve_left X_ne_zero

noncomputable def jacobiSquare {K : Type*} [CommRing K] (t : K) (P : K[X]) : K[X] :=
  36 * (1 - X ^ 2) ^ 2 * P.derivative.derivative.derivative -
    216 * C (1 + t) * X * (1 - X ^ 2) * P.derivative.derivative +
    (-72 * C (1 + t) * (1 - X ^ 2) +
      144 * C ((1 + t) * (1 + 2 * t)) * X ^ 2 -
      4 * C ((1 + 6 * t) * (5 + 6 * t)) * (1 - X ^ 2)) * P.derivative +
    4 * C ((1 + 6 * t) * (5 + 6 * t) * (1 + 2 * t)) * X * P

theorem jacobiSquare_source {K : Type*} [CommRing K] (t : K) (Y : K[X]) :
    jacobiSquare t (Y ^ 2) =
      2 * (1 - X ^ 2) * Y * (rankJacobiClear t Y).derivative +
        (6 * (1 - X ^ 2) * Y.derivative - 4 * C (1 + 2 * t) * X * Y) *
          rankJacobiClear t Y := by
  simp [jacobiSquare, rankJacobiClear, derivative_mul, derivative_pow_succ,
    map_mul, map_add, map_ofNat]
  ring

theorem termRegular_jacobi_source {K : Type*} [CommRing K] (t : K) (F : K[X]) :
    jacobiSquare t (F.comp (1 - X ^ 2)) =
      -4 * X * (termRegular t F).comp (1 - X ^ 2) := by
  simp [jacobiSquare, termRegular, derivative_comp, derivative_mul,
    derivative_pow_succ, derivative_sub, map_mul, map_add, map_pow, map_ofNat,
    Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.pow_comp]
  ring

noncomputable def squareE3 {K : Type*} [CommRing K] : K[X] := -36 * (2 - X) ^ 2
noncomputable def squareE2 {K : Type*} [CommRing K] (t : K) : K[X] :=
  -216 * C (1 + t) * (1 - X) * (2 - X) - 3 * squareE3
noncomputable def squareE1 {K : Type*} [CommRing K] (t : K) : K[X] :=
  72 * C (1 + t) * X * (2 - X) -
    144 * C ((1 + t) * (1 + 2 * t)) * (1 - X) ^ 2 +
    4 * C ((1 + 6 * t) * (5 + 6 * t)) * X * (2 - X) - squareE2 t - squareE3
noncomputable def squareE0 {K : Type*} [CommRing K] (t : K) : K[X] :=
  4 * C ((1 + 6 * t) * (5 + 6 * t) * (1 + 2 * t)) * (1 - X) * X

theorem jacobiSquare_euler {K : Type*} [CommRing K] (t : K) (P : K[X]) :
    regularEuler squareE3 (squareE2 t) (squareE1 t) (squareE0 t) (P.comp (1 - X)) =
      X * (jacobiSquare t P).comp (1 - X) := by
  simp [regularEuler, squareE3, squareE2, squareE1, squareE0, jacobiSquare,
    theta, derivative_mul, derivative_comp, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.pow_comp]
  ring

theorem squareEuler_indicial (t : ℚ) (P : ℚ[X]) (n : ℕ)
    (hP : ∀ k < n, P.coeff k = 0) :
    (regularEuler squareE3 (squareE2 t) (squareE1 t) (squareE0 t) P).coeff n =
      (-144 * (n : ℚ) * ((n : ℚ) + t) * ((n : ℚ) + 2 * t)) * P.coeff n := by
  rw [regularEuler_indicial _ _ _ _ _ n hP]
  simp [squareE3, squareE2, squareE1, squareE0, coeff_zero_eq_eval_zero]
  ring

theorem rational_jacobi_square_unique (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : ℚ[X]) (h1 : P.eval 1 = 0) (hODE : jacobiSquare (-(p : ℚ) / 6) P = 0) : P = 0 := by
  let H := P.comp (1 - X)
  have hH : H = 0 := by
    have he : regularEuler squareE3 (squareE2 (-(p : ℚ) / 6))
        (squareE1 (-(p : ℚ) / 6)) (squareE0 (-(p : ℚ) / 6)) H = 0 := by
      dsimp only [H]
      rw [jacobiSquare_euler, hODE, zero_comp, mul_zero]
    ext n
    rw [coeff_zero]
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [H, coeff_zero_eq_eval_zero, eval_comp] using h1
      · have h2 : ¬2 ∣ p := by
          intro hd
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h <;> omega
        have h3 : ¬3 ∣ p := by
          intro hd
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h <;> omega
        have h6n : (n : ℚ) + -(p : ℚ) / 6 ≠ 0 := by
          intro hz
          have hh : 6 * (n : ℚ) = p := by linarith
          have hi : 6 * n = p := by exact_mod_cast hh
          apply h2
          exact ⟨3 * n, by omega⟩
        have h3n : (n : ℚ) + 2 * (-(p : ℚ) / 6) ≠ 0 := by
          intro hz
          have hh : 3 * (n : ℚ) = p := by linarith
          have hi : 3 * n = p := by exact_mod_cast hh
          exact h3 ⟨n, hi.symm⟩
        have hc : -144 * (n : ℚ) * ((n : ℚ) + -(p : ℚ) / 6) *
            ((n : ℚ) + 2 * (-(p : ℚ) / 6)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
            (Nat.cast_ne_zero.mpr hn)) h6n) h3n
        have hi := squareEuler_indicial (-(p : ℚ) / 6) H n ih
        rw [he, coeff_zero] at hi
        exact (mul_eq_zero.mp hi.symm).resolve_left hc
  have hi := congrArg (fun F : ℚ[X] => F.comp (1 - X)) hH
  dsimp only [H] at hi
  rw [comp_assoc, show (1 - X : ℚ[X]).comp (1 - X) = X by simp,
    comp_X, zero_comp] at hi
  exact hi

theorem jacobiSquare_sub {K : Type*} [CommRing K] (t : K) (P Q : K[X]) :
    jacobiSquare t (P - Q) = jacobiSquare t P - jacobiSquare t Q := by
  simp only [jacobiSquare, derivative_sub]
  ring

/-- Exact rational terminating Clausen identity, before any division or field reduction. -/
theorem actual_terminating_Jacobi_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeTermPolynomial p).comp (1 - X ^ 2) = rankJacobiNode p 1 ^ 2 := by
  apply sub_eq_zero.mp
  apply rational_jacobi_square_unique p hp
  · simp [eval_sub, eval_comp, nativeTermPolynomial_origin, rankJacobiNode,
      rankNodePolynomial_origin]
  · have hY : rankJacobiClear (-(p : ℚ) / 6) (rankJacobiNode p 1) = 0 := by
      simpa only [Nat.cast_one, neg_one_mul] using
        actual_rankJacobi_ODE p 1 (by omega) (Or.inl rfl)
    rw [jacobiSquare_sub, termRegular_jacobi_source, actual_nativeTermRegular_ODE p hp,
      zero_comp, mul_zero, jacobiSquare_source, hY,
      derivative_zero]
    ring

theorem rational_native_V_conic :
    WPActualPullbackSource.Vpolynomial.comp (WPFiniteJHighCoefficient.conic : ℚ[X]) =
      1 - WPFiniteCubicLog.Tc ^ 2 := by
  have hu : (125 : ℚ[X]) * C (1 / 125 : ℚ) = 1 := by
    change C (125 : ℚ) * C (1 / 125 : ℚ) = 1
    rw [← C_mul]
    norm_num
  simp only [WPActualPullbackSource.Vpolynomial, mul_comp, pow_comp, sub_comp,
    ofNat_comp, one_comp, X_comp, C_comp]
  unfold WPFiniteJHighCoefficient.conic WPFiniteCubicLog.Tc
  linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * hu

theorem actual_terminating_V_conic_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((nativeTermPolynomial p).comp WPActualPullbackSource.Vpolynomial).comp
        (WPFiniteJHighCoefficient.conic : ℚ[X]) =
      ((rankJacobiNode p 1).comp WPFiniteCubicLog.Tc) ^ 2 := by
  have he := congrArg (fun P : ℚ[X] => P.comp WPFiniteCubicLog.Tc)
    (actual_terminating_Jacobi_square p hp)
  rw [comp_assoc, rational_native_V_conic]
  simpa only [comp_assoc, sub_comp, one_comp, pow_comp, X_comp] using he

noncomputable def jacobiDiscriminant {K : Type*} [CommRing K] (t : K) (G : K[X]) : K[X] :=
  9 * (1 - X ^ 2) * (2 * G * G.derivative.derivative - G.derivative ^ 2) -
    36 * C (1 + t) * X * G * G.derivative -
    C ((1 + 6 * t) * (5 + 6 * t)) * G ^ 2

/-- The whole discriminant source has its actual Pearson weight. -/
theorem jacobiDiscriminant_source {K : Type*} [CommRing K] (t : K) (G : K[X]) :
    2 * (1 - X ^ 2) * (jacobiDiscriminant t G).derivative -
      4 * C (1 + 2 * t) * X * jacobiDiscriminant t G =
        G * jacobiSquare t G := by
  simp [jacobiDiscriminant, jacobiSquare, derivative_mul, derivative_pow_succ,
    map_mul, map_add, map_ofNat]
  ring

/-- At zero parameter the primitive differentiates the weighted discriminant. -/
theorem jacobiDiscriminant_zero_source {K : Type*} [CommRing K] (G : K[X]) :
    2 * ((1 - X ^ 2) * jacobiDiscriminant 0 G).derivative =
      G * jacobiSquare 0 G := by
  have he := jacobiDiscriminant_source (0 : K) G
  simp [derivative_mul, derivative_pow_succ] at he ⊢
  linear_combination he

theorem jacobiDiscriminant_square {K : Type*} [CommRing K] (t : K) (Y : K[X]) :
    jacobiDiscriminant t (Y ^ 2) = Y ^ 3 * rankJacobiClear t Y := by
  simp [jacobiDiscriminant, rankJacobiClear, derivative_mul, derivative_pow_succ]
  ring

theorem actual_terminating_discriminant (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    jacobiDiscriminant (-(p : ℚ) / 6) ((nativeTermPolynomial p).comp (1 - X ^ 2)) = 0 := by
  have hY : rankJacobiClear (-(p : ℚ) / 6) (rankJacobiNode p 1) = 0 := by
    simpa only [Nat.cast_one, neg_one_mul] using
      actual_rankJacobi_ODE p 1 (by omega) (Or.inl rfl)
  rw [actual_terminating_Jacobi_square p hp, jacobiDiscriminant_square, hY, mul_zero]

theorem jacobiDiscriminant_parameter {K : Type*} [CommRing K] (t : K) (G : K[X]) :
    jacobiDiscriminant 0 G - jacobiDiscriminant t G =
      36 * C t * X * G * G.derivative + 36 * C (t * (1 + t)) * G ^ 2 := by
  simp [jacobiDiscriminant, map_add, map_mul, map_ofNat]
  ring

/-- Actual first divided source of the rational terminating square, without field division by p. -/
theorem actual_terminating_discriminant_carry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let G := (nativeTermPolynomial p).comp (1 - X ^ 2)
    jacobiDiscriminant 0 G = C (p : ℚ) *
      (-6 * X * G * G.derivative - 6 * G ^ 2 + C (p : ℚ) * G ^ 2) := by
  dsimp only
  let G := (nativeTermPolynomial p).comp (1 - X ^ 2)
  have hphase := jacobiDiscriminant_parameter (-(p : ℚ) / 6) G
  have hzero := actual_terminating_discriminant p hp
  have h6 : (6 : ℚ[X]) * C (-(p : ℚ) / 6) = -C (p : ℚ) := by
    have hq : 6 * (-(p : ℚ) / 6) = -(p : ℚ) := by ring
    simpa only [map_mul, map_ofNat, map_neg] using congrArg (C : ℚ → ℚ[X]) hq
  simp only [map_mul, map_add, map_one] at hphase
  linear_combination hphase + hzero +
    (6 * X * G * G.derivative + 6 * G ^ 2 +
      (6 * C (-(p : ℚ) / 6) - C (p : ℚ)) * G ^ 2) * h6

theorem actual_terminating_discriminant_divided (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let G := (nativeTermPolynomial p).comp (1 - X ^ 2)
    C (1 / (p : ℚ)) * jacobiDiscriminant 0 G =
      -6 * X * G * G.derivative - 6 * G ^ 2 + C (p : ℚ) * G ^ 2 := by
  dsimp only
  rw [actual_terminating_discriminant_carry p hp]
  have hu : (C (1 / (p : ℚ)) : ℚ[X]) * C (p : ℚ) = 1 := by
    rw [← C_mul, one_div_mul_cancel (by positivity : (p : ℚ) ≠ 0), C_1]
  rw [← mul_assoc, hu, one_mul]

noncomputable def integralTermPolynomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  ∑ n : Fin ((p - 1) / 2 + 1), monomial n.val
    (integralParameterCoefficient p n.val (by omega) (by have := n.isLt; omega))

theorem integralTermPolynomial_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralTermPolynomial p hp).map (integralRationals p).subtype = nativeTermPolynomial p := by
  simp only [integralTermPolynomial, Polynomial.map_sum, map_monomial,
    Subring.coe_subtype, integralParameterCoefficient_value]
  unfold nativeTermPolynomial
  exact Fin.sum_univ_eq_sum_range
    (fun n => monomial n (parameterCoefficient n (-(p : ℚ) / 6))) ((p - 1) / 2 + 1)

theorem integralTermPolynomial_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralTermPolynomial p hp).map (residueHom p) = nativeField p (p / 6) := by
  simp only [integralTermPolynomial, Polynomial.map_sum, map_monomial,
    actual_parameterCoefficient_residue]
  have he : (∑ n : Fin ((p - 1) / 2 + 1), monomial n.val
      (WPReview.nativeCoefficient n.val : ZMod p)) = nativeField p ((p - 1) / 2) := by
    unfold nativeField
    exact Fin.sum_univ_eq_sum_range
      (fun n => monomial n (WPReview.nativeCoefficient n : ZMod p)) ((p - 1) / 2 + 1)
  rw [he, actual_full_native_field_cutoff p ((p - 1) / 2) (by omega) (by omega) (by
    have := Nat.div_mul_le_self p 6
    have := WPFiniteWSource.half_exponent p hp
    omega)]

noncomputable def integralJacobiTerm (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := (integralTermPolynomial p hp).comp (1 - X ^ 2)

theorem integralJacobiTerm_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralJacobiTerm p hp).map (integralRationals p).subtype =
      (nativeTermPolynomial p).comp (1 - X ^ 2) := by
  rw [integralJacobiTerm, Polynomial.map_comp, integralTermPolynomial_rational]
  simp

theorem integralJacobiTerm_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralJacobiTerm p hp).map (residueHom p) =
      WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2 := by
  rw [integralJacobiTerm, Polynomial.map_comp, integralTermPolynomial_field]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  exact WPActualNativeQuadraticSquare.actual_native_Jacobi_square p hp

/-- The actual integral witness for the Q-divided discriminant, retaining its p-dependent row. -/
noncomputable def integralDiscriminantCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  -6 * X * integralJacobiTerm p hp * (integralJacobiTerm p hp).derivative -
    6 * integralJacobiTerm p hp ^ 2 + C (p : integralRationals p) * integralJacobiTerm p hp ^ 2

theorem integralDiscriminantCarry_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralDiscriminantCarry p hp).map (integralRationals p).subtype =
      C (1 / (p : ℚ)) * jacobiDiscriminant 0 ((nativeTermPolynomial p).comp (1 - X ^ 2)) := by
  rw [actual_terminating_discriminant_divided p hp]
  simp only [integralDiscriminantCarry, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_pow, ← derivative_map, integralJacobiTerm_rational]
  simp only [map_natCast]
  rw [Polynomial.map_natCast]

theorem integralDiscriminantCarry_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralDiscriminantCarry p hp).map (residueHom p) =
      -6 * X * WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2 *
        (WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2).derivative -
        6 * WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 4 := by
  simp only [integralDiscriminantCarry, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_pow, ← derivative_map, integralJacobiTerm_field]
  simp only [map_natCast]
  have hpzero : (p : (ZMod p)[X]) = 0 := by
    rw [← C_eq_natCast, ZMod.natCast_self, C_0]
  rw [Polynomial.map_natCast, hpzero, zero_mul, add_zero]
  ring

theorem actual_divided_discriminant_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((C (1 / (p : ℚ)) *
      jacobiDiscriminant 0 ((nativeTermPolynomial p).comp (1 - X ^ 2))).coeff n) := by
  rw [← integralDiscriminantCarry_rational p hp, coeff_map]
  exact ((integralDiscriminantCarry p hp).coeff n).property

theorem actual_divided_discriminant_coefficient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    (((C (1 / (p : ℚ)) * jacobiDiscriminant 0
      ((nativeTermPolynomial p).comp (1 - X ^ 2))).coeff n : ℚ) : ZMod p) =
      (-6 * X * WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2 *
        (WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2).derivative -
        6 * WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 4).coeff n := by
  rw [← integralDiscriminantCarry_rational p hp, coeff_map,
    ← integralDiscriminantCarry_field p hp, coeff_map]
  rfl

end WPFieldAssembly.TerminatingSquare
