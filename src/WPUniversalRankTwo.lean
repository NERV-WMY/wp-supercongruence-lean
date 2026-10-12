import WPReview.NativeTruncation

open scoped BigOperators
open Polynomial

namespace WPUniversalRankTwo

/-- The literal parameter numerator, including the empty product. -/
def parameterNumerator (mu : ℚ) (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, ((j : ℚ) * ((j : ℚ) + 1) - mu)

/-- The rank-two coefficient used in the actual finite square comparison. -/
def b (mu : ℚ) (n : ℕ) : ℚ :=
  parameterNumerator mu n / (n.factorial : ℚ) ^ 2

def halfCoefficient (n : ℕ) : ℚ :=
  (∏ j ∈ Finset.range n, ((j : ℚ) + 1 / 2)) / (n.factorial : ℚ)

/-- The third-order parameter coefficient, with the same parameter numerator. -/
def g (mu : ℚ) (n : ℕ) : ℚ := halfCoefficient n * b mu n

theorem b_zero (mu : ℚ) : b mu 0 = 1 := by
  simp [b, parameterNumerator]

theorem g_zero (mu : ℚ) : g mu 0 = 1 := by
  simp [g, halfCoefficient, b_zero]

theorem parameterNumerator_succ (mu : ℚ) (n : ℕ) :
    parameterNumerator mu (n + 1) =
      parameterNumerator mu n * ((n : ℚ) * ((n : ℚ) + 1) - mu) := by
  simp only [parameterNumerator, Finset.prod_range_succ]

theorem b_recurrence (mu : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * b mu (n + 1) =
      ((n : ℚ) * ((n : ℚ) + 1) - mu) * b mu n := by
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hs : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [b, parameterNumerator_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem halfCoefficient_recurrence (n : ℕ) :
    ((n : ℚ) + 1) * halfCoefficient (n + 1) =
      ((n : ℚ) + 1 / 2) * halfCoefficient n := by
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hs : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [halfCoefficient, Finset.prod_range_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem g_recurrence (mu : ℚ) (n : ℕ) :
    ((n : ℚ) + 1) ^ 3 * g mu (n + 1) =
      ((n : ℚ) + 1 / 2) * ((n : ℚ) * ((n : ℚ) + 1) - mu) * g mu n := by
  calc
    ((n : ℚ) + 1) ^ 3 * g mu (n + 1) =
        (((n : ℚ) + 1) * halfCoefficient (n + 1)) *
          (((n : ℚ) + 1) ^ 2 * b mu (n + 1)) := by unfold g; ring
    _ = (((n : ℚ) + 1 / 2) * halfCoefficient n) *
          (((n : ℚ) * ((n : ℚ) + 1) - mu) * b mu n) := by
      rw [halfCoefficient_recurrence, b_recurrence]
    _ = _ := by unfold g; ring

/-- The special parameter is identified with the retained literal factorial coefficients. -/
theorem g_special_eq_nativeCoefficient (n : ℕ) :
    g (-5 / 36) n = WPReview.nativeCoefficient n := by
  induction n with
  | zero => rw [g_zero, WPReview.nativeCoefficient_zero]
  | succ n ih =>
    have hs : (n : ℚ) + 1 ≠ 0 := by positivity
    apply mul_left_cancel₀ (pow_ne_zero 3 hs)
    rw [g_recurrence, WPReview.nativeCoefficient_recurrence, ih]
    ring

noncomputable def Y (mu : ℚ) (N : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range N, monomial n (b mu n)

noncomputable def F (mu : ℚ) (N : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range N, monomial n (g mu n)

theorem Y_coeff (mu : ℚ) (N n : ℕ) :
    (Y mu N).coeff n = if n < N then b mu n else 0 := by
  classical
  simp only [Y, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro j hj hjn
      simp [hjn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≠ n := by have := Finset.mem_range.mp hj; omega
    simp [hjn]

theorem F_coeff (mu : ℚ) (N n : ℕ) :
    (F mu N).coeff n = if n < N then g mu n else 0 := by
  classical
  simp only [F, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro j hj hjn
      simp [hjn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j ≠ n := by have := Finset.mem_range.mp hj; omega
    simp [hjn]

theorem F_special_eq_nativePolynomial (N : ℕ) :
    F (-5 / 36) N = WPReview.nativePolynomial N := by
  unfold F WPReview.nativePolynomial
  simp_rw [g_special_eq_nativeCoefficient]

/-- The Euler form of the actual rank-two equation in z=(1-T)/2. -/
noncomputable def gaussEulerOperator (mu : ℚ) (P : ℚ[X]) : ℚ[X] :=
  WPReview.nativeTheta (WPReview.nativeTheta P) -
    X * (WPReview.nativeTheta (WPReview.nativeTheta P) +
      WPReview.nativeTheta P - C mu * P)

theorem gaussEulerOperator_coeff_zero (mu : ℚ) (P : ℚ[X]) :
    (gaussEulerOperator mu P).coeff 0 = 0 := by
  simp [gaussEulerOperator, WPReview.nativeTheta_coeff]

theorem gaussEulerOperator_coeff_succ (mu : ℚ) (P : ℚ[X]) (n : ℕ) :
    (gaussEulerOperator mu P).coeff (n + 1) =
      ((n : ℚ) + 1) ^ 2 * P.coeff (n + 1) -
        ((n : ℚ) * ((n : ℚ) + 1) - mu) * P.coeff n := by
  simp only [gaussEulerOperator, coeff_sub, coeff_add, coeff_C_mul,
    WPReview.nativeTheta_coeff, coeff_X_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The complete finite rank-two source, including the last coefficient. -/
theorem Y_finite_euler_residual (mu : ℚ) (N : ℕ) (hN : 0 < N) :
    gaussEulerOperator mu (Y mu N) =
      monomial N (-((N : ℚ) ^ 2 * b mu N)) := by
  ext k
  cases k with
  | zero => simp [gaussEulerOperator_coeff_zero, coeff_monomial, Nat.ne_of_gt hN]
  | succ n =>
    rw [gaussEulerOperator_coeff_succ, Y_coeff, Y_coeff, coeff_monomial]
    by_cases hn : n + 1 < N
    · have hn' : n < N := by omega
      have hne : N ≠ n + 1 := by omega
      rw [if_pos hn, if_pos hn', if_neg hne]
      exact sub_eq_zero.mpr (b_recurrence mu n)
    · by_cases heq : n + 1 = N
      · have hn' : n < N := by omega
        rw [if_neg hn, if_pos hn', if_pos heq.symm]
        have hr := b_recurrence mu n
        rw [← heq]
        push_cast
        linear_combination hr
      · have hn' : ¬n < N := by omega
        rw [if_neg hn, if_neg hn', if_neg (Ne.symm heq)]
        ring

/-- The regular rank-two equation before the affine change from z to T. -/
noncomputable def gaussRegularOperator (mu : ℚ) (P : ℚ[X]) : ℚ[X] :=
  (X - X ^ 2) * derivative (derivative P) +
    (1 - 2 * X) * derivative P + C mu * P

theorem gaussEulerOperator_eq_X_mul_regular (mu : ℚ) (P : ℚ[X]) :
    gaussEulerOperator mu P = X * gaussRegularOperator mu P := by
  simp only [gaussEulerOperator, gaussRegularOperator, WPReview.nativeTheta,
    derivative_mul, derivative_X, one_mul]
  ring

/-- The literal regular finite source is at degree N-1, with no omitted last slot. -/
theorem Y_finite_regular_residual (mu : ℚ) (N : ℕ) (hN : 0 < N) :
    gaussRegularOperator mu (Y mu N) =
      monomial (N - 1) (-((N : ℚ) ^ 2 * b mu N)) := by
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from X_ne_zero)
  rw [← gaussEulerOperator_eq_X_mul_regular, Y_finite_euler_residual mu N hN]
  rw [X_mul_monomial, show N - 1 + 1 = N by omega]

/-- The universal third-order parameter equation in the same native variable. -/
noncomputable def thirdParameterOperator (mu : ℚ) (P : ℚ[X]) : ℚ[X] :=
  WPReview.nativeTheta (WPReview.nativeTheta (WPReview.nativeTheta P)) -
    X * WPReview.nativeShift (1 / 2)
      (WPReview.nativeTheta (WPReview.nativeTheta P) +
        WPReview.nativeTheta P - C mu * P)

theorem thirdParameterOperator_coeff_zero (mu : ℚ) (P : ℚ[X]) :
    (thirdParameterOperator mu P).coeff 0 = 0 := by
  simp [thirdParameterOperator, WPReview.nativeTheta_coeff]

theorem thirdParameterOperator_coeff_succ (mu : ℚ) (P : ℚ[X]) (n : ℕ) :
    (thirdParameterOperator mu P).coeff (n + 1) =
      ((n : ℚ) + 1) ^ 3 * P.coeff (n + 1) -
        ((n : ℚ) + 1 / 2) * ((n : ℚ) * ((n : ℚ) + 1) - mu) * P.coeff n := by
  simp only [thirdParameterOperator, WPReview.nativeShift, coeff_sub, coeff_add,
    coeff_C_mul, WPReview.nativeTheta_coeff, coeff_X_mul, Nat.cast_add, Nat.cast_one]
  ring

theorem thirdParameterOperator_special (P : ℚ[X]) :
    thirdParameterOperator (-5 / 36) P = WPReview.nativeOperator P := by
  ext k
  cases k with
  | zero => simp [thirdParameterOperator_coeff_zero, WPReview.nativeOperator,
      WPReview.nativeTheta_coeff]
  | succ n =>
    rw [thirdParameterOperator_coeff_succ, WPReview.nativeOperator_coeff_succ]
    ring

/-- The actual third-order source is retained at every rational parameter. -/
theorem F_finite_residual (mu : ℚ) (N : ℕ) (hN : 0 < N) :
    thirdParameterOperator mu (F mu N) =
      monomial N (-((N : ℚ) ^ 3 * g mu N)) := by
  ext k
  cases k with
  | zero => simp [thirdParameterOperator_coeff_zero, coeff_monomial, Nat.ne_of_gt hN]
  | succ n =>
    rw [thirdParameterOperator_coeff_succ, F_coeff, F_coeff, coeff_monomial]
    by_cases hn : n + 1 < N
    · have hn' : n < N := by omega
      have hne : N ≠ n + 1 := by omega
      rw [if_pos hn, if_pos hn', if_neg hne]
      exact sub_eq_zero.mpr (g_recurrence mu n)
    · by_cases heq : n + 1 = N
      · have hn' : n < N := by omega
        rw [if_neg hn, if_pos hn', if_pos heq.symm]
        have hr := g_recurrence mu n
        rw [← heq]
        push_cast
        linear_combination hr
      · have hn' : ¬n < N := by omega
        rw [if_neg hn, if_neg hn', if_neg (Ne.symm heq)]
        ring

theorem b_terminating (m n : ℕ) (hmn : m < n) :
    b ((m : ℚ) * ((m : ℚ) + 1)) n = 0 := by
  have hnum : parameterNumerator ((m : ℚ) * ((m : ℚ) + 1)) n = 0 := by
    unfold parameterNumerator
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hmn)
    ring
  simp [b, hnum]

theorem g_terminating (m n : ℕ) (hmn : m < n) :
    g ((m : ℚ) * ((m : ℚ) + 1)) n = 0 := by
  simp [g, b_terminating m n hmn]

theorem Y_terminating_euler_equation (m N : ℕ) (hmN : m < N) :
    gaussEulerOperator ((m : ℚ) * ((m : ℚ) + 1))
      (Y ((m : ℚ) * ((m : ℚ) + 1)) N) = 0 := by
  rw [Y_finite_euler_residual _ N (by omega), b_terminating m N hmN]
  simp

theorem Y_terminating_regular_equation (m N : ℕ) (hmN : m < N) :
    gaussRegularOperator ((m : ℚ) * ((m : ℚ) + 1))
      (Y ((m : ℚ) * ((m : ℚ) + 1)) N) = 0 := by
  rw [Y_finite_regular_residual _ N (by omega), b_terminating m N hmN]
  simp

theorem F_terminating_equation (m N : ℕ) (hmN : m < N) :
    thirdParameterOperator ((m : ℚ) * ((m : ℚ) + 1))
      (F ((m : ℚ) * ((m : ℚ) + 1)) N) = 0 := by
  rw [F_finite_residual _ N (by omega), g_terminating m N hmN]
  simp

/-- The literal affine parameter z=(1-T)/2 as a rational polynomial. -/
noncomputable def zOfT : ℚ[X] := C (1 / 2) - C (1 / 2) * X

noncomputable def YT (mu : ℚ) (N : ℕ) : ℚ[X] := (Y mu N).comp zOfT

noncomputable def legendreOperator (mu : ℚ) (P : ℚ[X]) : ℚ[X] :=
  (1 - X ^ 2) * derivative (derivative P) - 2 * X * derivative P + C mu * P

theorem regular_operator_affine_transport (mu : ℚ) (P : ℚ[X]) :
    legendreOperator mu (P.comp zOfT) =
      (gaussRegularOperator mu P).comp zOfT := by
  have hhalf : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := by
    change C (2 : ℚ) * C (1 / 2 : ℚ) = C (1 : ℚ)
    rw [← C_mul]
    norm_num
  have hscaled := congrArg (fun H : ℚ[X] =>
    (C (1 / 2) * (1 - X) * (derivative (derivative P)).comp zOfT +
      (derivative P).comp zOfT) * H) hhalf
  simp only [zOfT, one_div] at hscaled
  simp [legendreOperator, gaussRegularOperator, zOfT, derivative_comp, pow_two]
  linear_combination hscaled

/-- MC4's exact finite source in T, before any p-adic reduction. -/
theorem YT_finite_residual (mu : ℚ) (N : ℕ) (hN : 0 < N) :
    legendreOperator mu (YT mu N) =
      C (-((N : ℚ) ^ 2 * b mu N)) * zOfT ^ (N - 1) := by
  rw [YT, regular_operator_affine_transport, Y_finite_regular_residual mu N hN]
  simp [monomial_comp]

/-- A general self-adjoint rank-two operator on finite rational polynomials. -/
noncomputable def selfAdjointRankTwo (A C0 y : ℚ[X]) : ℚ[X] :=
  derivative (A * derivative y) + C0 * y

/-- The corresponding symmetric-square operator, with all forcing terms retained. -/
noncomputable def symmetricSquareOperator (A C0 Q : ℚ[X]) : ℚ[X] :=
  derivative (A * derivative (A * derivative Q)) +
    4 * A * C0 * derivative Q + 2 * derivative (A * C0) * Q

/-- The full polynomial source identity underlying MC6; no coefficient is inverted. -/
theorem symmetric_square_source (A C0 y : ℚ[X]) :
    symmetricSquareOperator A C0 (y ^ 2) =
      2 * A * y * derivative (selfAdjointRankTwo A C0 y) +
        6 * A * derivative y * selfAdjointRankTwo A C0 y +
        2 * derivative A * y * selfAdjointRankTwo A C0 y := by
  simp [symmetricSquareOperator, selfAdjointRankTwo, pow_two, derivative_mul]
  ring

theorem symmetric_square_homogeneous (A C0 y : ℚ[X])
    (hy : selfAdjointRankTwo A C0 y = 0) :
    symmetricSquareOperator A C0 (y ^ 2) = 0 := by
  rw [symmetric_square_source, hy]
  simp

end WPUniversalRankTwo
