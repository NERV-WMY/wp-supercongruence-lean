import WPReview.NativeTruncation

open Polynomial

namespace WPForcedSourceStokes

/-- The actual full native square state uses every native index below p. -/
noncomputable def squaredNativePolynomial (p : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range p, monomial n (WPReview.nativeCoefficient n ^ 2)

noncomputable def thetaPower (k : ℕ) (P : ℚ[X]) : ℚ[X] :=
  (WPReview.nativeTheta^[k]) P

noncomputable def squareNativeShift (P : ℚ[X]) : ℚ[X] :=
  WPReview.nativeShift (1/2) (WPReview.nativeShift (1/2)
    (WPReview.nativeShift (1/6) (WPReview.nativeShift (1/6)
      (WPReview.nativeShift (5/6) (WPReview.nativeShift (5/6) P)))))

noncomputable def squareNativeOperator (P : ℚ[X]) : ℚ[X] :=
  thetaPower 6 P - X * squareNativeShift P

theorem squaredNativePolynomial_coeff (p n : ℕ) :
    (squaredNativePolynomial p).coeff n =
      if n < p then WPReview.nativeCoefficient n ^ 2 else 0 := by
  classical
  simp only [squaredNativePolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by
      have hb' := Finset.mem_range.mp hb
      omega
    simp [hbn]

theorem thetaPower_coeff (k : ℕ) (P : ℚ[X]) (n : ℕ) :
    (thetaPower k P).coeff n = (n : ℚ)^k * P.coeff n := by
  induction k with
  | zero => simp [thetaPower]
  | succ k ih =>
      rw [thetaPower, Function.iterate_succ_apply', WPReview.nativeTheta_coeff]
      change (n : ℚ) * (thetaPower k P).coeff n = _
      rw [ih, pow_succ]
      ring

private theorem shift_coeff (a : ℚ) (P : ℚ[X]) (n : ℕ) :
    (WPReview.nativeShift a P).coeff n = ((n : ℚ)+a)*P.coeff n := by
  simp only [WPReview.nativeShift, coeff_add, WPReview.nativeTheta_coeff, coeff_C_mul]
  ring

private theorem squareNativeShift_coeff (P : ℚ[X]) (n : ℕ) :
    (squareNativeShift P).coeff n =
      ((n : ℚ)+1/2)^2*((n : ℚ)+1/6)^2*((n : ℚ)+5/6)^2*P.coeff n := by
  simp only [squareNativeShift, shift_coeff]
  ring

private theorem squareNativeOperator_coeff_succ (P : ℚ[X]) (n : ℕ) :
    (squareNativeOperator P).coeff (n+1) =
      ((n : ℚ)+1)^6*P.coeff (n+1) -
        ((n : ℚ)+1/2)^2*((n : ℚ)+1/6)^2*((n : ℚ)+5/6)^2*P.coeff n := by
  simp only [squareNativeOperator, coeff_sub, thetaPower_coeff, coeff_X_mul,
    squareNativeShift_coeff, Nat.cast_add, Nat.cast_one]

private theorem squareNative_recurrence (n : ℕ) :
    ((n : ℚ)+1)^6*WPReview.nativeCoefficient (n+1)^2 =
      ((n : ℚ)+1/2)^2*((n : ℚ)+1/6)^2*((n : ℚ)+5/6)^2*
        WPReview.nativeCoefficient n^2 := by
  have h := congrArg (fun q : ℚ => q^2) (WPReview.nativeCoefficient_recurrence n)
  simpa only [mul_pow, ← pow_mul] using h

/-- The six-order residual is retained as the square of the literal endpoint. -/
theorem square_native_truncation_residual (p : ℕ) (hp : 0 < p) :
    squareNativeOperator (squaredNativePolynomial p) =
      monomial p (-(WPReview.nativeEndpoint p)^2) := by
  ext k
  cases k with
  | zero =>
      simp [squareNativeOperator, thetaPower_coeff, coeff_monomial, Nat.ne_of_gt hp]
  | succ n =>
      rw [squareNativeOperator_coeff_succ, squaredNativePolynomial_coeff,
        squaredNativePolynomial_coeff, coeff_monomial]
      by_cases hn : n+1 < p
      · have hn' : n < p := by omega
        have hpne : p ≠ n+1 := by omega
        rw [if_pos hn, if_pos hn', if_neg hpne]
        exact sub_eq_zero.mpr (squareNative_recurrence n)
      · by_cases heq : n+1=p
        · have hn' : n < p := by omega
          have hpred : p-1=n := by omega
          rw [if_neg hn, if_pos hn', if_pos heq.symm]
          simp only [WPReview.nativeEndpoint, hpred]
          rw [← heq]
          push_cast
          ring
        · have hn' : ¬n < p := by omega
          rw [if_neg hn, if_neg hn', if_neg (Ne.symm heq)]
          ring

noncomputable def thirdNativeShift (P : ℚ[X]) : ℚ[X] :=
  thetaPower 3 P + C (3/2)*thetaPower 2 P +
    C (23/36)*thetaPower 1 P + C (5/72)*P

/-- Six coordinates obtained from the literal squared native polynomial. -/
noncomputable def actualSixState (p : ℕ) : Fin 6 → ℚ[X] :=
  let H := squaredNativePolynomial p
  let b := thirdNativeShift H
  ![-thetaPower 3 H, -thetaPower 4 H, -thetaPower 5 H,
    b, WPReview.nativeTheta b, thetaPower 2 b]

def nativeBoundaryWeight (n : ℕ) : ℚ := 5/72 + 23*(n : ℚ)/36 + 3*(n : ℚ)^2/2

theorem native_boundary_telescope (n : ℕ) :
    nativeBoundaryWeight n * WPReview.nativeCoefficient n =
      ((n : ℚ)+1)^3 * WPReview.nativeCoefficient (n+1) -
        (n : ℚ)^3 * WPReview.nativeCoefficient n := by
  have h := WPReview.nativeCoefficient_recurrence n
  unfold nativeBoundaryWeight
  linear_combination -h

theorem native_boundary_prefix (n : ℕ) :
    (∑ a ∈ Finset.range n, nativeBoundaryWeight a * WPReview.nativeCoefficient a) =
      (n : ℚ)^3 * WPReview.nativeCoefficient n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h := native_boundary_telescope n
      push_cast
      linear_combination h

theorem native_boundary_tail (p a : ℕ) (ha : a < p) :
    (∑ b ∈ Finset.Ico (a+1) p, nativeBoundaryWeight b * WPReview.nativeCoefficient b) =
      (p : ℚ)^3 * WPReview.nativeCoefficient p -
        ((a : ℚ)+1)^3 * WPReview.nativeCoefficient (a+1) := by
  have h := Finset.sum_range_add_sum_Ico
    (fun b => nativeBoundaryWeight b * WPReview.nativeCoefficient b) (by omega : a+1 ≤ p)
  rw [native_boundary_prefix, native_boundary_prefix] at h
  push_cast at h
  linear_combination h

/-- The literal first finite residue triangle, before endpoint telescoping. -/
noncomputable def angularFirst (p j : ℕ) : ℚ[X] :=
  -(∑ b ∈ Finset.range p, monomial b ((b : ℚ)^j * WPReview.nativeCoefficient b *
    ∑ a ∈ Finset.range b, nativeBoundaryWeight a * WPReview.nativeCoefficient a))

/-- The literal second finite residue triangle retains b=p-1. -/
noncomputable def angularSecond (p j : ℕ) : ℚ[X] :=
  -(∑ a ∈ Finset.range p, monomial a ((a : ℚ)^j * WPReview.nativeCoefficient a *
    ∑ b ∈ Finset.Ico (a+1) p, nativeBoundaryWeight b * WPReview.nativeCoefficient b))

private theorem sum_monomial_coeff (p n : ℕ) (a : ℕ → ℚ) :
    (∑ b ∈ Finset.range p, monomial b (a b) : ℚ[X]).coeff n =
      if n < p then a n else 0 := by
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by have := Finset.mem_range.mp hb; omega
    simp [hbn]

theorem actual_angular_first (p j : ℕ) :
    angularFirst p j = -thetaPower (j+3) (squaredNativePolynomial p) := by
  ext n
  simp only [angularFirst, coeff_neg, sum_monomial_coeff, thetaPower_coeff,
    squaredNativePolynomial_coeff]
  by_cases hn : n < p
  · rw [if_pos hn, if_pos hn, native_boundary_prefix]
    rw [pow_add]
    ring
  · simp [hn]

private theorem thirdNativeShift_coeff (P : ℚ[X]) (n : ℕ) :
    (thirdNativeShift P).coeff n =
      ((n : ℚ)^3 + 3*(n : ℚ)^2/2 + 23*(n : ℚ)/36 + 5/72) * P.coeff n := by
  simp only [thirdNativeShift, coeff_add, coeff_C_mul, thetaPower_coeff]
  ring

theorem actual_angular_second (p j : ℕ) (hp : 0 < p) :
    angularSecond p j = thetaPower j (thirdNativeShift (squaredNativePolynomial p)) -
      C (WPReview.nativeEndpoint p) * thetaPower j (WPReview.nativePolynomial p) := by
  ext n
  simp only [angularSecond, coeff_neg, sum_monomial_coeff, coeff_sub,
    thetaPower_coeff, thirdNativeShift_coeff, squaredNativePolynomial_coeff,
    coeff_C_mul, WPReview.nativePolynomial_coeff]
  by_cases hn : n < p
  · rw [if_pos hn, if_pos hn, if_pos hn, native_boundary_tail p n hn,
      WPReview.nativeEndpoint_eq p hp, WPReview.nativeCoefficient_recurrence n]
    ring
  · simp [hn]

noncomputable def angularSixState (p : ℕ) : Fin 6 → ℚ[X] :=
  ![angularFirst p 0, angularFirst p 1, angularFirst p 2,
    angularSecond p 0, angularSecond p 1, angularSecond p 2]

noncomputable def nativeEndpointState (p : ℕ) : Fin 6 → ℚ[X] :=
  ![0, 0, 0, WPReview.nativePolynomial p,
    WPReview.nativeTheta (WPReview.nativePolynomial p),
    thetaPower 2 (WPReview.nativePolynomial p)]

/-- The angular residues attach to the actual full native state with its endpoint correction. -/
theorem actual_angular_six_state (p : ℕ) (hp : 0 < p) (i : Fin 6) :
    angularSixState p i = actualSixState p i -
      C (WPReview.nativeEndpoint p) * nativeEndpointState p i := by
  fin_cases i <;> simp [angularSixState, actualSixState, nativeEndpointState,
    actual_angular_first, actual_angular_second p _ hp, thetaPower]

noncomputable def nativeConnectionNumerator (Y : Fin 6 → ℚ[X]) : Fin 6 → ℚ[X] :=
  ![(X-1)*Y 1, (X-1)*Y 2,
    X*(C (-5/72)*Y 0 + C (-23/36)*Y 1 + C (-3/2)*Y 2 +
      C (5/72)*Y 3 + C (23/36)*Y 4 + C (3/2)*Y 5),
    (X-1)*Y 4, (X-1)*Y 5,
    C (5/72)*Y 0 + C (23/36)*Y 1 + C (3/2)*Y 2 -
      X*(C (5/72)*Y 3 + C (23/36)*Y 4 + C (3/2)*Y 5)]

def nativeForcingVector : Fin 6 → ℚ := ![0, 0, -1, 0, 0, 1]

/-- The exact polynomial form of the actual six-state connection, with its square residual. -/
theorem native_six_state_connection (p : ℕ) (hp : 0 < p) (i : Fin 6) :
    (X-1) * WPReview.nativeTheta (actualSixState p i) =
      nativeConnectionNumerator (actualSixState p) i +
        monomial p (WPReview.nativeEndpoint p ^ 2 * nativeForcingVector i) := by
  fin_cases i
  all_goals
    ext k
    cases k with
    | zero =>
        simp [nativeConnectionNumerator, actualSixState, thirdNativeShift,
          nativeForcingVector, thetaPower_coeff, WPReview.nativeTheta_coeff,
          coeff_monomial, Nat.ne_of_gt hp]
    | succ n =>
        have h := congrArg (fun P : ℚ[X] => P.coeff (n+1))
          (square_native_truncation_residual p hp)
        rw [squareNativeOperator_coeff_succ, coeff_monomial] at h
        simp [nativeConnectionNumerator, actualSixState, nativeForcingVector,
          sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul,
          WPReview.nativeTheta_coeff, thetaPower_coeff, thirdNativeShift_coeff,
          Nat.cast_add, Nat.cast_one, coeff_monomial] <;>
          (by_cases hpn : p = n+1 <;> simp [hpn] at h ⊢ <;>
            first | (solve | ring) | (solve | linear_combination h) |
              (solve | linear_combination -h))

end WPForcedSourceStokes
