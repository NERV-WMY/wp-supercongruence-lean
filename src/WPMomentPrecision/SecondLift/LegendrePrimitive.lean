import WPActualRankTwoFiniteLegendre

open scoped BigOperators Polynomial
open Polynomial WPActualCMGauss WPActualGaussProper WPActualRankTwoGaussODE
  WPActualRankTwoLegendreField WPActualRankTwoProper WPActualRankTwoFiniteLegendre
  WPActualGaussBottom

namespace WPMomentPrecision.LegendrePrimitive

set_option maxHeartbeats 1600000

/-- The retained integer Legendre family in the same original Jacobi coordinate. -/
noncomputable def integerJacobiField (p n : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  ((shiftedLegendre n).map (Int.castRingHom (ZMod p))).comp
    (C (1 / 2 : ZMod p) * (1 - X))

theorem integerJacobiField_actual (p : ℕ) [Fact p.Prime] :
    integerJacobiField p (p / 6) = actualLegendreJacobi p := rfl

theorem integerJacobiField_degree (p n : ℕ) [Fact p.Prime] :
    (integerJacobiField p n).natDegree ≤ n := by
  have hq : (C (1 / 2 : ZMod p) * (1 - X)).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])) hq).trans (by omega))

theorem integerJacobiField_endpoint_one (p n : ℕ) [Fact p.Prime] :
    (integerJacobiField p n).eval 1 = 1 := by
  simp only [integerJacobiField, eval_comp, eval_mul, eval_C, eval_sub,
    eval_one, eval_X, sub_self, mul_zero, ← coeff_zero_eq_eval_zero, coeff_map,
    coeff_shiftedLegendre, pow_zero, Nat.choose_zero_right, Nat.add_zero,
    Nat.choose_self]
  norm_num

theorem integerJacobiField_zero (p : ℕ) [Fact p.Prime] : integerJacobiField p 0 = 1 := by
  simp [integerJacobiField, shiftedLegendre]

theorem integerJacobiField_source (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi n (integerJacobiField p n) = 0 := by
  rw [integerJacobiField, ← legendre_coordinate n (1 / 2 : ZMod p)
    (field_half_identity p hp), ← legendreRegular_map,
    actual_integer_legendre_ODE, Polynomial.map_zero, zero_comp]

theorem legendreJacobi_C_mul {K : Type*} [CommRing K] (n : ℕ) (a : K) (P : K[X]) :
    legendreJacobi n (C a * P) = C a * legendreJacobi n P := by
  simp only [legendreJacobi, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem legendreJacobi_sub {K : Type*} [CommRing K] (n : ℕ) (P Q : K[X]) :
    legendreJacobi n (P - Q) = legendreJacobi n P - legendreJacobi n Q := by
  simp only [legendreJacobi, derivative_sub]
  ring

/-- Lowering the integer degree is proved from the same whole Legendre operator. -/
theorem degree_lowering_source {K : Type*} [CommRing K] (n : ℕ) (Y : K[X]) :
    legendreJacobi n (C ((n : K) + 1) * X * Y + (1 - X ^ 2) * Y.derivative) =
      (1 - X ^ 2) * (legendreJacobi (n + 1) Y).derivative +
        C ((n : K) - 1) * X * legendreJacobi (n + 1) Y := by
  simp only [legendreJacobi, derivative_mul, derivative_C,
    derivative_X, derivative_neg, derivative_one, derivative_ofNat,
    derivative_X_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_one, map_ofNat, zero_mul, zero_add, zero_sub,
    mul_zero, add_zero]
  simp only [C_eq_natCast]
  ring

theorem adjacent_degree_lowering (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hn : n + 1 ≤ p / 6) :
    C ((n : ZMod p) + 1) * integerJacobiField p n =
      C ((n : ZMod p) + 1) * X * integerJacobiField p (n + 1) +
        (1 - X ^ 2) * (integerJacobiField p (n + 1)).derivative := by
  let Y := integerJacobiField p (n + 1)
  let W := C ((n : ZMod p) + 1) * X * Y + (1 - X ^ 2) * Y.derivative
  let Z := C (((n : ZMod p) + 1)⁻¹) * W
  have hd := Nat.div_mul_le_self p 6
  have hu : (n : ZMod p) + 1 ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      small_cast_ne_zero p (n + 1) (by omega) (by omega)
  have hunit : C (((n : ZMod p) + 1)⁻¹) * C ((n : ZMod p) + 1) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hu, C_1]
  have hWsource : legendreJacobi n W = 0 := by
    dsimp only [W, Y]
    rw [degree_lowering_source, integerJacobiField_source p (n + 1) (by omega)]
    simp
  have hZsource : legendreJacobi n Z = 0 := by
    dsimp only [Z]
    rw [legendreJacobi_C_mul, hWsource, mul_zero]
  have hZdegree : Z.natDegree ≤ n + 2 := by
    have hY := integerJacobiField_degree p (n + 1)
    have hYD := (natDegree_derivative_le _).trans (Nat.sub_le_sub_right hY 1)
    have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 :=
      natDegree_sub_le_of_le
        (show (1 : (ZMod p)[X]).natDegree ≤ 0 by simp) (natDegree_X_pow_le 2)
    exact (natDegree_mul_le_of_le
      (show (C (((n : ZMod p) + 1)⁻¹)).natDegree ≤ 0 from
        (natDegree_C _).le)
      (natDegree_add_le_of_le
        (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le
            (show (C ((n : ZMod p) + 1)).natDegree ≤ 0 from (natDegree_C _).le)
            (show (X : (ZMod p)[X]).natDegree ≤ 1 by simp)) hY)
        (natDegree_mul_le_of_le hq hYD))).trans (by omega)
  have hZ1 : Z.eval 1 = 1 := by
    simp only [Z, W, Y, eval_mul, eval_C, eval_add, eval_X, eval_sub,
      eval_one, eval_pow, one_pow, sub_self, zero_mul, add_zero, mul_one,
      integerJacobiField_endpoint_one, inv_mul_cancel₀ hu]
  have hdiff : Z - integerJacobiField p n = 0 := by
    apply legendre_jacobi_kernel_zero p n (by omega)
    · exact (natDegree_sub_le_of_le hZdegree (integerJacobiField_degree p n)).trans_lt
        (by omega)
    · rw [eval_sub, hZ1, integerJacobiField_endpoint_one, sub_self]
    · rw [legendreJacobi_sub, hZsource, integerJacobiField_source p n (by omega), sub_self]
  have hZ : Z = integerJacobiField p n := sub_eq_zero.mp hdiff
  rw [← hZ]
  change C ((n : ZMod p) + 1) * (C (((n : ZMod p) + 1)⁻¹) * W) = W
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hu, C_1, one_mul]

/-- This adjacent-square identity is the finite source of the endpoint harmonic. -/
theorem adjacent_square_derivative (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hn : n + 1 ≤ p / 6) :
    (1 - X ^ 2) * (integerJacobiField p (n + 1) * integerJacobiField p n).derivative =
      C ((n : ZMod p) + 1) *
        (integerJacobiField p n ^ 2 - integerJacobiField p (n + 1) ^ 2) := by
  let Y := integerJacobiField p (n + 1)
  let Z := integerJacobiField p n
  have hl := adjacent_degree_lowering p n hp hn
  have hd := congrArg Polynomial.derivative hl
  have hY := integerJacobiField_source p (n + 1) (by omega)
  have hu : (n : ZMod p) + 1 ≠ 0 := by
    have hdiv := Nat.div_mul_le_self p 6
    simpa only [Nat.cast_add, Nat.cast_one] using
      small_cast_ne_zero p (n + 1) (by omega) (by omega)
  have hD : Z.derivative = X * Y.derivative - C ((n : ZMod p) + 1) * Y := by
    have hz : C ((n : ZMod p) + 1) *
        (Z.derivative - X * Y.derivative + C ((n : ZMod p) + 1) * Y) = 0 := by
      simp only [derivative_mul, derivative_add, derivative_C, derivative_X,
        derivative_sub, derivative_one, derivative_X_pow, Nat.cast_ofNat,
        map_ofNat, zero_mul, zero_add, zero_sub] at hd
      simp only [legendreJacobi, Nat.cast_add, Nat.cast_one] at hY
      simp only [map_mul, map_add, map_one] at hd hY ⊢
      linear_combination hd + hY
    have hh := (mul_eq_zero.mp hz).resolve_left (Polynomial.C_ne_zero.mpr hu)
    linear_combination hh
  have hlow : (1 - X ^ 2) * Y.derivative = C ((n : ZMod p) + 1) * (Z - X * Y) := by
    linear_combination -hl
  change (1 - X ^ 2) * (Y * Z).derivative = _
  rw [derivative_mul, hD]
  linear_combination (Z + X * Y) * hlow

/-- The odd polynomial primitive of the actual finite logarithmic source. -/
noncomputable def legendreLogPrimitive (p d : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  -∑ n ∈ Finset.range d, C (((n : ZMod p) + 1)⁻¹) *
    integerJacobiField p (n + 1) * integerJacobiField p n

theorem legendreLogPrimitive_zero (p : ℕ) [Fact p.Prime] : legendreLogPrimitive p 0 = 0 := by
  simp [legendreLogPrimitive]

theorem legendreLogPrimitive_succ (p d : ℕ) [Fact p.Prime] :
    legendreLogPrimitive p (d + 1) = legendreLogPrimitive p d -
      C (((d : ZMod p) + 1)⁻¹) * integerJacobiField p (d + 1) * integerJacobiField p d := by
  simp only [legendreLogPrimitive, Finset.sum_range_succ]
  ring

theorem legendreLogPrimitive_source (p d : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hd : d ≤ p / 6) :
    (1 - X ^ 2) * (legendreLogPrimitive p d).derivative = integerJacobiField p d ^ 2 - 1 := by
  induction d with
  | zero => simp [legendreLogPrimitive_zero, integerJacobiField_zero]
  | succ d ih =>
    have hu : (d : ZMod p) + 1 ≠ 0 := by
      have hdiv := Nat.div_mul_le_self p 6
      simpa only [Nat.cast_add, Nat.cast_one] using
        small_cast_ne_zero p (d + 1) (by omega) (by omega)
    have hunit : C (((d : ZMod p) + 1)⁻¹) * C ((d : ZMod p) + 1) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hu, C_1]
    rw [legendreLogPrimitive_succ]
    have hcalc : (1 - X ^ 2) *
        (legendreLogPrimitive p d - C (((d : ZMod p) + 1)⁻¹) *
          integerJacobiField p (d + 1) * integerJacobiField p d).derivative =
        (1 - X ^ 2) * (legendreLogPrimitive p d).derivative -
          C (((d : ZMod p) + 1)⁻¹) * ((1 - X ^ 2) *
            (integerJacobiField p (d + 1) * integerJacobiField p d).derivative) := by
      simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
      ring
    rw [hcalc, ih (by omega), adjacent_square_derivative p d hp hd,
      ← mul_assoc, hunit, one_mul]
    ring

theorem legendreLogPrimitive_endpoint_one (p d : ℕ) [Fact p.Prime] :
    (legendreLogPrimitive p d).eval 1 = -fieldHarmonic p d := by
  induction d with
  | zero => simp [legendreLogPrimitive_zero, fieldHarmonic_zero]
  | succ d ih =>
    rw [legendreLogPrimitive_succ, eval_sub, eval_mul, eval_mul, eval_C,
      integerJacobiField_endpoint_one, integerJacobiField_endpoint_one,
      mul_one, mul_one, ih, fieldHarmonic_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem legendreLogPrimitive_degree (p d : ℕ) [Fact p.Prime] (hd : 0 < d) :
    (legendreLogPrimitive p d).natDegree ≤ 2 * d - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [legendreLogPrimitive, coeff_neg, finsetSum_coeff, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := Finset.mem_range.mp hn
  apply coeff_eq_zero_of_natDegree_lt
  exact (natDegree_mul_le_of_le
    (natDegree_mul_le_of_le
      (show (C (((n : ZMod p) + 1)⁻¹)).natDegree ≤ 0 from (natDegree_C _).le)
      (integerJacobiField_degree p (n + 1))) (integerJacobiField_degree p n)).trans_lt
      (by omega)

/-- Actual B_d has both its original source and the endpoint needed to remove T^p. -/
theorem actual_legendreLogPrimitive (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (legendreLogPrimitive p (p / 6)).derivative = actualLegendreJacobi p ^ 2 - 1 ∧
      (legendreLogPrimitive p (p / 6)).eval 1 = (properLegendreJacobi p).eval 1 ∧
      (legendreLogPrimitive p (p / 6)).natDegree ≤ 2 * (p / 6) - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← integerJacobiField_actual]
    exact legendreLogPrimitive_source p (p / 6) hp le_rfl
  · rw [legendreLogPrimitive_endpoint_one, properLegendreJacobi_endpoint_one]
  · exact legendreLogPrimitive_degree p (p / 6) (by omega)

end WPMomentPrecision.LegendrePrimitive
