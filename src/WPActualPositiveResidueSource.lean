import WPActualEtaFieldCutoff

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource
  WPActualLogarithmicEta WPActualEtaPole WPActualEtaSupport WPActualEtaPrimitive
  WPActualEtaIntegrality WPActualEtaFieldCutoff WPActualNativeHasse

namespace WPActualPositiveResidueSource

/-- The actual two endpoint quotients, with their original multiplicities. -/
noncomputable def weightedDifference : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] :=
  (2 : ℚ) • dividedDifference (1 / 4) + dividedDifference 4

theorem weightedDifference_apply (P : ℚ[T;T⁻¹]) :
    weightedDifference P = C 2 * dividedDifference (1 / 4) P + dividedDifference 4 P := by
  simp only [weightedDifference, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_C_mul]

theorem weightedDifference_C_mul (c : ℚ) (P : ℚ[T;T⁻¹]) :
    weightedDifference (C c * P) = C c * weightedDifference P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]

theorem weightedDifference_one : weightedDifference 1 = 0 := by
  have h (a : ℚ) : dividedDifference a (1 : ℚ[T;T⁻¹]) = 0 := by
    simpa [monomialQuotient, forwardQuotient] using dividedDifference_monomial a 1 0
  simp only [weightedDifference_apply, h, mul_zero, add_zero]

theorem actual_Vx_logarithmic_factor :
    (T 1 - C (1 / 4)) * (T 1 - C 4) * derivative Vx =
      (C 2 * (T 1 - C 4) + (T 1 - C (1 / 4))) * Vx := by
  apply ratify_injective
  simp only [map_mul, map_add, ratify_linear, ratify_C]
  have hV : ratify Vx ≠ 0 := by
    have hVx : Vx ≠ 0 := by
      intro hz
      have h := congrArg (evaluate 3 (by norm_num)) hz
      rw [evaluate_Vx, map_zero] at h
      norm_num at h
    simpa using ratify_injective.ne hVx
  have h := actual_dlogVx
  rw [dlog] at h
  have ha := linearPole_ne_zero (1 / 4)
  have hb := linearPole_ne_zero 4
  norm_num
  field_simp [hV, ha, hb] at h
  linear_combination h

theorem weightedDifference_Vx_power (n : ℕ) :
    weightedDifference (Vx ^ (n + 1)) = Vx ^ n * derivative Vx := by
  have ha : evaluate (1 / 4) (by norm_num) (Vx ^ (n + 1)) = 0 := by
    rw [map_pow, evaluate_Vx]; norm_num
  have hb : evaluate 4 (by norm_num) (Vx ^ (n + 1)) = 0 := by
    rw [map_pow, evaluate_Vx]; norm_num
  have hda := dividedDifference_identity (1 / 4) (by norm_num) (Vx ^ (n + 1))
  have hdb := dividedDifference_identity 4 (by norm_num) (Vx ^ (n + 1))
  rw [ha, map_zero, sub_zero] at hda
  rw [hb, map_zero, sub_zero] at hdb
  have hne (a : ℚ) : (T 1 - C a : ℚ[T;T⁻¹]) ≠ 0 := by
    intro hz
    have hj := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff 1) hz
    norm_num [AddMonoidAlgebra.coeff_sub] at hj
  apply mul_left_cancel₀ (mul_ne_zero (hne (1 / 4)) (hne 4))
  rw [weightedDifference_apply]
  calc
    _ = C 2 * (T 1 - C 4) * ((T 1 - C (1 / 4)) *
          dividedDifference (1 / 4) (Vx ^ (n + 1))) +
        (T 1 - C (1 / 4)) * ((T 1 - C 4) *
          dividedDifference 4 (Vx ^ (n + 1))) := by ring
    _ = (C 2 * (T 1 - C 4) + (T 1 - C (1 / 4))) * Vx ^ (n + 1) := by
      rw [hda, hdb]; ring
    _ = Vx ^ n * ((T 1 - C (1 / 4)) * (T 1 - C 4) * derivative Vx) := by
      rw [actual_Vx_logarithmic_factor, pow_succ]; ring
    _ = _ := by ring

/-- The complete second coefficient primitive, including every native index. -/
noncomputable def GX (e : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.range (e + 1), C (WPReview.nativeCoefficient n / (n : ℚ) ^ 2) * Vx ^ n

theorem actual_native_positive_derivative (e : ℕ) :
    weightedDifference (Fpull e Vx) = derivative (HX e) := by
  rw [Fpull_expansion, HX, Hpull_expansion, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [weightedDifference_C_mul, derivative_mul, derivative_C, zero_mul, zero_add]
  cases n with
  | zero => simp [weightedDifference_one]
  | succ n =>
    rw [weightedDifference_Vx_power, derivative_pow_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    simp only [← mul_assoc, ← map_mul]
    congr 2
    field_simp

theorem actual_H_positive_derivative (e : ℕ) :
    weightedDifference (HX e) = derivative (GX e) := by
  rw [HX, Hpull_expansion, GX, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [weightedDifference_C_mul, derivative_mul, derivative_C, zero_mul, zero_add]
  cases n with
  | zero => simp [weightedDifference_one]
  | succ n =>
    rw [weightedDifference_Vx_power, derivative_pow_succ]
    have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    simp only [← mul_assoc, ← map_mul]
    congr 2
    field_simp

/-- Exact original source decomposition before extracting any resonant coefficient. -/
theorem actual_Peta_positive_decomposition (p N e : ℕ) :
    Peta p N e = C (1 / (p : ℚ)) * derivative (HX e) + derivative (GX e) -
      C (1 / 2) * HX e * T (-1) -
      C (1 / (p : ℚ)) * weightedDifference (T (N : ℤ) * Fpull e Qx) := by
  rw [Peta, ← weightedDifference_apply, AX, chiX, map_add,
    weightedDifference_C_mul, map_sub,
    actual_native_positive_derivative, actual_H_positive_derivative]
  ring

end WPActualPositiveResidueSource
