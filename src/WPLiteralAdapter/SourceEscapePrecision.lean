import WPLiteralAdapter.EscapeConductorPrecision

open scoped BigOperators
open Polynomial

namespace WPLiteralAdapter

open WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000

/-- Every Laurent coefficient of the actual high angular error has precision six. -/
theorem actual_angular_high_error_escape_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualEscapeRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualAngularHighError p) k) := by
  classical
  let R := WPFiniteConductorPolynomial.integralSubring p
  let I := integralRationalEscape R
  have hlam : lambda ∈ I := actual_lambda_escape_integral p hp
  have hlaminv : lambda⁻¹ ∈ I := actual_lambda_inverse_escape_integral p hp
  have hη (i : Fin 3) (a : ℕ) : (etaClearedPolynomial i 2).coeff a ∈ I :=
    (mem_polynomialCoefficientSubring I _).mp (eta_cleared_polynomial_escape_integral p hp i 2) a
  have hg (i : Fin 3) (a n : ℕ) :
      (etaClearedPolynomial i 2).coeff (a-n)*lambda^a/lambda^3 ∈ I := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact I.mul_mem (I.mul_mem (hη i (a-n)) (I.pow_mem hlam a)) (I.pow_mem hlaminv 3)
  unfold actualAngularHighError
  rw [Finset.mul_sum, actual_escape_coefficient_sum]
  apply precisionZero_sum
  intro a _ha
  by_cases ha : p+3≤a
  · rw [if_pos ha, actual_angular_high_term_expansion p a (by omega) ha]
    rw [actual_escape_coefficient_sum]
    apply precisionZero_sum
    intro i _hi
    rw [actual_escape_coefficient_sum]
    apply precisionZero_sum
    intro n hn
    by_cases hh : p-3≤n
    · rw [if_pos hh, actual_escape_coefficient_scalar]
      exact precisionZero_mul_integral p 6 _ _
        (actual_endpoint_weighted_top_three_precision p n i.val hp (Finset.mem_range.mp hn) hh)
        ((integral_rational_escape_iff R _).mp (hg i a n) k)
    · rw [if_neg hh]
      exact Or.inl (by simp [actualEscapeRationalCoefficient, actualEscapeRationalSeries, actualRationalSeries])
  · rw [if_neg ha, mul_zero]
    exact Or.inl (by simp [actualEscapeRationalCoefficient, actualEscapeRationalSeries, actualRationalSeries])

theorem actual_first_angular_kernel_escape_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) (j : Fin 3) :
    actualFirstAngularKernel p n j ∈
      integralRationalEscape (WPFiniteConductorPolynomial.integralSubring p) := by
  let I := integralRationalEscape (WPFiniteConductorPolynomial.integralSubring p)
  rw [actual_first_angular_kernel_finite]
  apply I.sum_mem
  intro k _hk
  by_cases ht : p-1+k<n+3
  · rw [if_pos ht, mul_one]
    exact I.mul_mem
      ((mem_polynomialCoefficientSubring I _).mp (eta_cleared_polynomial_escape_integral p hp 2 j) k)
      (I.pow_mem (actual_lambda_escape_integral p hp) n)
  · rw [if_neg ht, mul_zero]
    exact I.zero_mem

/-- Every Laurent coefficient of the actual first angular contribution has precision six. -/
theorem actual_first_angular_error_escape_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualEscapeRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualFirstAngularError p) k) := by
  classical
  have he : RatFunc.C (WPReview.nativeEndpoint p)*actualFirstAngularError p =
      -(∑ j : Fin 3, ∑ n ∈ Finset.range p,
        RatFunc.C (WPReview.nativeEndpoint p*((n : ℚ)^j.val*WPReview.nativeCoefficient n))*
          actualFirstAngularKernel p n j) := by
    rw [actual_first_angular_error_finite, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [map_mul]
    ring
  rw [he, actual_escape_coefficient_neg]
  apply precisionZero_neg
  rw [actual_escape_coefficient_sum]
  apply precisionZero_sum
  intro j _hj
  rw [actual_escape_coefficient_sum]
  apply precisionZero_sum
  intro n hn
  by_cases hh : p-3≤n
  · rw [actual_escape_coefficient_scalar]
    exact precisionZero_mul_integral p 6 _ _
      (actual_endpoint_weighted_top_three_precision p n j.val hp (Finset.mem_range.mp hn) hh)
      ((integral_rational_escape_iff _ _).mp (actual_first_angular_kernel_escape_integral p n hp j) k)
  · rw [actual_first_angular_kernel_low_zero p n j (by omega), mul_zero]
    exact Or.inl (by simp [actualEscapeRationalCoefficient, actualEscapeRationalSeries, actualRationalSeries])

theorem actual_first_endpoint_error_escape_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualEscapeRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualFirstEndpointError p) k) := by
  rw [actual_first_endpoint_error_split, mul_add, actual_escape_coefficient_add]
  exact precisionZero_add p 6 _ _
    (actual_first_angular_error_escape_precision p hp k)
    (actual_first_conductor_error_escape_precision p hp k)

/-- Every signed Laurent coefficient of the complete actual source error has precision six at x=50/99. -/
theorem actual_source_conductor_error_escape_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualEscapeRationalCoefficient
      (actualTotalSource p-RatFunc.C (WPReview.nativeEndpoint p)*actualBetaFunctional p) k) := by
  rw [actual_source_conductor_error_identity p (by omega),
    actual_escape_coefficient_add, actual_escape_coefficient_add]
  exact precisionZero_add p 6 _ _
    (actual_first_angular_error_escape_precision p hp k)
    (precisionZero_add p 6 _ _
      (actual_first_conductor_error_escape_precision p hp k)
      (actual_angular_high_error_escape_precision p hp k))

end

end WPLiteralAdapter
