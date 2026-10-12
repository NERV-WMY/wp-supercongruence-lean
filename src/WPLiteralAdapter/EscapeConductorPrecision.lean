import WPLiteralAdapter.EscapeUnits

open scoped BigOperators
open WPFiniteConductorPolynomial

namespace WPLiteralAdapter

open WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

attribute [local irreducible] integralRationalOrigin polynomialCoefficientSubring

/-- The actual conductor numerators use only the displayed scalar inverses and the coefficient variable. -/
theorem actual_first_conductor_numerators_integral_in (I : Subring (RatFunc ℚ))
    (hx : symbol∈I) (h2 : (1/2 : RatFunc ℚ)∈I) (h3 : (1/3 : RatFunc ℚ)∈I)
    (h5 : (1/5 : RatFunc ℚ)∈I) :
    firstConductorMean∈I ∧ firstConductorNumeratorZero∈I ∧ firstConductorNumeratorOne∈I := by
  have h1000 : (27/1000 : RatFunc ℚ)∈I := by
    rw [show (27/1000 : RatFunc ℚ)=27*(1/2)^3*(1/5)^3 by norm_num]
    exact I.mul_mem (I.mul_mem (natCast_mem I 27) (I.pow_mem h2 3)) (I.pow_mem h5 3)
  have h209952 : (209952 : RatFunc ℚ)⁻¹∈I := by
    rw [show (209952 : RatFunc ℚ)⁻¹=(1/2)^5*(1/3)^8 by norm_num]
    exact I.mul_mem (I.pow_mem h2 5) (I.pow_mem h3 8)
  have h15625 : (2187/15625 : RatFunc ℚ)∈I := by
    rw [show (2187/15625 : RatFunc ℚ)=2187*(1/5)^6 by norm_num]
    exact I.mul_mem (natCast_mem I 2187) (I.pow_mem h5 6)
  have hm : firstConductorMean∈I := by
    unfold firstConductorMean
    repeat' first
      | exact h1000
      | exact hx
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
      | apply I.pow_mem
  have hmd : firstConductorMeanDerivative∈I := by
    unfold firstConductorMeanDerivative
    repeat' first
      | exact h1000
      | exact hx
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
      | apply I.pow_mem
  have he : firstConductorEll∈I := by
    unfold firstConductorEll
    repeat' first
      | exact h1000
      | exact hx
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.sub_mem
  have hed : firstConductorEllDerivative∈I := by
    unfold firstConductorEllDerivative
    repeat' first
      | exact h1000
      | exact hx
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.sub_mem
  have hL : firstConductorLP∈I := by
    unfold firstConductorLP
    rw [div_eq_mul_inv]
    repeat' first
      | exact hx
      | exact h209952
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
      | apply I.pow_mem
  have hR : firstConductorRP∈I := by
    unfold firstConductorRP
    rw [div_eq_mul_inv]
    repeat' first
      | exact hx
      | exact h209952
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
      | apply I.pow_mem
  have hK : firstConductorK∈I := by
    unfold firstConductorK
    repeat' first
      | exact hx
      | exact he
      | exact hed
      | exact I.one_mem
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
  have hN0 : firstConductorNumeratorZero∈I := by
    unfold firstConductorNumeratorZero
    repeat' first
      | exact hx
      | exact hL
      | exact hR
      | exact he
      | exact hm
      | exact hmd
      | exact hK
      | exact h15625
      | exact I.one_mem
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.add_mem
      | apply I.sub_mem
  have hN1 : firstConductorNumeratorOne∈I := by
    unfold firstConductorNumeratorOne
    repeat' first
      | exact hx
      | exact hL
      | exact hR
      | exact hmd
      | exact hK
      | exact I.one_mem
      | exact natCast_mem I _
      | apply I.mul_mem
      | apply I.sub_mem
      | apply I.neg_mem
  exact ⟨hm,hN0,hN1⟩

/-- The full affine numerator is integral in the actual translated coefficient ring. -/
theorem actual_first_conductor_numerators_escape_integral (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) :
    firstConductorMean ∈ integralRationalEscape (integralSubring p) ∧
      firstConductorNumeratorZero ∈ integralRationalEscape (integralSubring p) ∧
      firstConductorNumeratorOne ∈ integralRationalEscape (integralSubring p) :=
  actual_first_conductor_numerators_integral_in _ (actual_escape_symbol_integral p hp)
    (actual_small_inverse_escape p 2 (by norm_num) (by omega))
    (actual_small_inverse_escape p 3 (by norm_num) (by omega))
    (actual_small_inverse_escape p 5 (by norm_num) (by omega))

theorem actual_first_conductor_divisor_inverse_escape_integral (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) : firstConductorDivisor⁻¹ ∈ integralRationalEscape (integralSubring p) := by
  let I := integralRationalEscape (integralSubring p)
  have hM : (25-9*symbol)⁻¹∈I := by
    rw [show 25-9*symbol=-(9*symbol-25) by ring, inv_neg]
    exact I.neg_mem (actual_escape_M_inverse_integral p hp)
  have hf : firstConductorDivisor⁻¹=(symbol⁻¹)^4*(25-9*symbol)⁻¹*((99*symbol-50)⁻¹)^2 := by
    rw [firstConductorDivisor]
    simp only [mul_inv_rev, ← inv_pow]
    ring
  rw [hf]
  exact I.mul_mem (I.mul_mem (I.pow_mem (actual_escape_symbol_inverse_integral p hp) 4) hM)
    (I.pow_mem (actual_escape_e_inverse_integral p hp) 2)

theorem actual_first_conductor_kernel_escape_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) : actualFirstConductorKernel p n ∈ integralRationalEscape (integralSubring p) := by
  let I := integralRationalEscape (integralSubring p)
  have hN := actual_first_conductor_numerators_escape_integral p hp
  unfold actualFirstConductorKernel
  rw [div_eq_mul_inv]
  exact I.mul_mem (I.mul_mem (natCast_mem I 2)
    (actual_first_conductor_divisor_inverse_escape_integral p hp))
    (first_quadratic_kernel_integral I p n _ _ _ hN.1 hN.2.1 hN.2.2
      (actual_lambda_escape_integral p hp) (actual_lambda_inverse_escape_integral p hp))

/-- The actual conductor correction has precision six at every signed escape coefficient. -/
theorem actual_first_conductor_error_escape_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualEscapeRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualFirstConductorError p) k) := by
  classical
  have he : RatFunc.C (WPReview.nativeEndpoint p)*actualFirstConductorError p =
      ∑ n ∈ Finset.range p,
        RatFunc.C (WPReview.nativeEndpoint p*WPReview.nativeCoefficient n)*actualFirstConductorKernel p n := by
    rw [actual_first_conductor_error_finite, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [map_mul]
    ring
  rw [he, actual_escape_coefficient_sum]
  apply precisionZero_sum
  intro n hn
  by_cases hh : p-3≤n
  · rw [actual_escape_coefficient_scalar]
    exact precisionZero_mul_integral p 6 _ _
      (actual_endpoint_top_three_precision p n hp (Finset.mem_range.mp hn) hh)
      ((integral_rational_escape_iff _ _).mp
        (actual_first_conductor_kernel_escape_integral p n hp) k)
  · rw [actual_first_conductor_kernel_low_zero p n (by omega), mul_zero]
    exact Or.inl (by simp [actualEscapeRationalCoefficient, actualEscapeRationalSeries, actualRationalSeries])

end

end WPLiteralAdapter
