import WPActualAngularHighPrecision

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000

noncomputable def actualFirstAngularKernel (p n : ℕ) (j : Fin 3) : RatFunc ℚ :=
  rationalResidue (bivS^(p-1)/(1-bivS)*bivEta 2 j*bivB^n)

noncomputable def actualFirstAngularError (p : ℕ) : RatFunc ℚ :=
  -rationalResidue (bivS^(p-1)/(1-bivS)*
    ∑ j : Fin 3, bivEta 2 j*finiteNativeJet p bivB j)

noncomputable def actualFirstConductorError (p : ℕ) : RatFunc ℚ :=
  rationalResidue (bivS^(p-1)/(1-bivS)*
    ∑ j : Fin 3, bivConductorBU 2 j*finiteNativeJet p bivB j)

theorem actual_first_endpoint_error_split (p : ℕ) :
    actualFirstEndpointError p = actualFirstAngularError p+actualFirstConductorError p := by
  have ht (j : Fin 3) : (bivEta 2 j-bivConductorBU 2 j)*finiteNativeJet p bivB j =
      bivEta 2 j*finiteNativeJet p bivB j-bivConductorBU 2 j*finiteNativeJet p bivB j := by ring
  simp only [actualFirstEndpointError, actualFirstAngularError, actualFirstConductorError, ht,
    Finset.sum_sub_distrib, mul_sub, rationalResidue_sub]
  ring

theorem actual_first_angular_kernel_finite (p n : ℕ) (j : Fin 3) :
    actualFirstAngularKernel p n j =
      ∑ k ∈ Finset.range ((etaClearedPolynomial 2 j).natDegree+1),
        (etaClearedPolynomial 2 j).coeff k*lambda^n*
          (if p-1+k<n+3 then 1 else 0) := by
  have hc : bivEta 2 j = Polynomial.aeval bivS (etaClearedPolynomial 2 j)/bivS^3 := by
    apply (eq_div_iff (pow_ne_zero _ bivS_ne_zero)).2
    simpa only [mul_comm] using (actual_eta_cleared_polynomial 2 j).symm
  unfold actualFirstAngularKernel
  rw [hc]
  exact finite_laurent_first_kernel p n _ _ (Nat.lt_succ_self _)

/-- Actual low native indices have zero first angular residue in the declared Laurent chamber. -/
theorem actual_first_angular_kernel_low_zero (p n : ℕ) (j : Fin 3) (hn : n+4≤p) :
    actualFirstAngularKernel p n j = 0 := by
  rw [actual_first_angular_kernel_finite]
  apply Finset.sum_eq_zero
  intro k _hk
  rw [if_neg (by omega : ¬p-1+k<n+3), mul_zero]

theorem actual_first_angular_kernel_origin_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19≤p) (j : Fin 3) :
    actualFirstAngularKernel p n j ∈
      integralRationalOrigin (WPFiniteConductorPolynomial.integralSubring p) := by
  let I := integralRationalOrigin (WPFiniteConductorPolynomial.integralSubring p)
  rw [actual_first_angular_kernel_finite]
  apply I.sum_mem
  intro k _hk
  by_cases ht : p-1+k<n+3
  · rw [if_pos ht, mul_one]
    exact I.mul_mem
      ((mem_polynomialCoefficientSubring I _).mp (eta_cleared_polynomial_integral p hp 2 j) k)
      (I.pow_mem (actual_lambda_origin_integral p hp) n)
  · rw [if_neg ht, mul_zero]
    exact I.zero_mem

theorem actual_first_angular_error_finite (p : ℕ) :
    actualFirstAngularError p =
      -(∑ j : Fin 3, ∑ n ∈ Finset.range p,
        RatFunc.C ((n : ℚ)^j.val*WPReview.nativeCoefficient n)*actualFirstAngularKernel p n j) := by
  simp only [actualFirstAngularError, finite_native_jet_sum, outer_native_scalar,
    Finset.mul_sum, rationalResidue_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro n _hn
  have ht : bivS^(p-1)/(1-bivS)*
      (bivEta 2 j*(RatFunc.C (RatFunc.C ((n : ℚ)^j.val*WPReview.nativeCoefficient n))*bivB^n)) =
      RatFunc.C (RatFunc.C ((n : ℚ)^j.val*WPReview.nativeCoefficient n))*
        (bivS^(p-1)/(1-bivS)*bivEta 2 j*bivB^n) := by ring
  rw [ht, rationalResidue_coefficient_mul]
  rfl

/-- Every Laurent coefficient of the actual first angular contribution has precision six. -/
theorem actual_first_angular_error_origin_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
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
  rw [he, actual_rational_coefficient_neg]
  apply precisionZero_neg
  rw [actual_rational_coefficient_sum]
  apply precisionZero_sum
  intro j _hj
  rw [actual_rational_coefficient_sum]
  apply precisionZero_sum
  intro n hn
  by_cases hh : p-3≤n
  · rw [actual_rational_coefficient_scalar]
    exact precisionZero_mul_integral p 6 _ _
      (actual_endpoint_weighted_top_three_precision p n j.val hp (Finset.mem_range.mp hn) hh)
      (actual_first_angular_kernel_origin_integral p n hp j k)
  · rw [actual_first_angular_kernel_low_zero p n j (by omega), mul_zero]
    exact Or.inl (by simp [actualRationalCoefficient, actualRationalSeries])

end

end WPForcedSourceStokes
