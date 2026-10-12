import WPActualFiniteResidueAttachment

open scoped LaurentSeries BigOperators
open HahnSeries Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

theorem actual_laurent_power_quotient (a b : ℕ) :
    algebraMap (RatFunc (RatFunc ℚ)) (LaurentSeries (RatFunc ℚ))
      (bivS^a/bivS^b) = single ((a : ℤ)-(b : ℤ)) 1 := by
  simp only [map_div₀, map_pow, actual_laurent_s,
    single_pow, nsmul_eq_mul, one_pow, single_div_single, div_one]
  congr 1
  ring

/-- Formal residue of an actual Laurent monomial at a nonzero finite pole. -/
theorem actual_power_pole_residue (a b : ℕ) (c : RatFunc ℚ) (hc : c≠0) :
    rationalResidue (bivS^a/(bivS^b*(bivS-RatFunc.C c))) =
      if a<b then -(c⁻¹)^(b-a) else 0 := by
  have hsplit : bivS^a/(bivS^b*(bivS-RatFunc.C c)) =
      (bivS^a/bivS^b)/(bivS-RatFunc.C c) := by rw [div_mul_eq_div_div]
  rw [hsplit, rationalResidue, laurentResidue, map_div₀,
    actual_laurent_power_quotient, map_sub, actual_laurent_s,
    rational_laurent_coefficient]
  simp only [div_eq_mul_inv]
  simpa only [one_pow, one_mul] using geometric_pole_residue a b 1 c hc

theorem actual_diagonal_shifted_residue (p a : ℕ) :
    lambda^p * rationalResidue
      (bivS^a/(bivS^(p+3)*(bivS-bivLambda))) =
      if a<p+3 then -(lambda^a/lambda^3) else 0 := by
  have hl : lambda ≠ 0 := by
    unfold lambda
    exact mul_ne_zero (by norm_num) (pow_ne_zero _
      (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero))
  rw [bivLambda, actual_power_pole_residue a (p+3) lambda hl]
  by_cases ha : a<p+3
  · rw [if_pos ha, if_pos ha]
    have hpow : lambda^(p+3) = lambda^a*lambda^(p+3-a) := by
      rw [← pow_add]
      congr 1
      omega
    have hcalc : lambda^p*(lambda⁻¹)^(p+3-a) = lambda^a/lambda^3 := by
      rw [inv_pow, ← div_eq_mul_inv]
      apply (div_eq_div_iff (pow_ne_zero _ hl) (pow_ne_zero _ hl)).2
      simpa only [← pow_add] using hpow
    simpa only [mul_neg] using congrArg Neg.neg hcalc
  · simp only [if_neg ha, mul_zero]

/-- The finite diagonal endpoint leaves exactly its polynomial high tail. -/
theorem finite_laurent_diagonal_endpoint (p N : ℕ) (P : Polynomial (RatFunc ℚ))
    (hP : P.natDegree<N) :
    lambda^p * rationalResidue
      (Polynomial.aeval bivS P/(bivS^(p+3)*(bivS-bivLambda))) =
      -P.eval lambda/lambda^3 +
        ∑ a ∈ Finset.range N,
          if p+3≤a then P.coeff a*lambda^a/lambda^3 else 0 := by
  rw [Polynomial.aeval_eq_sum_range' hP, Polynomial.eval_eq_sum_range' hP]
  simp only [Algebra.smul_def, Finset.sum_div, rationalResidue_sum,
    Finset.mul_sum]
  have ht (a : ℕ) :
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ))) (P.coeff a) * bivS^a /
          (bivS^(p+3)*(bivS-bivLambda)) =
      RatFunc.C (P.coeff a) *
        (bivS^a/(bivS^(p+3)*(bivS-bivLambda))) := by
    rw [RatFunc.algebraMap_eq_C]
    ring
  have hm (a : ℕ) (r : RatFunc ℚ) : lambda^p*(P.coeff a*r) =
      P.coeff a*(lambda^p*r) := by ring
  simp_rw [ht, rationalResidue_coefficient_mul, hm,
    actual_diagonal_shifted_residue]
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases ha : a<p+3
  · rw [if_pos ha, if_neg (by omega : ¬p+3≤a)]
    ring
  · rw [if_neg ha, if_pos (by omega : p+3≤a)]
    ring

theorem actual_power_geometric_residue (a b : ℕ) :
    rationalResidue (bivS^a/(bivS^b*(1-bivS))) =
      if a<b then 1 else 0 := by
  have hd : 1-bivS = -(bivS-1) := by ring
  rw [hd, mul_neg, div_neg, rationalResidue_neg]
  have h1 : (RatFunc.C (1 : RatFunc ℚ) : RatFunc (RatFunc ℚ))=1 := map_one _
  rw [← h1, actual_power_pole_residue a b 1 one_ne_zero]
  by_cases ha : a<b <;> simp [ha]

/-- Exact finite first-endpoint extraction for a cleared actual angular Laurent polynomial. -/
theorem finite_laurent_first_kernel (p n N : ℕ) (P : Polynomial (RatFunc ℚ))
    (hP : P.natDegree<N) :
    rationalResidue (bivS^(p-1)/(1-bivS)*
      (Polynomial.aeval bivS P/bivS^3)*bivB^n) =
      ∑ k ∈ Finset.range N,
        P.coeff k*lambda^n*(if p-1+k<n+3 then 1 else 0) := by
  rw [Polynomial.aeval_eq_sum_range' hP]
  simp only [Algebra.smul_def, Finset.sum_div, Finset.mul_sum, Finset.sum_mul,
    rationalResidue_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have ht : bivS^(p-1)/(1-bivS)*
      (algebraMap (RatFunc ℚ) (RatFunc (RatFunc ℚ)) (P.coeff k)*bivS^k/bivS^3)*bivB^n =
      RatFunc.C (P.coeff k*lambda^n)*
        (bivS^(p-1+k)/(bivS^(n+3)*(1-bivS))) := by
    simp only [RatFunc.algebraMap_eq_C, map_mul, map_pow,
      bivB, bivLambda, div_pow, pow_add]
    field_simp [bivS_ne_zero, biv_one_sub_s_ne_zero]
  rw [ht, rationalResidue_coefficient_mul, actual_power_geometric_residue]

end

end WPForcedSourceStokes
