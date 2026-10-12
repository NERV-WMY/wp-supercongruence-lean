import WPFiniteQuadraticResidue

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1500000

def firstQuadraticCoefficient (m : RatFunc ℚ) (a b : ℕ) : RatFunc ℚ :=
  if a<b then PowerSeries.coeff (b-a-1) (finiteQuadraticInverse m lambda) else 0

def firstQuadraticKernel (p n : ℕ) (m N0 N1 : RatFunc ℚ) : RatFunc ℚ :=
  rationalResidue (bivS^(p-1)*(RatFunc.C N0+RatFunc.C N1*bivS)/
    algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (finiteQuadraticPolynomial m lambda)*
      bivB^(n+2)*(1-bivB))

theorem first_quadratic_divisor_ne_zero (m : RatFunc ℚ) :
    algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (finiteQuadraticPolynomial m lambda) ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro hz
  have hc := congrArg (fun P : Polynomial (RatFunc ℚ) => P.coeff 0) hz
  norm_num [finiteQuadraticPolynomial] at hc
  apply (mul_ne_zero (by norm_num : (729/15625 : RatFunc ℚ)≠0)
    (pow_ne_zero 3 (RatFunc.algebraMap_ne_zero X_ne_zero)))
  simpa only [lambda, symbol] using hc

/-- The complete first conductor kernel uses four coefficients of the regular inverse. -/
theorem first_quadratic_kernel_finite (p n : ℕ) (m N0 N1 : RatFunc ℚ) :
    firstQuadraticKernel p n m N0 N1 =
      lambda^(n+2)*N0*firstQuadraticCoefficient m (p-1) (n+2)+
      lambda^(n+2)*N1*firstQuadraticCoefficient m (p-1+1) (n+2)-
      lambda^(n+3)*N0*firstQuadraticCoefficient m (p-1) (n+3)-
      lambda^(n+3)*N1*firstQuadraticCoefficient m (p-1+1) (n+3) := by
  have hl : lambda≠0 := by
    unfold lambda
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero _ (RatFunc.algebraMap_ne_zero X_ne_zero))
  let Q := algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
    (finiteQuadraticPolynomial m lambda)
  have hQ : Q≠0 := first_quadratic_divisor_ne_zero m
  have ht : bivS^(p-1)*(RatFunc.C N0+RatFunc.C N1*bivS)/Q*bivB^(n+2)*(1-bivB) =
      RatFunc.C (lambda^(n+2)*N0)*(bivS^(p-1)/(bivS^(n+2)*Q))+
      RatFunc.C (lambda^(n+2)*N1)*(bivS^(p-1+1)/(bivS^(n+2)*Q))-
      RatFunc.C (lambda^(n+3)*N0)*(bivS^(p-1)/(bivS^(n+3)*Q))-
      RatFunc.C (lambda^(n+3)*N1)*(bivS^(p-1+1)/(bivS^(n+3)*Q)) := by
    simp only [bivB, bivLambda, div_pow, map_mul, map_pow]
    field_simp [bivS_ne_zero, hQ]
    simp only [pow_succ]
    ring
  unfold firstQuadraticKernel
  change rationalResidue (bivS^(p-1)*(RatFunc.C N0+RatFunc.C N1*bivS)/Q*
    bivB^(n+2)*(1-bivB)) = _
  rw [ht]
  simp only [rationalResidue_add, rationalResidue_sub, rationalResidue_coefficient_mul, Q]
  rw [finite_quadratic_power_residue (p-1) (n+2) m lambda hl,
    finite_quadratic_power_residue (p-1+1) (n+2) m lambda hl,
    finite_quadratic_power_residue (p-1) (n+3) m lambda hl,
    finite_quadratic_power_residue (p-1+1) (n+3) m lambda hl]
  rfl

theorem first_quadratic_kernel_low_zero (p n : ℕ) (m N0 N1 : RatFunc ℚ)
    (hn : n+4≤p) : firstQuadraticKernel p n m N0 N1=0 := by
  rw [first_quadratic_kernel_finite]
  simp only [firstQuadraticCoefficient, if_neg (by omega : ¬p-1<n+2),
    if_neg (by omega : ¬p-1+1<n+2), if_neg (by omega : ¬p-1<n+3),
    if_neg (by omega : ¬p-1+1<n+3), mul_zero, add_zero, sub_zero]

theorem first_quadratic_kernel_integral (R : Subring (RatFunc ℚ))
    (p n : ℕ) (m N0 N1 : RatFunc ℚ) (hm : m∈R) (h0 : N0∈R) (h1 : N1∈R)
    (hl : lambda∈R) (hli : lambda⁻¹∈R) : firstQuadraticKernel p n m N0 N1 ∈ R := by
  have hcoef (a b : ℕ) : firstQuadraticCoefficient m a b ∈ R := by
    unfold firstQuadraticCoefficient
    split_ifs
    · exact finite_quadratic_inverse_integral R m lambda hm hl hli _
    · exact R.zero_mem
  rw [first_quadratic_kernel_finite]
  exact R.sub_mem (R.sub_mem (R.add_mem
    (R.mul_mem (R.mul_mem (R.pow_mem hl _) h0) (hcoef _ _))
    (R.mul_mem (R.mul_mem (R.pow_mem hl _) h1) (hcoef _ _)))
    (R.mul_mem (R.mul_mem (R.pow_mem hl _) h0) (hcoef _ _)))
    (R.mul_mem (R.mul_mem (R.pow_mem hl _) h1) (hcoef _ _))

end

end WPForcedSourceStokes
