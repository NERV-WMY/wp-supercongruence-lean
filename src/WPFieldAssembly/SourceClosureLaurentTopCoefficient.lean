import WPFiniteLaurentDifferential

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureLaurentTopCoefficient

set_option maxHeartbeats 800000

theorem laurent_coeff_finset_sum {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (F : ι → K[T;T⁻¹]) (j : ℤ) :
    (∑ i ∈ s,F i).coeff j=∑ i ∈ s,(F i).coeff j := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,ih]

/-- A bounded whole Laurent carrier contributes only its top coefficient at the
top of a product with the actual polynomial; lower coefficients are not assigned. -/
theorem polynomial_times_laurent_top {K : Type*} [Field K]
    (F : K[X]) (R : K[T;T⁻¹]) (b : ℤ) (hR : Above R b) :
    (F.toLaurent*R).coeff ((F.natDegree : ℤ)+b)=F.leadingCoeff*R.coeff b := by
  classical
  have he : F.toLaurent*R=
      ∑ n ∈ Finset.range (F.natDegree+1),
        LaurentPolynomial.C (F.coeff n)*T (n : ℤ)*R := by
    have h := congrArg (fun P : K[X] => P.toLaurent*R)
      F.as_sum_range_C_mul_X_pow
    simpa only [map_sum,Finset.sum_mul,map_mul,Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow] using h
  rw [he,laurent_coeff_finset_sum,Finset.sum_range_succ]
  have hzero : (∑ n ∈ Finset.range F.natDegree,
      (LaurentPolynomial.C (F.coeff n)*T (n : ℤ)*R).coeff ((F.natDegree : ℤ)+b))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [WPFiniteJCarrier.shifted_coeff,hR _ (by omega),mul_zero]
  rw [hzero,zero_add,WPFiniteJCarrier.shifted_coeff,
    show (F.natDegree : ℤ)+b-(F.natDegree : ℤ)=b by omega,coeff_natDegree]

end WPFieldAssembly.SourceClosureLaurentTopCoefficient
