import WPFieldAssembly.ActualKwWeightedTrace
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial BigOperators
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualKwWeightedTrace

namespace WPFieldAssembly.SourceClosureVbalProperSquareEndpoints

set_option maxHeartbeats 1800000

section Endpoint
variable {K : Type*} [Field K]

theorem endpoint_of_nonpositive (a b : K) (F : K[T;T⁻¹])
    (hF : Above F 0) : endpointTrace a b F=0 := by
  classical
  have hs : (∑ n∈F.coeff.support, LaurentPolynomial.C (F.coeff n)*T n)=F := by
    simpa only [Finsupp.sum,single_eq_C_mul_T] using AddMonoidAlgebra.sum_coeff_single F
  rw [←hs,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hn0 : n≤0 := by
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hn) (hF n (by omega))
  rw [endpointTrace_monomial,endpointWeight_nonpositive a b n hn0,mul_zero]

theorem endpoint_positive_polynomial (a b : K) (P : K[X]) (m : ℕ)
    (hm : 0<m) : endpointTrace a b (T (m : ℤ)*P.toLaurent)=
      -2*b^m*P.eval b-a^m*P.eval a := by
  have he : (T (m : ℤ)*P.toLaurent : K[T;T⁻¹])=(X^m*P).toLaurent := by
    rw [map_mul,Polynomial.toLaurent_X_pow]
  rw [he,endpointTrace_polynomial]
  have hz : (X^m*P : K[X]).coeff 0=0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [eval_mul,eval_pow,eval_X,zero_pow (by omega : m≠0),zero_mul]
  simp only [eval_mul,eval_pow,eval_X,hz,mul_zero,add_zero]
  ring

theorem endpoint_positive_inverse (a b : K) (ha : a≠0) (hb : b≠0)
    (P : K[X]) (m : ℕ) (hm : P.natDegree<m) :
    endpointTrace a b (T (m : ℤ)*invert P.toLaurent)=
      -2*b^m*P.eval b⁻¹-a^m*P.eval a⁻¹ := by
  classical
  have hs := P.as_sum_range_C_mul_X_pow
  have hea := congrArg (fun Q : K[X] => Q.eval a⁻¹) hs
  have heb := congrArg (fun Q : K[X] => Q.eval b⁻¹) hs
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] at hea heb
  conv_lhs => rw [hs]
  simp only [map_sum,map_mul,Polynomial.toLaurent_C,Polynomial.toLaurent_X_pow,
    invert_C,invert_T]
  simp only [Finset.mul_sum,map_sum]
  have hterm (i : ℕ) (hi : i∈Finset.range (P.natDegree+1)) :
      endpointTrace a b (T (m : ℤ)*(LaurentPolynomial.C (P.coeff i)*T (-(i : ℤ))))=
        -2*b^m*(P.coeff i*b⁻¹^i)-a^m*(P.coeff i*a⁻¹^i) := by
    have hi' : i<m := by have := Finset.mem_range.mp hi; omega
    have hT : (T (m : ℤ)*(LaurentPolynomial.C (P.coeff i)*T (-(i : ℤ))) :
        K[T;T⁻¹])=LaurentPolynomial.C (P.coeff i)*T ((m-i : ℕ) : ℤ) := by
      rw [mul_comm (T (m : ℤ)),mul_assoc,←T_add]
      congr 2
      omega
    rw [hT,endpointTrace_monomial,endpointWeight_nat,if_neg (by omega : m-i≠0)]
    have hpa : a^(m-i)=a^m*a⁻¹^i := by
      rw [pow_sub₀ a ha (by omega),inv_pow]
    have hpb : b^(m-i)=b^m*b⁻¹^i := by
      rw [pow_sub₀ b hb (by omega),inv_pow]
    rw [hpa,hpb]
    ring
  rw [hea,heb]
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl hterm

theorem endpoint_shift_regular_zero (a b : K) (P : K[X]) (s : ℤ)
    (hs : s+(P.natDegree : ℤ)≤0) : endpointTrace a b (T s*P.toLaurent)=0 := by
  exact endpoint_of_nonpositive a b _ (Above_mono
    (Above_shift (Above_toLaurent P P.natDegree le_rfl) s) hs)

theorem endpoint_shift_inverse_zero (a b : K) (P : K[X]) (s : ℤ)
    (hs : s≤0) : endpointTrace a b (T s*invert P.toLaurent)=0 := by
  exact endpoint_of_nonpositive a b _ (Above_mono
    (Above_shift (Above_invert_toLaurent P) s) (by omega))

private theorem shift_term (s j : ℤ) (c : K) (F : K[T;T⁻¹]) :
    T s*(LaurentPolynomial.C c*T j*F)=LaurentPolynomial.C c*T (s+j)*F := by
  rw [show T s*(LaurentPolynomial.C c*T j*F)=
    LaurentPolynomial.C c*(T s*T j)*F by ring,←T_add]

theorem endpoint_shift_constant (a b c : K) (s : ℤ) (F : K[T;T⁻¹]) :
    endpointTrace a b (T s*(LaurentPolynomial.C c*F))=
      c*endpointTrace a b (T s*F) := by
  rw [show T s*(LaurentPolynomial.C c*F)=LaurentPolynomial.C c*(T s*F) by ring,
    endpointTrace_C_mul]

theorem endpoint_shift_term (a b c : K) (s j : ℤ) (F : K[T;T⁻¹]) :
    endpointTrace a b (T s*(LaurentPolynomial.C c*T j*F))=
      c*endpointTrace a b (T (s+j)*F) := by
  rw [shift_term,mul_assoc,endpointTrace_C_mul]

end Endpoint

end WPFieldAssembly.SourceClosureVbalProperSquareEndpoints
