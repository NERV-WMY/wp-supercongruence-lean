import WPFieldAssembly.GreenLaurentOperators
import WPFiniteProductTail

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteProductTail
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- A whole shifted reciprocal pairs with its literal polynomial coefficient. -/
theorem reciprocal_derivative_monomial (s j : ℕ) (P : K[X]) (c : K) :
    (T (s : ℤ)*invert P.toLaurent*D (Polynomial.C c*X^j).toLaurent).coeff (-1)=
      c*(j : K)*P.coeff (s+j) := by
  rw [map_mul,Polynomial.toLaurent_C,Polynomial.toLaurent_X_pow,D_monomial]
  have he : T (s : ℤ)*invert P.toLaurent*
      (LaurentPolynomial.C (c*((j : ℤ) : K))*T ((j : ℤ)-1))=
      LaurentPolynomial.C (c*((j : ℤ) : K))*
        T ((s : ℤ)+(j : ℤ)-1)*invert P.toLaurent := by
    rw [show (s : ℤ)+(j : ℤ)-1=(s : ℤ)+((j : ℤ)-1) by ring,T_add]
    ring
  rw [he,shift_coeff,invert_apply,
    show -(-1-((s : ℤ)+(j : ℤ)-1))=((s+j : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat,Int.cast_natCast]

/-- The sum ranges over the complete original polynomial support. -/
theorem reciprocal_derivative_sum (s : ℕ) (P Q : K[X]) :
    (T (s : ℤ)*invert P.toLaurent*D Q.toLaurent).coeff (-1)=
      ∑ j ∈ Q.support, Q.coeff j*(j : K)*P.coeff (s+j) := by
  classical
  have hd : D Q.toLaurent=
      ∑ j ∈ Q.support, D (Polynomial.C (Q.coeff j)*X^j).toLaurent := by
    conv_lhs => rw [Q.as_sum_support_C_mul_X_pow]
    simp only [map_sum]
  rw [hd,Finset.mul_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact reciprocal_derivative_monomial s j P (Q.coeff j)

/-- A positive p phase vanishes only after the actual reciprocal degree bound is used. -/
theorem reciprocal_derivative_positive_phase_zero (p : ℕ) (P Q : K[X])
    (hP : P.natDegree<p) :
    (T (p : ℤ)*invert P.toLaurent*D Q.toLaurent).coeff (-1)=0 := by
  classical
  rw [reciprocal_derivative_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<p+j),mul_zero]

/-- The entire negative p band is regularity-excluded, without deleting its source. -/
theorem reciprocal_derivative_negative_phase_zero (p : ℕ) (P Q : K[X])
    (hQ : Q.natDegree<p) :
    (T (-(p : ℤ))*invert P.toLaurent*D Q.toLaurent).coeff (-1)=0 := by
  have hleft := Above_shift (Above_invert_toLaurent P) (-(p : ℤ))
  have hright := Above_D (Above_toLaurent Q Q.natDegree le_rfl)
  have hwhole := Above_mul hleft hright
  exact hwhole (-1) (by omega)

/-- The literal finite logarithm pairs with an actual endpoint and the retained origin. -/
theorem reciprocal_log_derivative_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hQ : Q.natDegree<p) (c : K) :
    (invert ((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c*X)).toLaurent*
      D Q.toLaurent).coeff (-1)=Q.eval c-Q.eval 0 := by
  classical
  have hc := congrArg (fun R : K[X] => R.eval c) Q.as_sum_support_C_mul_X_pow
  have h0 := congrArg (fun R : K[X] => R.eval 0) Q.as_sum_support_C_mul_X_pow
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] at hc h0
  have heval : Q.eval c-Q.eval 0=
      ∑ j ∈ Q.support, Q.coeff j*(c^j-(0 : K)^j) := by
    rw [hc,h0,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr := reciprocal_derivative_sum 0
    ((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c*X)) Q
  rw [Nat.cast_zero,T_zero,one_mul] at hr
  simp only [Nat.zero_add] at hr
  rw [hr,heval]
  apply Finset.sum_congr rfl
  intro j hj
  rw [LP_scaled_coeff]
  by_cases hj0 : j=0
  · subst j
    simp
  · have hjp : j<p := (le_natDegree_of_mem_supp j hj).trans_lt hQ
    have hjunit : (j : K)≠0 := WPFiniteField.denominator_ne_zero p j
      (Finset.mem_Ico.mpr (by omega))
    rw [if_pos (by omega : 1≤j ∧ j<p),zero_pow hj0,sub_zero]
    field_simp [hjunit]

/-- The two actual logarithm rows keep the common origin coefficient in their pairing. -/
theorem reciprocal_logTrace_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hQ : Q.natDegree<p) :
    (invert (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent*D Q.toLaurent).coeff (-1)=
      -(1/4 : K)*(Q.eval 4-Q.eval 0)+4*(Q.eval (1/4)-Q.eval 0) := by
  have hfirst := reciprocal_log_derivative_endpoint p Q hQ (4 : K)
  have hsecond := reciprocal_log_derivative_endpoint p Q hQ (1/4 : K)
  simp only [WPFiniteABSourceTail.logTrace,map_add,map_mul,map_neg,
    Polynomial.toLaurent_C,invert_C,add_mul,neg_mul,mul_assoc,
    AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    AddMonoidAlgebra.coeff_neg,Finsupp.neg_apply,C_mul_coeff,hfirst,hsecond]

end WPFieldAssembly.ActualBpairContraction
