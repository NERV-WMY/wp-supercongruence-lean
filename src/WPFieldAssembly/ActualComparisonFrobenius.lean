import WPFieldAssembly.ActualComparisonKwAttachment
import WPFieldAssembly.ActualEntropyEndpoints
import WPFieldAssembly.ActualEntropyFifth
import WPFieldAssembly.ActualWeightedF0Carry

open scoped BigOperators Polynomial LaurentPolynomial PowerSeries
open Polynomial LaurentPolynomial WPPIntegralReduction
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.ActualKwSeriesAttachment
  WPFieldAssembly.ActualComparisonKwAttachment WPFieldAssembly.ActualBalancedTrace

namespace WPFieldAssembly.ActualComparisonFrobenius

set_option maxHeartbeats 1400000

theorem frobeniusUnit_coeff_two_slots (p r : ℕ) (hp : 0<p) (hr : r<2*p)
    (a b c : ℚ) :
    PowerSeries.coeff r (ActualKwFirstCarry.frobeniusUnit p a b c)=
      (if r=0 then 1 else 0)+(if r=p then a^p+b^p-c^p else 0) := by
  rw [(ActualKwFirstCarry.frobeniusUnit_firstJet p hp a b c).coeff r hr,map_add,
    PowerSeries.coeff_C_mul_X_pow]
  simp [eq_comm]

/-- The two Frobenius coefficients act on the entire signed input. -/
theorem frobeniusTrace_full_source (p B : ℕ) (hp : 0<p) (hpB : p<B) (hB : B≤2*p)
    (a b c : ℚ) (L : ℚ[T;T⁻¹])
    (hL : ∀ n∈L.coeff.support, n≤(B : ℤ)) :
    seriesWeightedTrace (ActualKwFirstCarry.frobeniusUnit p a b c) L=
      rationalDlogQ L+(a^p+b^p-c^p)*rationalDlogQ (T (-(p : ℤ))*L) := by
  have he := finiteCoupling_full_source B
    (ActualKwFirstCarry.frobeniusUnit p a b c) L.coeff.support L.coeff hL
  rw [←laurent_full_signed_expansion] at he
  rw [←he]
  change (∑ r∈Finset.range B,
    PowerSeries.coeff r (ActualKwFirstCarry.frobeniusUnit p a b c)*
      rationalDlogQ (T (-(r : ℤ))*L))=_
  have hc : ∀ r∈Finset.range B,
      PowerSeries.coeff r (ActualKwFirstCarry.frobeniusUnit p a b c)=
        (if r=0 then 1 else 0)+(if r=p then a^p+b^p-c^p else 0) := by
    intro r hr
    exact frobeniusUnit_coeff_two_slots p r hp (by
      have := Finset.mem_range.mp hr
      omega) a b c
  rw [Finset.sum_congr rfl (fun (r : ℕ) hr => congrArg
    (fun q : ℚ => q*rationalDlogQ (T (-(r : ℤ))*L)) (hc r hr))]
  simp only [add_mul,ite_mul]
  rw [Finset.sum_add_distrib]
  simp [Finset.mem_range.mpr hpB,show 0<B by omega]

theorem endpointTrace_shift_nonpositive (q : ℕ) (P : ℚ[X])
    (hP : P.natDegree≤q) (a b : ℚ) :
    endpointTrace a b (T (-(q : ℤ))*(P.toLaurent+invert P.toLaurent))=0 := by
  rw [original_laurent_expansion,map_sum,mul_add,Finset.mul_sum,Finset.mul_sum,map_add]
  have hpos : endpointTrace a b
      (∑ j∈P.support, T (-(q : ℤ))*(LaurentPolynomial.C (P.coeff j)*T (j : ℤ)))=0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjq := (le_natDegree_of_mem_supp j hj).trans hP
    have ht : (T (-(q : ℤ)) : ℚ[T;T⁻¹])*
        (LaurentPolynomial.C (P.coeff j)*T (j : ℤ))=
          LaurentPolynomial.C (P.coeff j)*T ((j : ℤ)-q) := by
      rw [mul_comm (T (-(q : ℤ))),mul_assoc,←T_add]
      congr 2
    rw [ht,endpointTrace_monomial,endpointWeight_nonpositive a b _ (by omega),mul_zero]
  have hneg : endpointTrace a b
      (∑ j∈P.support, T (-(q : ℤ))*invert
        (LaurentPolynomial.C (P.coeff j)*T (j : ℤ)))=0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [map_mul,invert_C,invert_T]
    have ht : (T (-(q : ℤ)) : ℚ[T;T⁻¹])*
        (LaurentPolynomial.C (P.coeff j)*T (-(j : ℤ)))=
          LaurentPolynomial.C (P.coeff j)*T (-((j : ℤ)+q)) := by
      rw [mul_comm (T (-(q : ℤ))),mul_assoc,←T_add]
      congr 2
      omega
    rw [ht,endpointTrace_monomial,endpointWeight_nonpositive a b _ (by omega),mul_zero]
  rw [hpos,hneg,add_zero]

theorem polynomial_eval_support (P : ℚ[X]) (z : ℚ) :
    P.eval z=∑ j∈P.support, P.coeff j*z^j := by
  have he := congrArg (fun Q : ℚ[X] => Q.eval z) (sum_C_mul_X_pow_eq P)
  simpa only [Polynomial.sum_def,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] using he.symm

/-- The reflected degree-N band contributes to both literal rational poles. -/
theorem endpointTrace_shift_positive (q : ℕ) (P : ℚ[X])
    (hP : P.natDegree<q) (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    endpointTrace a b (T (q : ℤ)*(P.toLaurent+invert P.toLaurent))=
      -2*b^q*(P.eval b+P.eval b⁻¹)-a^q*(P.eval a+P.eval a⁻¹) := by
  rw [original_laurent_expansion,map_sum,mul_add,Finset.mul_sum,Finset.mul_sum,map_add,
    map_sum,map_sum,polynomial_eval_support P b,polynomial_eval_support P b⁻¹,
    polynomial_eval_support P a,polynomial_eval_support P a⁻¹,
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib,
    Finset.mul_sum,Finset.mul_sum,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjq : j<q := (le_natDegree_of_mem_supp j hj).trans_lt hP
  have ht : (T (q : ℤ) : ℚ[T;T⁻¹])*(LaurentPolynomial.C (P.coeff j)*T (j : ℤ))=
      LaurentPolynomial.C (P.coeff j)*T ((q+j : ℕ) : ℤ) := by
    rw [mul_comm (T (q : ℤ)),mul_assoc,←T_add]
    congr 2
    omega
  have hi : (T (q : ℤ) : ℚ[T;T⁻¹])*invert
      (LaurentPolynomial.C (P.coeff j)*T (j : ℤ))=
        LaurentPolynomial.C (P.coeff j)*T ((q-j : ℕ) : ℤ) := by
    simp only [map_mul,invert_C,invert_T]
    rw [mul_comm (T (q : ℤ)),mul_assoc,←T_add]
    congr 2
    omega
  rw [ht,hi,endpointTrace_monomial,endpointTrace_monomial,endpointWeight_nat,
    endpointWeight_nat,if_neg (by omega : q+j≠0),if_neg (by omega : q-j≠0),
    pow_add,pow_add,pow_sub₀ b hb (by omega),pow_sub₀ a ha (by omega),←inv_pow,←inv_pow]
  ring

open WPActualRankTwoHatLift WPActualRankTwoLegendreField
  ActualEntropyPolynomial ActualEntropyLogAttachment ActualEntropyFifth

noncomputable def actualAendQ (p : ℕ) : ℚ :=
  2*(movingEvenQ p).eval 4-(movingEvenQ p).eval (1/4)-
    rationalHarmonic ((p-1)/2)/2-3*literalFifthConstantQ p

noncomputable def actualDendQ (p : ℕ) : ℚ :=
  (movingEvenQ p).eval (1/4)-(movingEvenQ p).eval 4

theorem movingEvenQ_endpoint_one (p : ℕ) :
    (movingEvenQ p).eval 1=rationalHarmonic ((p-1)/2)/2 := by
  exact ActualWeightedF0Carry.movingEvenQ_endpoint_one p

theorem movingComparisonQ_endpoints (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (movingComparisonQ p).eval 0=literalFifthConstantQ p ∧
    (movingComparisonQ p).eval (1/4)=
      rationalHarmonic ((p-1)/2)/2-(movingEvenQ p).eval (1/4) ∧
    (movingComparisonQ p).eval 4=
      (movingEvenQ p).eval 4-rationalHarmonic ((p-1)/2)/2 := by
  have hE : ActualJointGreen.finiteEvenSquaredQ p=movingEvenQ p := by
    rw [ActualJointGreen.finiteEvenSquaredQ,
      ActualJointGreen.finiteEvenLogQ_eq_actual p hp,
      ←movingEvenQ_eq_actual_contract p hp]
  simp only [movingComparisonQ,hE,comparisonCoordinateQ,eval_sub,eval_comp,
    eval_mul,eval_C,eval_add,eval_X,eval_one,eval_ofNat]
  norm_num only
  rw [movingEvenQ_endpoint_one]
  exact ⟨rfl,rfl,rfl⟩

theorem comparison_unshifted_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    endpointTrace (1/4 : ℚ) 4
      ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)=
        -actualAendQ p := by
  rw [map_add,endpointTrace_polynomial,endpointTrace_inverted_polynomial,
    coeff_zero_eq_eval_zero]
  obtain ⟨h0,ha,hb⟩ := movingComparisonQ_endpoints p hp
  rw [h0,ha,hb]
  unfold actualAendQ
  ring

theorem comparison_positive_phase_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    endpointTrace (1/4 : ℚ) 4
      (T (p : ℤ)*((movingComparisonQ p).toLaurent+
        invert (movingComparisonQ p).toLaurent))=
      ((1/4 : ℚ)^p+2*4^p)*actualDendQ p := by
  rw [endpointTrace_shift_positive p _
    ((movingComparisonQ_degree p hp).trans_lt (by omega)) _ _
      (by norm_num) (by norm_num)]
  norm_num only [inv_div,inv_one,one_mul]
  obtain ⟨_,ha,hb⟩ := movingComparisonQ_endpoints p hp
  rw [ha,hb]
  unfold actualDendQ
  ring

theorem comparison_negative_phase_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    endpointTrace (1/4 : ℚ) 4
      (T (-(p : ℤ))*((movingComparisonQ p).toLaurent+
        invert (movingComparisonQ p).toLaurent))=0 :=
  endpointTrace_shift_nonpositive p _
    ((movingComparisonQ_degree p hp).trans (by omega)) _ _

theorem endpointTrace_constant (a b d : ℚ) :
    endpointTrace a b (LaurentPolynomial.C d)=0 := by
  have he : LaurentPolynomial.C d=LaurentPolynomial.C d*T 0 := by simp
  rw [he,endpointTrace_monomial,endpointWeight_nonpositive a b 0 (by omega),mul_zero]

/-- Exact first two rational phases of the original comparison, before reduction. -/
theorem comparison_frobenius_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    seriesWeightedTrace (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4))
      (comparisonRational p hp)=
      -((17-4*((1/4 : ℚ)^p+4^p-(11/4 : ℚ)^p))*actualAendQ p+
        4*((1/4 : ℚ)^p+2*4^p)*actualDendQ p)/15 := by
  rw [frobeniusTrace_full_source p (p+(p-1)/2) (by omega) (by omega) (by omega)
    _ _ _ _ (comparisonRational_support_upper p hp),rationalDlogQ_endpoint,
    rationalDlogQ_endpoint,comparisonRational_full_form p hp]
  have ht : (T (-(p : ℤ)) : ℚ[T;T⁻¹])*T (p : ℤ)=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  have hn : (T (-(p : ℤ)) : ℚ[T;T⁻¹])*T (-(p : ℤ))=T (-(2*(p : ℤ))) := by
    rw [←T_add]
    congr 1
    ring
  have h2n := endpointTrace_shift_nonpositive (2*p) (movingComparisonQ p)
    ((movingComparisonQ_degree p hp).trans (by omega)) (1/4 : ℚ) 4
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h2n
  have hc : endpointTrace (1/4 : ℚ) 4
      (T (-(p : ℤ))*LaurentPolynomial.C (comparisonBranchQ p))=0 := by
    rw [mul_comm,endpointTrace_monomial,
      endpointWeight_nonpositive (1/4 : ℚ) 4 _ (by omega),mul_zero]
  have hshift : (T (-(p : ℤ)) : ℚ[T;T⁻¹])*
      (LaurentPolynomial.C (17/15 : ℚ)*T 0*
          ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)-
        LaurentPolynomial.C (4/15 : ℚ)*T (p : ℤ)*
          ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)-
        LaurentPolynomial.C (4/15 : ℚ)*T (-(p : ℤ))*
          ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)+
        LaurentPolynomial.C (comparisonBranchQ p))=
      LaurentPolynomial.C (17/15 : ℚ)*(T (-(p : ℤ))*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent))-
      LaurentPolynomial.C (4/15 : ℚ)*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)-
      LaurentPolynomial.C (4/15 : ℚ)*(T (-(2*(p : ℤ)))*
        ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent))+
      T (-(p : ℤ))*LaurentPolynomial.C (comparisonBranchQ p) := by
    simp only [T_zero,mul_one]
    linear_combination -LaurentPolynomial.C (4/15 : ℚ)*
      ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)*ht-
      LaurentPolynomial.C (4/15 : ℚ)*
      ((movingComparisonQ p).toLaurent+invert (movingComparisonQ p).toLaurent)*hn
  rw [hshift]
  simp only [map_add,map_sub,mul_assoc,endpointTrace_C_mul,T_zero,one_mul,
    comparison_unshifted_trace p hp,comparison_positive_phase_trace p hp,
    comparison_negative_phase_trace p hp,h2n,hc,endpointTrace_constant,mul_zero,
    zero_sub,sub_zero,add_zero]
  ring

end WPFieldAssembly.ActualComparisonFrobenius
