import WPFieldAssembly.SourceClosureUVWeightedContraction
import WPFieldAssembly.ActualKwFiniteHBridge
import WPFieldAssembly.ActualSigmaNormCarrySource
import WPFinitePrimitiveTransport

open scoped Polynomial LaurentPolynomial BigOperators
open LaurentPolynomial WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.ActualKwPhaseTrace WPFieldAssembly.ActualKwFiniteHBridge
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedBands
  WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWeightedContraction
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.ActualUVSourceIdentification

namespace WPFieldAssembly.SourceClosureUVProductWeight

open WPFiniteLaurentDifferential

set_option maxHeartbeats 1800000

theorem endpointTrace_above_zero {K : Type*} [Field K] (a b : K)
    (F : K[T;T⁻¹]) (hF : Above F 0) : endpointTrace a b F=0 := by
  have hs : (∑ n∈F.coeff.support, LaurentPolynomial.C (F.coeff n)*T n)=F := by
    simpa only [Finsupp.sum,single_eq_C_mul_T] using
      AddMonoidAlgebra.sum_coeff_single F
  rw [←hs,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hn0 : n≤0 := by
    by_contra he
    exact (Finsupp.mem_support_iff.mp hn) (hF n (by omega))
  rw [endpointTrace_monomial,endpointWeight_nonpositive a b n hn0,mul_zero]

/-- The origin coefficient is present until the actual zero-origin specialization. -/
theorem original_weight_low_symmetric (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (P : (ZMod p)[X]) (hP : P.natDegree<p) :
    originalWeightedFieldTrace p (P.toLaurent+invert P.toLaurent) =
      3*(2*P.eval 4+P.eval (1/4)-3*P.coeff 0) := by
  have hS : Above (P.toLaurent+invert P.toLaurent) (P.natDegree : ℤ) := by
    have hh := Above_add (Above_toLaurent P P.natDegree (le_refl _))
      (Above_invert_toLaurent P)
    simpa only [max_eq_left (by omega : (0 : ℤ)≤P.natDegree)] using hh
  have hshift : Above (T (-(p : ℤ))*(P.toLaurent+invert P.toLaurent)) 0 := by
    have hh := Above_mul
      (show Above (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) (-(p : ℤ)) by
        simpa only [map_one,one_mul] using Above_monomial (1 : ZMod p) (-(p : ℤ))) hS
    exact Above_mono hh (by omega)
  rw [original_weight_above p hp _ (Above_mono hS (by omega)),
    endpointTrace_above_zero (1/4 : ZMod p) 4 _ hshift,mul_zero,sub_zero,
    map_add,endpointTrace_polynomial,endpointTrace_inverted_polynomial]
  ring

/- UW18b uses the entire finite logarithm and the actual polynomial W.
   The second positive window and the finite-H diagonal are retained. -/

noncomputable def windowEquation (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) : Prop :=
  originalWeightedFieldTrace p F =
    -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 F -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*F)

theorem windowEquation_add (p : ℕ) [Fact p.Prime]
    (F G : (ZMod p)[T;T⁻¹]) (hF : windowEquation p F)
    (hG : windowEquation p G) : windowEquation p (F+G) := by
  unfold windowEquation at *
  rw [weighted_add,mul_add,map_add,map_add,hF,hG]
  ring

theorem windowEquation_sum (p : ℕ) [Fact p.Prime] {ι : Type*}
    (I : Finset ι) (F : ι → (ZMod p)[T;T⁻¹])
    (hF : ∀ i∈I, windowEquation p (F i)) : windowEquation p (∑ i∈I, F i) := by
  unfold windowEquation at *
  simp only [originalWeightedFieldTrace,Finset.mul_sum,map_sum,
    Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact hF i hi

/-- Both signs of the source and every logarithm index satisfy the same whole weight row. -/
theorem original_weight_full_log_product (p N : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hN : N<p) (e : ℕ → ZMod p) (z : ZMod p)
    (s : ℤ) (hs : s≤1) :
    originalWeightedFieldTrace p
      ((finiteSource N e+invert (finiteSource N e))*
        (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (z^j/(j : ZMod p))*T (s*(j : ℤ)))) =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*
          (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (z^j/(j : ZMod p))*T (s*(j : ℤ)))) -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (T (-(p : ℤ))*((finiteSource N e+invert (finiteSource N e))*
          (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (z^j/(j : ZMod p))*T (s*(j : ℤ))))) := by
  change windowEquation p _
  have hmono (t : ℤ) (ht : t < 2 * (p : ℤ)) (c : ZMod p) :
      windowEquation p (LaurentPolynomial.C c * T t) := by
    unfold windowEquation
    rw [show (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) *
        (LaurentPolynomial.C c * T t) = LaurentPolynomial.C c * T (t - p) by
      rw [mul_left_comm, ←T_add,
        show -(p : ℤ) + t = t - (p : ℤ) by omega]]
    exact original_weight_monomial p hp t ht c
  rw [add_mul]
  apply windowEquation_add
  · rw [finiteSource,Finset.sum_mul]
    apply windowEquation_sum
    intro n hn
    rw [Finset.mul_sum]
    apply windowEquation_sum
    intro j hj
    have ht : (LaurentPolynomial.C (e n)*T (n : ℤ) : (ZMod p)[T;T⁻¹])*
        (LaurentPolynomial.C (z^j/(j : ZMod p))*T (s*(j : ℤ))) =
          LaurentPolynomial.C (e n*(z^j/(j : ZMod p)))*T ((n : ℤ)+s*(j : ℤ)) := by
      rw [map_mul,T_add]
      ring
    rw [ht]
    apply hmono
    have hnN : n≤N := by have := Finset.mem_range.mp hn; omega
    have hj' := Finset.mem_Ico.mp hj
    have hsj : s*(j : ℤ)≤(j : ℤ) := by nlinarith
    omega
  · rw [finiteSource,map_sum,Finset.sum_mul]
    apply windowEquation_sum
    intro n hn
    simp only [map_mul,invert_C,invert_T]
    rw [Finset.mul_sum]
    apply windowEquation_sum
    intro j hj
    have ht : (LaurentPolynomial.C (e n)*T (-(n : ℤ)) : (ZMod p)[T;T⁻¹])*
        (LaurentPolynomial.C (z^j/(j : ZMod p))*T (s*(j : ℤ))) =
          LaurentPolynomial.C (e n*(z^j/(j : ZMod p)))*T (-(n : ℤ)+s*(j : ℤ)) := by
      rw [map_mul,T_add]
      ring
    rw [ht]
    apply hmono
    have hj' := Finset.mem_Ico.mp hj
    have hsj : s*(j : ℤ)≤(j : ℤ) := by nlinarith
    omega

theorem original_weight_positiveLog_source (p N : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hN : N<p) (e : ℕ → ZMod p) (z : ZMod p) :
    originalWeightedFieldTrace p
      ((finiteSource N e+invert (finiteSource N e))*positiveLog p z) =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*positiveLog p z) -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (T (-(p : ℤ))*((finiteSource N e+invert (finiteSource N e))*positiveLog p z)) := by
  simpa only [one_mul,positiveLog] using
    original_weight_full_log_product p N hp hN e z 1 (by omega)

theorem original_weight_negativeLog_source (p N : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hN : N<p) (e : ℕ → ZMod p) (z : ZMod p) :
    originalWeightedFieldTrace p
      ((finiteSource N e+invert (finiteSource N e))*negativeLog p z) =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*negativeLog p z) := by
  have hw := original_weight_full_log_product p N hp hN e z (-1) (by omega)
  simp only [neg_one_mul,negativeLog] at hw ⊢
  rw [show (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*
      ((finiteSource N e+invert (finiteSource N e))*
        (∑ j∈Finset.Ico 1 p, LaurentPolynomial.C (z^j/(j : ZMod p))*T (-(j : ℤ)))) =
      T (-(p : ℤ))*(finiteSource N e+invert (finiteSource N e))*negativeLog p z by
        simp only [negativeLog,mul_assoc],
    shifted_source_negativeLog_trace_zero p N p (by omega),mul_zero,sub_zero] at hw
  exact hw

theorem shifted_positiveLog_reflection (p : ℕ) [Fact p.Prime]
    (z : ZMod p) (hz : z≠0) :
    T (-(p : ℤ))*positiveLog p z=
      LaurentPolynomial.C (-z)*negativeLog p z⁻¹ := by
  have hr := frobenius_negativeLog_reflection p z⁻¹ (inv_ne_zero hz)
  rw [inv_inv] at hr
  have hc : (LaurentPolynomial.C (-z) : (ZMod p)[T;T⁻¹])*
      LaurentPolynomial.C (-z⁻¹)=1 := by
    rw [←map_mul,neg_mul_neg,mul_inv_cancel₀ hz,map_one]
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*T (p : ℤ)=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  calc
    _ = (LaurentPolynomial.C (-z)*T (-(p : ℤ)))*
        (LaurentPolynomial.C (-z⁻¹)*positiveLog p z) := by
      linear_combination -(T (-(p : ℤ))*positiveLog p z)*hc
    _ = (LaurentPolynomial.C (-z)*T (-(p : ℤ)))*
        (T (p : ℤ)*negativeLog p z⁻¹) := by rw [hr]
    _ = _ := by
      linear_combination LaurentPolynomial.C (-z)*negativeLog p z⁻¹*ht

theorem normEntropyField_positive (p : ℕ) [Fact p.Prime] :
    normEntropyField p =
      (T (-(p : ℤ))-4)*positiveLog p (1/4)+
        (T (-(p : ℤ))-LaurentPolynomial.C (1/4 : ZMod p))*positiveLog p 4 := by
  have h (z : ZMod p) : scaledLog p z=positiveLog p z := scaledLog_full p z
  change (T (-(p : ℤ))-4)*scaledLog p (1/4)+
    (T (-(p : ℤ))-LaurentPolynomial.C (1/4 : ZMod p))*scaledLog p 4=_
  rw [h,h]

theorem normEntropyField_reflected (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    normEntropyField p =
      -LaurentPolynomial.C (1/4 : ZMod p)*negativeLog p 4-
        LaurentPolynomial.C (4 : ZMod p)*negativeLog p (1/4)-
          LaurentPolynomial.C (4 : ZMod p)*positiveLog p (1/4)-
            LaurentPolynomial.C (1/4 : ZMod p)*positiveLog p 4 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  rw [normEntropyField_positive,sub_mul,sub_mul,
    shifted_positiveLog_reflection p (1/4) (one_div_ne_zero h4),
    shifted_positiveLog_reflection p 4 h4]
  simp only [map_neg,one_div,inv_inv,map_ofNat]
  ring

theorem normEntropyField_full_weight (p N : ℕ) [Fact p.Prime]
    (hp : 19≤p) (hN : N<p) (e : ℕ → ZMod p) :
    originalWeightedFieldTrace p
      (normEntropyField p*(finiteSource N e+invert (finiteSource N e))) =
      (15/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*negativeLog p (1/4)) -
      (15/4 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*negativeLog p 4) +
      12*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*positiveLog p (1/4)) +
      (3/4 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        ((finiteSource N e+invert (finiteSource N e))*positiveLog p 4) := by
  let S := finiteSource N e+invert (finiteSource N e)
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hshift (z : ZMod p) (hz : z≠0) :
      endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*(S*positiveLog p z)) =
        -z*endpointTrace (1/4 : ZMod p) 4 (S*negativeLog p z⁻¹) := by
    rw [show (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*(S*positiveLog p z)=
        LaurentPolynomial.C (-z)*(S*negativeLog p z⁻¹) by
          rw [mul_left_comm,shifted_positiveLog_reflection p z hz]
          ring,
      endpointTrace_C_mul]
  have hneg (z : ZMod p) := original_weight_negativeLog_source p N hp hN e z
  have hpos (z : ZMod p) := original_weight_positiveLog_source p N hp hN e z
  change originalWeightedFieldTrace p (normEntropyField p*S)=_
  rw [normEntropyField_reflected p hp]
  rw [show (-LaurentPolynomial.C (1/4 : ZMod p)*negativeLog p 4-
      LaurentPolynomial.C (4 : ZMod p)*negativeLog p (1/4)-
        LaurentPolynomial.C (4 : ZMod p)*positiveLog p (1/4)-
          LaurentPolynomial.C (1/4 : ZMod p)*positiveLog p 4)*S =
      LaurentPolynomial.C (-(1/4 : ZMod p))*(S*negativeLog p 4)-
        LaurentPolynomial.C (4 : ZMod p)*(S*negativeLog p (1/4))-
          LaurentPolynomial.C (4 : ZMod p)*(S*positiveLog p (1/4))-
            LaurentPolynomial.C (1/4 : ZMod p)*(S*positiveLog p 4) by
              rw [map_neg]
              ring,
    weighted_sub,weighted_sub,weighted_sub,
    weighted_C_mul,weighted_C_mul,weighted_C_mul,weighted_C_mul,hneg,hneg,hpos,hpos]
  rw [hshift (1/4) (one_div_ne_zero h4),hshift 4 h4]
  simp only [one_div,inv_inv,S,mul_comm]
  field_simp [h4,h2]
  ring

/-- The finite triangles are the original W primitives, including y=0. -/
theorem finiteH_originalW (p : ℕ) [Fact p.Prime] (hp : 19≤p) (y v : ZMod p) :
    finiteH ((p-1)/2) (fun n => (WPFiniteWSource.W p : (ZMod p)[X]).coeff n) y v =
      (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) y).eval v := by
  have hN : (p-1)/2<p := by omega
  have hW : (WPFiniteWSource.W p : (ZMod p)[X]).natDegree≤(p-1)/2 :=
    (WPFiniteWSource.W_degree p hp).trans (by omega)
  have hQ := WPFinitePrimitiveTransport.unitPrimitiveP_unique p (WPFiniteWSource.W p)
    (hW.trans_lt hN) (WPFiniteWSource.W_origin p) y
    (HPrimitive ((p-1)/2) (fun n => (WPFiniteWSource.W p).coeff n) y)
    ((HPrimitive_degree _ _ _).trans_lt hN) (HPrimitive_eval_zero _ _ _)
    (HPrimitive_polynomial_derivative p ((p-1)/2) hN _ hW y)
  rw [←HPrimitive_eval,hQ]

theorem sourceValue_originalW (p : ℕ) [Fact p.Prime] (hp : 19≤p) (y : ZMod p) :
    sourceValue ((p-1)/2) (fun n => (WPFiniteWSource.W p : (ZMod p)[X]).coeff n) y =
      (WPFiniteWSource.W p).eval y := by
  have hs := congrArg (fun Q : (ZMod p)[X] => Q.eval y)
    (sourcePolynomial_eq ((p-1)/2) (WPFiniteWSource.W p)
      ((WPFiniteWSource.W_degree p hp).trans (by omega)))
  simpa only [sourcePolynomial,sourceValue,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] using hs

/-- UW18b for the original whole source, after exact cutoff reflection. -/
theorem original_entropy_W_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p
      (normEntropyField p*((WPFiniteWSource.W p).toLaurent+
        invert (WPFiniteWSource.W p).toLaurent)) =
      -(3/4 : ZMod p)*WPFiniteField.ell p (16 : ZMod p)*
        ((WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4) +
      (33/2 : ZMod p)*(originalHa p).eval (1/4)+
      (21/4 : ZMod p)*(originalHa p).eval 4-
      3*(originalHb p).eval (1/4)+(33/4 : ZMod p)*(originalHb p).eval 4+
      (45/2 : ZMod p)*(originalHx p).eval (1/4)-(45/4 : ZMod p)*(originalHx p).eval 4 := by
  let e : ℕ → ZMod p := fun n => (WPFiniteWSource.W p).coeff n
  have hN : (p-1)/2<p := by omega
  have hW := finiteSource_polynomial ((p-1)/2) (WPFiniteWSource.W p : (ZMod p)[X])
    ((WPFiniteWSource.W_degree p hp).trans (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4*4 by ring]
    exact mul_ne_zero h4 h4
  have hlog (z : ZMod p) : finiteLogValue p z=WPFiniteField.ell p z := rfl
  have he := normEntropyField_full_weight p ((p-1)/2) hp hN e
  rw [full_source_negativeLog_trace p ((p-1)/2) hN,
    full_source_negativeLog_trace p ((p-1)/2) hN,
    full_source_positiveLog_trace p ((p-1)/2) hN e (1/4) 4 (1/4)
      (one_div_ne_zero h4) h4,
    full_source_positiveLog_trace p ((p-1)/2) hN e (1/4) 4 4
      (one_div_ne_zero h4) h4] at he
  simp only [e,sourceValue_originalW p hp,finiteH_originalW p hp,hlog,
    show (4 : ZMod p)⁻¹=1/4 by simp only [one_div],
    show (1/4 : ZMod p)⁻¹=4 by simp only [one_div,inv_inv],
    show (4 : ZMod p)*(1/4)=1 by field_simp [h4],
    show (1/4 : ZMod p)*(1/4)=1/16 by field_simp [h4,h16]; ring,
    show (1/4 : ZMod p)*4=1 by field_simp [h4],
    show (4 : ZMod p)*4=16 by ring] at he
  have hreal := original_real_log_ends p hp
  change WPFiniteField.ell p (1 : ZMod p)=0 ∧
    WPFiniteField.ell p (1/16 : ZMod p)=-(WPFiniteField.ell p (16 : ZMod p))/16 at hreal
  rw [hreal.1,hreal.2] at he
  rw [hW] at he
  change _ = _ at he
  calc
    _ = _ := he
    _ = _ := by
      unfold originalHa originalHb originalHx
      field_simp [h2,h4,h16]
      ring

end WPFieldAssembly.SourceClosureUVProductWeight
