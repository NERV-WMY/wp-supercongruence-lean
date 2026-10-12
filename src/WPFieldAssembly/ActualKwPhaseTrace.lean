import WPFieldAssembly.ActualKwFirstCarry
import WPFieldAssembly.ActualKwWeightedTrace
import WPFieldAssembly.ActualKwSeriesAttachment

open scoped Polynomial LaurentPolynomial PowerSeries BigOperators
open LaurentPolynomial

namespace WPFieldAssembly.ActualKwPhaseTrace

open ActualKwWeightedTrace

set_option maxHeartbeats 1600000

/- The first two infinity phases act on the complete finite Laurent source.
The source coefficients, branch term and actual comparison identification stay
with their owner. Every finite logarithm index and its diagonal is retained. -/

section Support
variable {K : Type*} [Field K]

theorem finiteSource_polynomial (N : ℕ) (P : K[X]) (hP : P.natDegree≤N) :
    finiteSource N (fun n => P.coeff n)=P.toLaurent := by
  have hsub : P.support ⊆ Finset.range (N+1) := by
    intro n hn
    have hd := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
    exact Finset.mem_range.mpr (by omega)
  have hs := congrArg (fun P : K[X] => P.toLaurent) (Polynomial.sum_C_mul_X_pow_eq P)
  rw [Polynomial.sum_def,map_sum] at hs
  simp only [Polynomial.toLaurent_C_mul_X_pow] at hs
  unfold finiteSource
  calc
    _ = ∑ n∈P.support, C (P.coeff n)*T (n : ℤ) := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hcn : P.coeff n=0 := by
        by_contra hc
        exact hnot (Polynomial.mem_support_iff.mpr hc)
      rw [hcn,map_zero,zero_mul]
    _ = P.toLaurent := hs

theorem negativeLog_trace_nonpositive (p : ℕ) (a b z : K) (n : ℤ) (hn : n≤0) :
    endpointTrace a b (T n*negativeLog p z)=0 := by
  rw [negativeLog,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have ht : (T n : K[T;T⁻¹])*(C (z^j/(j : K))*T (-(j : ℤ)))=
      C (z^j/(j : K))*T (n-(j : ℤ)) := by
    rw [mul_comm (T n),mul_assoc,←T_add]
    congr 2
    omega
  rw [ht,endpointTrace_monomial,endpointWeight_nonpositive a b _ (by omega),mul_zero]

theorem shifted_source_negativeLog_trace_zero (p N q : ℕ) (hN : N≤q)
    (e : ℕ → K) (a b z : K) :
    endpointTrace a b
      (T (-(q : ℤ))*(finiteSource N e+invert (finiteSource N e))*negativeLog p z)=0 := by
  have hpos : endpointTrace a b
      (T (-(q : ℤ))*finiteSource N e*negativeLog p z)=0 := by
    rw [finiteSource,Finset.mul_sum,Finset.sum_mul,map_sum]
    apply Finset.sum_eq_zero
    intro n hn
    have ht : (T (-(q : ℤ)) : K[T;T⁻¹])*(C (e n)*T (n : ℤ))=
        C (e n)*T ((n : ℤ)-q) := by
      rw [mul_comm (T (-(q : ℤ))),mul_assoc,←T_add]
      congr 2
    rw [ht,mul_assoc,endpointTrace_C_mul,negativeLog_trace_nonpositive p a b z _ (by
      have := Finset.mem_range.mp hn
      omega),mul_zero]
  have hneg : endpointTrace a b
      (T (-(q : ℤ))*invert (finiteSource N e)*negativeLog p z)=0 := by
    rw [finiteSource,map_sum,Finset.mul_sum,Finset.sum_mul,map_sum]
    apply Finset.sum_eq_zero
    intro n hn
    simp only [map_mul,invert_C,invert_T]
    have ht : (T (-(q : ℤ)) : K[T;T⁻¹])*(C (e n)*T (-(n : ℤ)))=
        C (e n)*T (-((n : ℤ)+q)) := by
      rw [mul_comm (T (-(q : ℤ))),mul_assoc,←T_add]
      congr 2
      omega
    rw [ht,mul_assoc,endpointTrace_C_mul,
      negativeLog_trace_nonpositive p a b z _ (by omega),mul_zero]
  rw [mul_add,add_mul,map_add,hpos,hneg,add_zero]

theorem logCombination_trace_nonpositive (p : ℕ) (a b x y z u v w : K)
    (n : ℤ) (hn : n≤0) :
    endpointTrace a b (T n*(C u*negativeLog p x+C v*negativeLog p y-C w*negativeLog p z))=0 := by
  calc
    _ = endpointTrace a b
        (C u*(T n*negativeLog p x)+C v*(T n*negativeLog p y)-C w*(T n*negativeLog p z)) := by
      congr 1
      ring
    _ = _ := by
      rw [map_sub,map_add,endpointTrace_C_mul,endpointTrace_C_mul,endpointTrace_C_mul,
        negativeLog_trace_nonpositive p a b x n hn,
        negativeLog_trace_nonpositive p a b y n hn,
        negativeLog_trace_nonpositive p a b z n hn]
      ring

theorem shifted_logCombination_trace_zero (p N q : ℕ) (hN : N≤q)
    (e : ℕ → K) (a b x y z u v w : K) :
    endpointTrace a b
      (T (-(q : ℤ))*(C u*negativeLog p x+C v*negativeLog p y-C w*negativeLog p z)*
        (finiteSource N e+invert (finiteSource N e)))=0 := by
  have hzero (r : K) : endpointTrace a b
      (T (-(q : ℤ))*negativeLog p r*(finiteSource N e+invert (finiteSource N e)))=0 := by
    convert shifted_source_negativeLog_trace_zero p N q hN e a b r using 1
    congr 1
    ring
  calc
    _ = endpointTrace a b
        (C u*(T (-(q : ℤ))*negativeLog p x*(finiteSource N e+invert (finiteSource N e)))+
          C v*(T (-(q : ℤ))*negativeLog p y*(finiteSource N e+invert (finiteSource N e)))-
            C w*(T (-(q : ℤ))*negativeLog p z*(finiteSource N e+invert (finiteSource N e)))) := by
      congr 1
      ring
    _ = _ := by
      rw [map_sub,map_add,endpointTrace_C_mul,endpointTrace_C_mul,endpointTrace_C_mul,
        hzero,hzero,hzero]
      ring

end Support

theorem frobenius_negativeLog_reflection (p : ℕ) [Fact p.Prime]
    (z : ZMod p) (hz : z≠0) :
    T (p : ℤ)*negativeLog p z=C (-z)*positiveLog p z⁻¹ := by
  rw [negativeLog,positiveLog,Finset.mul_sum,Finset.mul_sum]
  rw [←WPFiniteInversion.full_cutoff_reflection p
    (fun j => (T (p : ℤ) : (ZMod p)[T;T⁻¹])*
      (C (z^j/(j : ZMod p))*T (-(j : ℤ))))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j≤p := Nat.le_of_lt (Finset.mem_Ico.mp hj).2
  have hzj : z^j*z⁻¹^j=1 := by
    rw [←mul_pow,mul_inv_cancel₀ hz,one_pow]
  have hpow : z^(p-j)=z*z⁻¹^j := by
    calc
      _ = z^(p-j)*(z^j*z⁻¹^j) := by rw [hzj,mul_one]
      _ = z^p*z⁻¹^j := by rw [←mul_assoc,←pow_add,Nat.sub_add_cancel hjp]
      _ = _ := by rw [ZMod.pow_card]
  have hc : z^(p-j)/((p-j : ℕ) : ZMod p)=(-z)*(z⁻¹^j/(j : ZMod p)) := by
    rw [hpow,WPFiniteInversion.reflected_denominator p j hj]
    ring
  have ht : -((p-j : ℕ) : ℤ)+(p : ℤ)=(j : ℤ) := by omega
  rw [mul_comm (T (p : ℤ)),mul_assoc,←T_add]
  rw [ht,hc,map_mul]
  ring

noncomputable def firstLog (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  negativeLog p (1/4)+negativeLog p 4-negativeLog p (11/4)

noncomputable def phaseLog (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  C (7/4 : ZMod p)*negativeLog p (1/4)+C (11/2 : ZMod p)*negativeLog p 4-
    C (17/4 : ZMod p)*negativeLog p (11/4)

noncomputable def literalF1Laurent (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  firstLog p+T (-(p : ℤ))*phaseLog p

theorem firstLog_phase_cancellation (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    17*firstLog p-4*phaseLog p=
      10*negativeLog p (1/4)-5*negativeLog p 4 := by
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h7 : (4 : ZMod p)*(7/4)=7 := by field_simp [h4]
  have h11 : (4 : ZMod p)*(11/2)=22 := by field_simp [h2]; ring
  have h17 : (4 : ZMod p)*(17/4)=17 := by field_simp [h4]
  have h7C : (4 : (ZMod p)[T;T⁻¹])*C (7/4 : ZMod p)=7 := by
    change C (4 : ZMod p)*C (7/4 : ZMod p)=C 7
    rw [←map_mul,h7]
  have h11C : (4 : (ZMod p)[T;T⁻¹])*C (11/2 : ZMod p)=22 := by
    change C (4 : ZMod p)*C (11/2 : ZMod p)=C 22
    rw [←map_mul,h11]
  have h17C : (4 : (ZMod p)[T;T⁻¹])*C (17/4 : ZMod p)=17 := by
    change C (4 : ZMod p)*C (17/4 : ZMod p)=C 17
    rw [←map_mul,h17]
  unfold firstLog phaseLog
  calc
    _ = 17*negativeLog p (1/4)+17*negativeLog p 4-17*negativeLog p (11/4)-
        ((4*C (7/4 : ZMod p))*negativeLog p (1/4)+
          (4*C (11/2 : ZMod p))*negativeLog p 4-
            (4*C (17/4 : ZMod p))*negativeLog p (11/4)) := by ring
    _ = _ := by rw [h7C,h11C,h17C]; ring

noncomputable def fieldCoupling (p B : ℕ) [Fact p.Prime]
    (F : (ZMod p)⟦X⟧) (L : (ZMod p)[T;T⁻¹]) : ZMod p :=
  ∑ r∈Finset.range B, PowerSeries.coeff r F*fieldDlogQ p (T (-(r : ℤ))*L)

theorem fieldDlogQ_shift_full_source_zero (p B r : ℕ) [Fact p.Prime] (hp : 19≤p)
    (I : Finset ℤ) (e : ℤ → ZMod p) (hI : ∀ n∈I, n≤(B : ℤ)) (hr : B≤r) :
    fieldDlogQ p (T (-(r : ℤ))*(∑ n∈I, C (e n)*T n))=0 := by
  rw [fieldDlogQ_endpoint p hp,Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have ht : (T (-(r : ℤ)) : (ZMod p)[T;T⁻¹])*(C (e n)*T n)=
      C (e n)*T (n-(r : ℤ)) := by
    rw [mul_comm (T (-(r : ℤ))),mul_assoc,←T_add]
    congr 2
  rw [ht,endpointTrace_monomial,endpointWeight_nonpositive _ _ _ (by
    have := hI n hn
    omega),mul_zero]

theorem fieldCoupling_add (p B : ℕ) [Fact p.Prime]
    (F G : (ZMod p)⟦X⟧) (L : (ZMod p)[T;T⁻¹]) :
    fieldCoupling p B (F+G) L=fieldCoupling p B F L+fieldCoupling p B G L := by
  simp only [fieldCoupling,map_add,add_mul,Finset.sum_add_distrib]

theorem fieldCoupling_sub (p B : ℕ) [Fact p.Prime]
    (F G : (ZMod p)⟦X⟧) (L : (ZMod p)[T;T⁻¹]) :
    fieldCoupling p B (F-G) L=fieldCoupling p B F L-fieldCoupling p B G L := by
  simp only [fieldCoupling,map_sub,sub_mul,Finset.sum_sub_distrib]

theorem fieldCoupling_C_mul (p B : ℕ) [Fact p.Prime]
    (d : ZMod p) (F : (ZMod p)⟦X⟧) (L : (ZMod p)[T;T⁻¹]) :
    fieldCoupling p B (PowerSeries.C d*F) L=d*fieldCoupling p B F L := by
  simp only [fieldCoupling,PowerSeries.coeff_C_mul,Finset.mul_sum,mul_assoc]

theorem fieldCoupling_sum (p B : ℕ) [Fact p.Prime] {J : Type*}
    (I : Finset J) (F : J → (ZMod p)⟦X⟧) (L : (ZMod p)[T;T⁻¹]) :
    fieldCoupling p B (∑ j∈I, F j) L=∑ j∈I, fieldCoupling p B (F j) L := by
  simp only [fieldCoupling,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem fieldCoupling_C_mul_X_pow (p B k : ℕ) [Fact p.Prime] (hp : 19≤p)
    (d : ZMod p) (I : Finset ℤ) (e : ℤ → ZMod p) (hI : ∀ n∈I, n≤(B : ℤ)) :
    fieldCoupling p B (PowerSeries.C d*PowerSeries.X^k) (∑ n∈I, C (e n)*T n)=
      d*fieldDlogQ p (T (-(k : ℤ))*(∑ n∈I, C (e n)*T n)) := by
  by_cases hk : k<B
  · unfold fieldCoupling
    rw [Finset.sum_eq_single k]
    · simp [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]
    · intro r hr hrk
      simp [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow,hrk]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hk))
  · have hz := fieldDlogQ_shift_full_source_zero p B k hp I e hI (by omega)
    rw [hz,mul_zero]
    unfold fieldCoupling
    apply Finset.sum_eq_zero
    intro r hr
    have hrk : r≠k := by have := Finset.mem_range.mp hr; omega
    simp [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow,hrk]

theorem fieldCoupling_shifted_log (p B q : ℕ) [Fact p.Prime] (hp : 19≤p)
    (a : ZMod p) (I : Finset ℤ) (e : ℤ → ZMod p) (hI : ∀ n∈I, n≤(B : ℤ)) :
    fieldCoupling p B (PowerSeries.X^q*ActualKwFirstCarry.finiteLogSeries p a)
      (∑ n∈I, C (e n)*T n)=
      fieldDlogQ p (T (-(q : ℤ))*negativeLog p a*(∑ n∈I, C (e n)*T n)) := by
  have hlog : (T (-(q : ℤ)) : (ZMod p)[T;T⁻¹])*negativeLog p a=
      ∑ j∈Finset.Ico 1 p, T (-(q : ℤ))*(C (a^j/(j : ZMod p))*T (-(j : ℤ))) := by
    rw [negativeLog,Finset.mul_sum]
  rw [ActualKwFirstCarry.finiteLogSeries,Finset.mul_sum,fieldCoupling_sum,
    hlog,Finset.sum_mul,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hseries : (PowerSeries.X^q : (ZMod p)⟦X⟧)*
      (PowerSeries.C (a^j/(j : ZMod p))*PowerSeries.X^j)=
      PowerSeries.C (a^j/(j : ZMod p))*PowerSeries.X^(q+j) := by
    rw [pow_add]
    ring
  have ht : (T (-(q : ℤ)) : (ZMod p)[T;T⁻¹])*
      (C (a^j/(j : ZMod p))*T (-(j : ℤ)))=
      C (a^j/(j : ZMod p))*T (-((q+j : ℕ) : ℤ)) := by
    rw [mul_comm (T (-(q : ℤ))),mul_assoc,←T_add]
    congr 2
    omega
  rw [hseries,fieldCoupling_C_mul_X_pow p B (q+j) hp _ I e hI,
    ht,mul_assoc,←LaurentPolynomial.smul_eq_C_mul,map_smul,smul_eq_mul]

theorem fieldCoupling_literalF1 (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (I : Finset ℤ) (e : ℤ → ZMod p) (hI : ∀ n∈I, n≤(B : ℤ)) :
    fieldCoupling p B (ActualKwFirstCarry.literalFirstTwoPhases p)
      (∑ n∈I, C (e n)*T n)=
      fieldDlogQ p (literalF1Laurent p*(∑ n∈I, C (e n)*T n)) := by
  have hlog (a : ZMod p) :
      fieldCoupling p B (ActualKwFirstCarry.finiteLogSeries p a)
        (∑ n∈I, C (e n)*T n)=
        fieldDlogQ p (negativeLog p a*(∑ n∈I, C (e n)*T n)) := by
    simpa only [pow_zero,one_mul,T_zero,neg_zero,Nat.cast_zero] using
      fieldCoupling_shifted_log p B 0 hp a I e hI
  have hphase (d a : ZMod p) :
      fieldCoupling p B (PowerSeries.X^p*(PowerSeries.C d*ActualKwFirstCarry.finiteLogSeries p a))
        (∑ n∈I, C (e n)*T n)=
        d*fieldDlogQ p (T (-(p : ℤ))*negativeLog p a*(∑ n∈I, C (e n)*T n)) := by
    have hs : (PowerSeries.X^p : (ZMod p)⟦X⟧)*
        (PowerSeries.C d*ActualKwFirstCarry.finiteLogSeries p a)=
        PowerSeries.C d*(PowerSeries.X^p*ActualKwFirstCarry.finiteLogSeries p a) := by ring
    rw [hs,fieldCoupling_C_mul,fieldCoupling_shifted_log p B p hp a I e hI]
  rw [ActualKwFirstCarry.literalFirstTwoPhases,mul_sub,mul_add,
    fieldCoupling_add,fieldCoupling_sub,fieldCoupling_add,
    fieldCoupling_sub,fieldCoupling_add,hlog,hlog,hlog,hphase,hphase,hphase]
  have hcoeff (d : ZMod p) (M : (ZMod p)[T;T⁻¹]) :
      fieldDlogQ p (T (-(p : ℤ))*(C d*M)*(∑ n∈I, C (e n)*T n))=
        d*fieldDlogQ p (T (-(p : ℤ))*M*(∑ n∈I, C (e n)*T n)) := by
    rw [show (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*(C d*M)*(∑ n∈I, C (e n)*T n)=
        C d*(T (-(p : ℤ))*M*(∑ n∈I, C (e n)*T n)) by ring,
      ←LaurentPolynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
  unfold literalF1Laurent firstLog phaseLog
  simp only [add_mul,sub_mul,mul_add,mul_sub,map_add,map_sub]
  rw [hcoeff,hcoeff,hcoeff]

/-- The canonical integral carry is reduced only after its whole rational difference was divided. -/
theorem actualFiniteCarry_field_full_source (p B : ℕ) [Fact p.Prime] (hp : 19≤p)
    (hB : B≤2*p) (L : (WPPIntegralReduction.integralRationals p)[T;T⁻¹])
    (I : Finset ℤ) (e : ℤ → ZMod p)
    (hL : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) L=
      ∑ n∈I, C (e n)*T n) (hI : ∀ n∈I, n≤(B : ℤ)) :
    WPPIntegralReduction.residueHom p
      (ActualKwSeriesAttachment.actualFiniteCarryIntegral p B hp L)=
        (-3 : ZMod p)*fieldDlogQ p
          (literalF1Laurent p*WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) L) := by
  rw [ActualKwSeriesAttachment.actualFiniteCarryIntegral_field p B hp hB]
  change (-3 : ZMod p)*fieldCoupling p B (ActualKwFirstCarry.literalFirstTwoPhases p)
    (WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) L)=_
  rw [hL,fieldCoupling_literalF1 p B hp I e hI]

theorem literalF1_trace_zero (p : ℕ) [Fact p.Prime] (a b : ZMod p) :
    endpointTrace a b (literalF1Laurent p)=0 := by
  have hfirst : endpointTrace a b (firstLog p)=0 := by
    simpa only [firstLog,map_one,one_mul,T_zero] using
      logCombination_trace_nonpositive p a b (1/4 : ZMod p) 4 (11/4) 1 1 1 0 (by omega)
  have hphase : endpointTrace a b (T (-(p : ℤ))*phaseLog p)=0 :=
    logCombination_trace_nonpositive p a b (1/4 : ZMod p) 4 (11/4)
      (7/4) (11/2) (17/4) (-(p : ℤ)) (by omega)
  rw [literalF1Laurent,map_add,hfirst,hphase,add_zero]

/-- This is an explicit kernel identity; the actual comparison equality is separate. -/
theorem literalF1_kernel_projection (p N : ℕ) [Fact p.Prime] (hp : 19≤p) (hN : N<p)
    (e : ℕ → ZMod p) (d : ZMod p) :
    endpointTrace (1/4 : ZMod p) 4
      (literalF1Laurent p*(C (1/15 : ZMod p)*(17-4*T (p : ℤ)-4*T (-(p : ℤ)))*
        (finiteSource N e+invert (finiteSource N e))+C d))=
      (1/15 : ZMod p)*
        (10*endpointTrace (1/4 : ZMod p) 4
            (negativeLog p (1/4)*(finiteSource N e+invert (finiteSource N e)))-
          5*endpointTrace (1/4 : ZMod p) 4
            (negativeLog p 4*(finiteSource N e+invert (finiteSource N e)))-
          4*endpointTrace (1/4 : ZMod p) 4
            (T (p : ℤ)*firstLog p*(finiteSource N e+invert (finiteSource N e)))) := by
  let S := finiteSource N e+invert (finiteSource N e)
  have hfirst (q : ℕ) (hq : N≤q) :
      endpointTrace (1/4 : ZMod p) 4 (T (-(q : ℤ))*firstLog p*S)=0 := by
    simpa only [firstLog,S,map_one,one_mul] using
      shifted_logCombination_trace_zero p N q hq e (1/4 : ZMod p) 4
        (1/4) 4 (11/4) 1 1 1
  have hphase (q : ℕ) (hq : N≤q) :
      endpointTrace (1/4 : ZMod p) 4 (T (-(q : ℤ))*phaseLog p*S)=0 :=
    shifted_logCombination_trace_zero p N q hq e (1/4 : ZMod p) 4
      (1/4) 4 (11/4) (7/4) (11/2) (17/4)
  have ht : (T (p : ℤ) : (ZMod p)[T;T⁻¹])*T (-(p : ℤ))=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have htt : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*T (-(p : ℤ))=T (-((2*p : ℕ) : ℤ)) := by
    rw [←T_add]
    congr 1
    omega
  change endpointTrace (1/4 : ZMod p) 4
    (literalF1Laurent p*(C (1/15 : ZMod p)*(17-4*T (p : ℤ)-4*T (-(p : ℤ)))*S+C d))=_
  calc
    _ = endpointTrace (1/4 : ZMod p) 4
        (C (1/15 : ZMod p)*
          ((17*firstLog p-4*(T (p : ℤ)*T (-(p : ℤ)))*phaseLog p)*S-
            4*(T (p : ℤ)*firstLog p*S)+17*(T (-(p : ℤ))*phaseLog p*S)-
              4*(T (-(p : ℤ))*firstLog p*S)-
                4*((T (-(p : ℤ))*T (-(p : ℤ)))*phaseLog p*S))+C d*literalF1Laurent p) := by
      congr 1
      unfold literalF1Laurent
      ring
    _ = _ := by
      rw [ht,mul_one,htt,firstLog_phase_cancellation p hp,
        map_add,endpointTrace_C_mul,endpointTrace_C_mul,literalF1_trace_zero,
        map_sub,map_sub,map_add,map_sub]
      have h17 : (17 : (ZMod p)[T;T⁻¹])=C (17 : ZMod p) := rfl
      have h4 : (4 : (ZMod p)[T;T⁻¹])=C (4 : ZMod p) := rfl
      have h10 : (10 : (ZMod p)[T;T⁻¹])=C (10 : ZMod p) := rfl
      have h5 : (5 : (ZMod p)[T;T⁻¹])=C (5 : ZMod p) := rfl
      simp only [sub_mul,map_sub,h17,h4,h10,h5]
      rw [mul_assoc (C (10 : ZMod p)) (negativeLog p (1/4)) S,
        mul_assoc (C (5 : ZMod p)) (negativeLog p 4) S,
        endpointTrace_C_mul,endpointTrace_C_mul,endpointTrace_C_mul,
        endpointTrace_C_mul,endpointTrace_C_mul,endpointTrace_C_mul]
      rw [hphase p (by omega),hfirst p (by omega),hphase (2*p) (by omega)]
      ring

theorem firstLog_positive_reflection_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : (ZMod p)[T;T⁻¹]) :
    endpointTrace (1/4 : ZMod p) 4 (T (p : ℤ)*firstLog p*L)=
      -(1/4 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (positiveLog p (1/4 : ZMod p)⁻¹*L)-
        (4 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (positiveLog p (4 : ZMod p)⁻¹*L)+
          (11/4 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (positiveLog p (11/4 : ZMod p)⁻¹*L) := by
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h11 : (11 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 11
    (Finset.mem_Ico.mpr (by omega))
  rw [firstLog,mul_sub,mul_add,sub_mul,add_mul,map_sub,map_add,
    frobenius_negativeLog_reflection p (1/4) (one_div_ne_zero h4),
    frobenius_negativeLog_reflection p 4 h4,
    frobenius_negativeLog_reflection p (11/4) (div_ne_zero h11 h4),
    mul_assoc,mul_assoc,mul_assoc,endpointTrace_C_mul,endpointTrace_C_mul,endpointTrace_C_mul]
  ring

noncomputable def minusH {K : Type*} [Field K] (N : ℕ) (e : ℕ → K) (a b z : K) : K :=
  -2*finiteH N e b z-finiteH N e a z+3*finiteH N e 0 z

noncomputable def plusH {K : Type*} [Field K] (p N : ℕ) (e : ℕ → K) (a b z : K) : K :=
  -2*(sourceValue N e b+sourceValue N e b⁻¹)*finiteLogValue p (b*z)-
    (sourceValue N e a+sourceValue N e a⁻¹)*finiteLogValue p (a*z)+
      2*finiteH N e b⁻¹ z+finiteH N e a⁻¹ z

/-- The exact first carry contribution, with all finite triangles and their diagonal. -/
theorem literalF1_kernel_weight_two (p N : ℕ) [Fact p.Prime] (hp : 19≤p) (hN : N<p)
    (e : ℕ → ZMod p) (d : ZMod p) :
    (-3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
      (literalF1Laurent p*(C (1/15 : ZMod p)*(17-4*T (p : ℤ)-4*T (-(p : ℤ)))*
        (finiteSource N e+invert (finiteSource N e))+C d))=
      -2*minusH N e (1/4 : ZMod p) 4 (1/4)+minusH N e (1/4 : ZMod p) 4 4-
        (4/5 : ZMod p)*
          ((1/4 : ZMod p)*plusH p N e (1/4 : ZMod p) 4 (1/4 : ZMod p)⁻¹+
            (4 : ZMod p)*plusH p N e (1/4 : ZMod p) 4 (4 : ZMod p)⁻¹-
              (11/4 : ZMod p)*plusH p N e (1/4 : ZMod p) 4 (11/4 : ZMod p)⁻¹) := by
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hminus (z : ZMod p) : endpointTrace (1/4 : ZMod p) 4
      (negativeLog p z*(finiteSource N e+invert (finiteSource N e)))=
      minusH N e (1/4 : ZMod p) 4 z := by
    rw [mul_comm]
    exact full_source_negativeLog_trace p N hN e (1/4 : ZMod p) 4 z
  have hplus (z : ZMod p) : endpointTrace (1/4 : ZMod p) 4
      (positiveLog p z*(finiteSource N e+invert (finiteSource N e)))=
      plusH p N e (1/4 : ZMod p) 4 z := by
    rw [mul_comm]
    exact full_source_positiveLog_trace p N hN e (1/4 : ZMod p) 4 z
      (one_div_ne_zero h4) h4
  rw [literalF1_kernel_projection p N hp hN e d,
    firstLog_positive_reflection_trace p hp,hminus,hminus,hplus,hplus,hplus]
  field_simp [h5,h15]
  ring

end WPFieldAssembly.ActualKwPhaseTrace
