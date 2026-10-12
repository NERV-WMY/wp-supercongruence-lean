import WPFieldAssembly.SourceClosureVbalJHighElimination
import WPFieldAssembly.SourceClosureUVWeightedK0
import WPFieldAssembly.SourceClosureOriginalJTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteJSource WPFiniteJNormalization
  WPFiniteJHighCoefficient WPFiniteFifthSourceContraction WPFiniteABSourceTail
  WPFiniteWSource WPFiniteZSource WPFiniteJCarrier WPFiniteJWeightedResidue
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWeightedK0
  WPFieldAssembly.SourceClosureOriginalJTransport
  WPFieldAssembly.SourceClosureVbalJHighElimination

namespace WPFieldAssembly.SourceClosureVbalJWeightedTrace

set_option maxHeartbeats 1800000

/-- The complete J carrier shares the original quadratic factor with K0. -/
theorem actual_GJ_originalK0_factor (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (GJ p : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (2*epsilon p/45 : ZMod p)*
        (originalK0 p*((HJP p).toLaurent+invert (HJP p).toLaurent)) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h45 : (45 : ZMod p)≠0 := by
    rw [show (45 : ZMod p)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have heps : (epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  have h17 : (LaurentPolynomial.C (2*epsilon p/45 : ZMod p)*
      LaurentPolynomial.C (17/(2*epsilon p) : ZMod p) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1/45 : ZMod p)*17 := by
    change LaurentPolynomial.C (2*epsilon p/45 : ZMod p)*
      LaurentPolynomial.C (17/(2*epsilon p) : ZMod p)=
        LaurentPolynomial.C (1/45 : ZMod p)*LaurentPolynomial.C (17 : ZMod p)
    rw [←map_mul,←map_mul]
    congr 1
    field_simp [h2,h45,heps]
  have h4 : (LaurentPolynomial.C (2*epsilon p/45 : ZMod p)*
      LaurentPolynomial.C (2/epsilon p : ZMod p) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1/45 : ZMod p)*4 := by
    change LaurentPolynomial.C (2*epsilon p/45 : ZMod p)*
      LaurentPolynomial.C (2/epsilon p : ZMod p)=
        LaurentPolynomial.C (1/45 : ZMod p)*LaurentPolynomial.C (4 : ZMod p)
    rw [←map_mul,←map_mul]
    congr 1
    field_simp [h45,heps]
    ring
  rw [GJ_phase]
  simp only [originalK0,phase]
  linear_combination -((HJP p).toLaurent+invert (HJP p).toLaurent)*h17+
    (T (p : ℤ)+T (-(p : ℤ)))*((HJP p).toLaurent+invert (HJP p).toLaurent)*h4

/-- The SAME original field trace cancels the full J weight, without a support truncation. -/
theorem actual_original_weighted_GJ_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (GJ p)=infinityQ (canceledJ p : (ZMod p)[T;T⁻¹]) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := by
    rw [show (15 : ZMod p)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h45 : (45 : ZMod p)≠0 := by
    rw [show (45 : ZMod p)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have heps : (epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  rw [actual_GJ_originalK0_factor p hp,weighted_C_mul,originalK0_weight_source p hp,
    ←infinityQ_endpoint,canceledJ,infinityQ_C_mul]
  have hscale : (2*epsilon p/45 : ZMod p)*(3/(2*epsilon p))=1/15 := by
    field_simp [h2,h15,h45,heps]
    ring
  rw [←mul_assoc,hscale]
  simp only [map_ofNat]

/-- JT3 keeps the actual 2p coefficient and the whole third positive J band. -/
theorem actual_original_normalized_GJ_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p (GJ p)-
      (207/4 : ZMod p)*(GJ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ))=
        JfullFunctional p := by
  rw [actual_original_weighted_GJ_source p hp]
  calc
    _ = (2 : ZMod p)*infinityQ (canceledJ p)/3-
      207*(GJ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ))/4 := by ring
    _ = _ := actual_full_J_functional p hp

variable {K L : Type*} [Field K] [Field L]

theorem actual_J_full_functional_transport (f : K →+* L) (p : ℕ) :
    f (JfullFunctional p : K)=(JfullFunctional p : L) := by
  have hH := original_HJP_transport f p
  have hs : (strictHigh p : K[X]).map f=(strictHigh p : L[X]) := by
    unfold strictHigh highBand
    simp only [Polynomial.map_sub,Polynomial.map_sum,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X]
    have hc (j : ℕ) : f ((HJP p : K[X]).coeff j)=(HJP p : L[X]).coeff j := by
      rw [←Polynomial.coeff_map,hH]
    simp only [hc]
  have h0 : f ((HJP p : K[X]).eval 0)=(HJP p : L[X]).eval 0 := by
    rw [←coeff_zero_eq_eval_zero,←coeff_zero_eq_eval_zero,←Polynomial.coeff_map,hH]
  have hc : f ((HJP p : K[X]).coeff p)=(HJP p : L[X]).coeff p := by
    rw [←Polynomial.coeff_map,hH]
  have he (x : K) : f ((strictHigh p : K[X]).eval x)=
      (strictHigh p : L[X]).eval (f x) := by
    rw [←eval_map_apply,hs]
  unfold JfullFunctional JendpointFunctional
  simp only [map_add,map_neg,map_mul,map_div₀,map_ofNat,h0,hc,he,map_one]

/-- The original normalized GJ source is evaluated in the SAME fifth field alphabet. -/
theorem actual_original_normalized_GJ_fifth (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f ((2/3 : ZMod p)*originalWeightedFieldTrace p (GJ p)-
      (207/4 : ZMod p)*(GJ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ)))=
      11*U_J p u/15-22*V_J p u/15-
        6*(4*WPFiniteNC122.q p/15-r p/5)^2+3*uSlot p u^2+
        8*(2*(JdifferenceP p (W p)).eval (1/4)+
          (JdifferenceP p (W p)).eval 4)/(15*epsilon p) := by
  rw [actual_original_normalized_GJ_trace p hp,actual_J_full_functional_transport,
    actual_J_closed_fifth_functional p hp u hu]

end WPFieldAssembly.SourceClosureVbalJWeightedTrace
