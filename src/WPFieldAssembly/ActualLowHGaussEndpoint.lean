import WPFieldAssembly.ActualLowEuler
import WPFieldAssembly.ActualBpairLowHEuler
import WPFieldAssembly.ActualNativeGaussBeta
import WPFieldAssembly.ActualGaussSecondMoment
import WPFieldAssembly.ActualThreePhase

open scoped BigOperators Polynomial
open Polynomial WPFiniteProductTail WPFinitePrimitiveTransport WPActualNativeHasse
  WPFieldAssembly.ActualBpairContraction WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.ActualR0Node

namespace WPFieldAssembly.ActualGaussHarmonic

variable {K : Type*} [Field K]

set_option maxHeartbeats 2000000

/-- The canonical unit primitive has its entire coefficient expansion before evaluation. -/
theorem lowHEulerJ_coefficient_expansion (p d : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (hd : 1≤d) (hband : 6*d<p) (H : K[X]) (hH : H.natDegree≤d) :
    lowHEulerJ p H=
      ∑ j ∈ Finset.range d,C (H.coeff (j+1))*betaP (K:=K) p j := by
  classical
  let J : K[X] := ∑ j ∈ Finset.range d,C (H.coeff (j+1))*betaP (K:=K) p j
  have hdiv : H.divX.natDegree<d := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hR : lowHEulerR H=
      ∑ j ∈ Finset.range d,C (H.coeff (j+1))*(1-X^2)^j := by
    rw [lowHEulerR,as_sum_range' H.divX d hdiv]
    simp only [←C_mul_X_pow_eq_monomial,coeff_divX,sum_comp,mul_comp,
      C_comp,pow_comp,X_comp]
  have hJ : J.natDegree<p := by
    apply (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt (by omega : p-1<p)
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (betaP_degree p j)
  have hD : J.derivative=lowHEulerR H := by
    rw [hR]
    simp only [J,derivative_sum,derivative_C_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [betaP_derivative p j (by have := Finset.mem_range.mp hj; omega)]
  have h0 : J.eval 0=0 := by
    simp only [J,eval_finsetSum,eval_mul,eval_C,betaP_zero,mul_zero,Finset.sum_const_zero]
  have he : (lowHEulerJ p H-J).derivative=0 := by
    rw [derivative_sub,lowHEulerJ_derivative p hp d hd hband H hH,hD,sub_self]
  have hg : (lowHEulerJ p H-J).natDegree<p :=
    (natDegree_sub_le _ _).trans_lt (max_lt
      ((lowHIntegralP_degree p (lowHEulerR H)).trans_lt (by omega)) hJ)
  have hz : (lowHEulerJ p H-J).eval 0=0 := by
    rw [eval_sub,h0,sub_zero]
    exact lowHIntegralP_zero p (lowHEulerR H)
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hg he hz)

theorem gaussHarmonic_field (p d : ℕ) [Fact p.Prime] :
    gaussHarmonic (K:=ZMod p) d=WPActualGaussBottom.fieldHarmonic p d := by
  simp only [gaussHarmonic,WPActualGaussBottom.fieldHarmonic,one_div]

/-- Scalar extension preserves the same full unit-pivot primitive. -/
theorem lowHEulerJ_map {L : Type*} [Field L] (f : K →+* L) (p : ℕ) (H : K[X]) :
    (lowHEulerJ p H).map f=lowHEulerJ p (H.map f) := by
  have hdiv : (H.map f).divX=H.divX.map f := by
    ext n
    rw [coeff_divX,coeff_map,coeff_map,coeff_divX]
  have hint (W : K[X]) :
      (unitPrimitiveP p W 0).map f=unitPrimitiveP p (W.map f) 0 := by
    simp only [unitPrimitiveP,integratedGeometric,Polynomial.map_sum,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
      _root_.map_div₀,_root_.map_zero,_root_.map_pow,_root_.map_natCast,coeff_map]
  rw [lowHEulerJ,lowHIntegralP,hint,lowHEulerJ,lowHIntegralP]
  congr 1
  simp only [lowHEulerR,hdiv,Polynomial.map_mul,Polynomial.map_X,
    Polynomial.map_sub,Polynomial.map_one,Polynomial.map_pow,Polynomial.map_comp]

/-- The actual H coefficient and full beta integral retain the original native coefficient. -/
theorem actualH_beta_coefficient (p n : ℕ) [Fact p.Prime] (hp : 19≤p)
    (hn : 1≤n) (hd : n≤p/6) :
    (actualH p).coeff n*betaEndpoint (K:=ZMod p) p (n-1)=
      (1/2 : ZMod p)*gaussA (K:=ZMod p) (p/6) n/(n : ZMod p)^2 := by
  have hu : (n : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p n
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have he := actual_native_beta_product p n hp hn hd
  rw [actualH,unitEuler_coeff,if_pos (by omega : n<p),actualF_eq_native p hp,
    nativeField_coeff,if_pos (by omega : n<p/6+1)]
  field_simp [hu,h2]
  linear_combination he

/-- The actual native low-H primitive has the exact finite Gauss endpoint in both prime classes. -/
theorem actual_lowHEulerJ_endpoint (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (lowHEulerJ p (actualH p)).eval 1=
      -(WPActualGaussBottom.fieldHarmonic p (p/6))^2 := by
  classical
  have hd : 1≤p/6 := by omega
  have hband : 6*(p/6)<p := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1|h5 <;> omega
  rw [lowHEulerJ_coefficient_expansion p (p/6) hp hd hband (actualH p)
    (actualH_degree p hp),eval_finsetSum]
  simp only [eval_mul,eval_C]
  change (∑ j ∈ Finset.range (p/6),
    (actualH p).coeff (j+1)*betaEndpoint (K:=ZMod p) p j)=
      -(WPActualGaussBottom.fieldHarmonic p (p/6))^2
  have hterms :
      (∑ j ∈ Finset.range (p/6),(actualH p).coeff (j+1)*betaEndpoint (K:=ZMod p) p j)=
      (1/2 : ZMod p)*(∑ j ∈ Finset.range (p/6),
        gaussA (K:=ZMod p) (p/6) (j+1)/((j+1 : ℕ) : ZMod p)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.add_sub_cancel,mul_div_assoc] using
      actualH_beta_coefficient p (j+1) hp (by omega)
        (by have := Finset.mem_range.mp hj; omega)
  rw [hterms]
  have hs := gaussSecondMoment_value (K:=ZMod p) (p/6)
    (fun n hn hb => WPFiniteField.denominator_ne_zero p n
      (Finset.mem_Ico.mpr (by omega)))
  have hm : gaussSecondMoment (K:=ZMod p) (p/6)=
      ∑ j ∈ Finset.range (p/6),gaussA (K:=ZMod p) (p/6) (j+1)/
        ((j+1 : ℕ) : ZMod p)^2 := by
    rw [gaussSecondMoment,Finset.sum_range_succ']
    simp only [Nat.cast_zero,zero_pow (by omega : (2 : ℕ)≠0),div_zero,add_zero]
  rw [←hm,hs,gaussHarmonic_field]
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2]

/-- Both characteristic-p branches consume the actual mapped H and its fixed original endpoint. -/
theorem actual_lowHEulerJ_endpoint_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (lowHEulerJ p ((actualH p).map (ActualThreePhase.φ (K:=K) p))).eval 1=
      -(ActualThreePhase.φ (K:=K) p (WPActualGaussBottom.fieldHarmonic p (p/6)))^2 := by
  rw [←lowHEulerJ_map]
  have he := congrArg (ActualThreePhase.φ (K:=K) p) (actual_lowHEulerJ_endpoint p hp)
  simpa only [←eval_map_apply,_root_.map_one,map_neg,map_pow] using he

end WPFieldAssembly.ActualGaussHarmonic
