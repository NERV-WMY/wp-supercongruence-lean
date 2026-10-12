import WPFieldAssembly.ActualBpairMetric
import WPFieldAssembly.ActualBpairDerivativePair
import WPFieldAssembly.ActualBpairNativeTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.ActualSimplePoleResidue
open WPFieldAssembly.ActualCubicNativeSource WPFieldAssembly.ActualBpairNativeTail

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2000000

private theorem metric_smooth_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (a b c : ℕ) : ((2 : K)^a * 3^b * 5^c) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero a h2) (pow_ne_zero b h3))
    (pow_ne_zero c h5)

private theorem D_polynomial_origin_zero (P : K[X]) :
    (D P.toLaurent).coeff (-1)=0 := by
  rw [D_coeff]
  norm_num

private theorem trunc_negative_phase_polynomial (p : ℕ) (P : K[X])
    (hP : P.natDegree<p) : trunc (T (-(p : ℤ))*P.toLaurent)=0 := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff,coeff_zero]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) (j : ℤ) P.toLaurent
  simp only [map_one,one_mul] at hs
  rw [hs]
  exact WPFiniteJCarrier.toLaurent_coeff_outside P _ (Or.inr (by omega))

theorem actual_AK_reciprocal_D_pair (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (invert (actualAK p : K[X]).toLaurent*D (Dstar p : K[X]).toLaurent).coeff (-1)=
      -11*WPFiniteNC122.q p/50+
        21*(WPFiniteInversion.integerFermatQuotient p 3 : K)/100+
          WPFifthEntropy.C p u/2 := by
  have hD : (Dstar p : K[X]).natDegree<p := (Dstar_degree p hp).trans_lt (by omega)
  have hphase := reciprocal_derivative_negative_phase_zero p (nativeB p : K[X])
    (Dstar p : K[X]) hD
  have hlog := reciprocal_logTrace_derivative p (Dstar p : K[X]) hD
  have he : invert (actualAK p : K[X]).toLaurent=
      T (-(p : ℤ))*invert (nativeB p : K[X]).toLaurent+
        invert (nativeL p : K[X]).toLaurent := by
    rw [actual_AK_phase_source p hp]
    simp only [map_add,map_mul,Polynomial.toLaurent_X_pow,invert_T]
  rw [he,add_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hphase,zero_add]
  simp only [nativeL,map_add,map_sub,map_mul,Polynomial.toLaurent_C,invert_C,
    add_mul,sub_mul,mul_assoc,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply,Finsupp.sub_apply,C_mul_coeff,D_polynomial_origin_zero,mul_zero,
    zero_sub,hlog]
  change -((33/5 : K)*actualDMetric p)+(2/5 : K)*
    (-(1/4 : K)*((Dstar p : K[X]).eval 4-(Dstar p).eval 0)+
      4*((Dstar p : K[X]).eval (1/4)-(Dstar p).eval 0))=_
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  rw [actualDMetric_fermat p hp,ha,hb,←coeff_zero_eq_eval_zero,Dstar_origin_fifth p hp u hu]
  unfold WPFiniteNC122.h
  have h2 : (2 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 0 using 1; norm_num
  have h3 : (3 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 1 0 using 1; norm_num
  have h4 : (4 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h5 : (5 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 0 1 using 1; norm_num
  have h6 : (6 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h10 : (10 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 1 using 1; norm_num
  have h50 : (50 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 2 using 1; norm_num
  have h100 : (100 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 2 0 2 using 1; norm_num
  field_simp [h2,h3,h4,h5,h6,h10,h50,h100]
  ring

theorem actual_AK_reciprocal_D_p_pair (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (T (p : ℤ)*invert (actualAK p : K[X]).toLaurent*
      D (Dstar p : K[X]).toLaurent).coeff (-1)=
        12*WPFiniteNC122.q p/25-
          6*(WPFiniteInversion.integerFermatQuotient p 3 : K)/25 := by
  have hL : (nativeL p : K[X]).natDegree<p := (nativeL_degree p hp).trans_lt (by omega)
  have hphase := reciprocal_derivative_positive_phase_zero p (nativeL p : K[X])
    (Dstar p : K[X]) hL
  have he : T (p : ℤ)*invert (actualAK p : K[X]).toLaurent=
      invert (nativeB p : K[X]).toLaurent+
        T (p : ℤ)*invert (nativeL p : K[X]).toLaurent := by
    rw [actual_AK_phase_source p hp]
    simp only [map_add,map_mul,Polynomial.toLaurent_X_pow,invert_T,mul_add]
    rw [←mul_assoc,←T_add,add_neg_cancel,T_zero,one_mul]
  rw [he,add_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hphase,add_zero]
  simp only [nativeB,map_sub,map_mul,Polynomial.toLaurent_C,invert_C,sub_mul,
    mul_assoc,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,C_mul_coeff,
    D_polynomial_origin_zero,mul_zero,sub_zero]
  change (12/5 : K)*actualDMetric p=_
  rw [actualDMetric_fermat p hp]
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 1 using 1; norm_num
  have h25 : (25 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 0 2 using 1; norm_num
  field_simp [h2,h5,h10,h25]
  ring

theorem actual_AK_reciprocal_pole (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) : originPole (invert (actualAK p : K[X]).toLaurent)=0 := by
  obtain ⟨ha,hb⟩ := actual_AK_endpoints (K:=K) p hp
  rw [originPole_trunc_inverse,involutive_invert (actualAK p : K[X]).toLaurent,
    trunc_toLaurent,ha,hb,sub_self,zero_div]

theorem actual_AK_reciprocal_p_pole (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    originPole (T (p : ℤ)*invert (actualAK p : K[X]).toLaurent)=
      ((nativeB p : K[X]).eval (1/4)-(nativeB p).eval 4)/15 := by
  have hL : (nativeL p : K[X]).natDegree<p := (nativeL_degree p hp).trans_lt (by omega)
  have he : T (-(p : ℤ))*(actualAK p : K[X]).toLaurent=
      (nativeB p : K[X]).toLaurent+T (-(p : ℤ))*(nativeL p : K[X]).toLaurent := by
    rw [actual_AK_phase_source p hp]
    simp only [map_add,map_mul,Polynomial.toLaurent_X_pow,mul_add]
    rw [←mul_assoc,←T_add,neg_add_cancel,T_zero,one_mul]
  rw [originPole_trunc_inverse,map_mul,invert_T,involutive_invert (actualAK p : K[X]).toLaurent,he,map_add,
    trunc_toLaurent,trunc_negative_phase_polynomial p (nativeL p : K[X]) hL,
    add_zero]

/-- This relation uses the actual D source before taking any residue. -/
theorem actual_D_source_pole_relation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (F : K[T;T⁻¹]) :
    originPole (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*F)=
      originPole F-(2/5 : K)*(F*D (Dstar p : K[X]).toLaurent).coeff (-1) := by
  have he := congrArg (fun P : K[X] => P.toLaurent) (Dstar_cleared_source (K:=K) p hp)
  simp only [map_mul,map_sub,map_one,map_pow,Polynomial.toLaurent_C,←D_toLaurent] at he
  have hc : (WPFiniteZSource.Abar : K[X]).toLaurent*
      (F*D (Dstar p : K[X]).toLaurent)=
      LaurentPolynomial.C (5/2 : K)*
        (F-WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*F) := by
    linear_combination F*he
  have hh := congrArg originPole hc
  rw [originPole_cleared p hp,originPole_C_mul,originPole_sub] at hh
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  linear_combination (norm := (field_simp [h2,h5]; ring)) (2/5 : K)*hh

noncomputable def actualNativeMetric (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  -WPFiniteNC122.h p*originPole
    (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (25/3 : K)-LaurentPolynomial.C (55/4 : K)*T (p : ℤ))*
        invert (actualAK p : K[X]).toLaurent)

/-- The complete original metric keeps both phases and the genuine fifth-origin carrier. -/
theorem actualNativeMetric_NC126 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    actualNativeMetric (K:=K) p=
      -88*WPFiniteNC122.h p*WPFiniteNC122.q p/75+
        37*WPFiniteNC122.h p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/100+
          5*WPFiniteNC122.h p*WPFifthEntropy.C p u/3 := by
  have he : WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
      (LaurentPolynomial.C (25/3 : K)-LaurentPolynomial.C (55/4 : K)*T (p : ℤ))*
        invert (actualAK p : K[X]).toLaurent=
      LaurentPolynomial.C (25/3 : K)*
        (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*invert (actualAK p : K[X]).toLaurent)-
      LaurentPolynomial.C (55/4 : K)*
        (WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
          (T (p : ℤ)*invert (actualAK p : K[X]).toLaurent)) := by ring
  unfold actualNativeMetric
  rw [he,originPole_sub,originPole_C_mul,originPole_C_mul,
    actual_D_source_pole_relation p hp,actual_D_source_pole_relation p hp,
    actual_AK_reciprocal_pole p hp,actual_AK_reciprocal_p_pole p hp,
    actual_AK_reciprocal_D_pair p hp u hu,actual_AK_reciprocal_D_p_pair p hp]
  obtain ⟨ha,hb⟩ := nativeB_endpoints (K:=K) p hp
  rw [ha,hb]
  unfold nativeTau
  have h2 : (2 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 0 using 1; norm_num
  have h3 : (3 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 1 0 using 1; norm_num
  have h4 : (4 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h5 : (5 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 0 1 using 1; norm_num
  have h15 : (15 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 1 1 using 1; norm_num
  have h20 : (20 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 2 0 1 using 1; norm_num
  have h25 : (25 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 0 2 using 1; norm_num
  have h50 : (50 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 1 0 2 using 1; norm_num
  have h75 : (75 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 0 1 2 using 1; norm_num
  have h100 : (100 : K)≠0 := by
    convert metric_smooth_ne_zero (K:=K) p hp 2 0 2 using 1; norm_num
  field_simp [h2,h3,h4,h5,h15,h20,h25,h50,h75,h100]
  ring

end WPFieldAssembly.ActualBpairContraction
