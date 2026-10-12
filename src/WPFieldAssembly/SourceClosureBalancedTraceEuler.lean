import WPFieldAssembly.SourceClosureCommonWholeSource
import WPFieldAssembly.SourceClosureBalancedNativeReflection
import WPFieldAssembly.SourceClosureSigmaRingDerivative
import WPFieldAssembly.SourceClosureUVWholeContraction

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualCommonTraceReduction WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.ActualBalancedGreenTransfer WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualCommonFieldIBP WPFieldAssembly.SourceClosureCommonWholeSource
  WPFieldAssembly.SourceClosureSigmaActualVS
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedLog

namespace WPFieldAssembly.SourceClosureBalancedTraceEuler

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

private theorem Euler_integral_lift {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f)
    (A H F : R[T;T⁻¹]) (A' H' F' : K[T;T⁻¹])
    (hA : coefficientMap f A=A') (hH : coefficientMap f H=H')
    (hF : coefficientMap f F=F')
    (he : A'*D H'=dlogQNumerator*(invert F'-1)) :
    A*ringD H=dlogQNumerator*(invert F-1) := by
  apply WPLaurentIntegralResidue.coefficientMap_injective f hf
  simpa only [map_mul,map_sub,map_one,ringD_coefficientMap,ringD_field,
    hA,hH,hF,dlogQNumerator_map,coefficientMap_invert] using he

/-- The rational Euler identity is lifted before reduction, retaining the whole low family. -/
theorem actual_common_H_integral_euler (hp : 19≤p) :
    (actualAbarIntegral p).toLaurent*ringD (greenHAtIntegral p hp)=
      dlogQNumerator*(invert (actualLowFIntegral p hp)-1) := by
  have hF : coefficientMap (integralRationals p).subtype (actualLowFIntegral p hp)=
      lowFpullQ p := by
    simp only [actualLowFIntegral,coefficientMap_toLaurent,Polynomial.map_comp,
      NativeOriginalResidues.squareQIntegral_value p hp,
      WPHasseIntegralTransport.integralV_map_rational,lowFpullQ]
  have hA : (actualAbarIntegral p).map (integralRationals p).subtype=
      (WPFiniteZSource.Abar : ℚ[X]) := by
    simp only [actualAbarIntegral,Polynomial.map_mul,Polynomial.map_sub,
      Polynomial.map_ofNat,Polynomial.map_X,Polynomial.map_one,WPFiniteZSource.Abar]
  have hAL : coefficientMap (integralRationals p).subtype
      (actualAbarIntegral p).toLaurent=(WPFiniteZSource.Abar : ℚ[X]).toLaurent :=
    (coefficientMap_toLaurent (integralRationals p).subtype (actualAbarIntegral p)).trans
      (congrArg (fun P : ℚ[X] => P.toLaurent) hA)
  have hEuler : (WPFiniteZSource.Abar : ℚ[X]).toLaurent*D (greenHAtQ p hp)=
      (dlogQNumerator : ℚ[T;T⁻¹])*(invert (lowFpullQ p)-1) := by
    simpa only [dlogQNumerator] using actual_HQ_Euler_cleared p hp
  exact Euler_integral_lift (integralRationals p).subtype Subtype.val_injective
    (actualAbarIntegral p).toLaurent (greenHAtIntegral p hp) (actualLowFIntegral p hp)
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent (greenHAtQ p hp) (lowFpullQ p)
    hAL (greenHAtIntegral_rational p hp) hF hEuler

/-- The actual field Euler identity uses the original reflected low multiplier. -/
theorem actual_common_H_field_euler (hp : 19≤p) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*D (commonHField p)=
      dlogQNumerator*(T (-(((p-1)/2 : ℕ) : ℤ))*
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent-1) := by
  have he := congrArg (coefficientMap (residueHom p))
    (actual_common_H_integral_euler p hp)
  have hA : (actualAbarIntegral p).map (residueHom p)=
      (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    simp only [actualAbarIntegral,Polynomial.map_mul,Polynomial.map_sub,
      Polynomial.map_ofNat,Polynomial.map_X,Polynomial.map_one,WPFiniteZSource.Abar]
  simp only [map_mul,map_sub,map_one,coefficientMap_toLaurent,hA,
    ringD_coefficientMap,ringD_field,greenHAtIntegral_field p hp,
    dlogQNumerator_map,coefficientMap_invert,actualLowFIntegral_field p hp] at he
  change (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*D (commonHField p)=
    dlogQNumerator*(invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent-1) at he
  have ht : (T (-(((p-1)/2 : ℕ) : ℤ))*T (((p-1)/2 : ℕ) : ℤ) :
      (ZMod p)[T;T⁻¹])=1 := by rw [←T_add]; simp
  have hf : T (-(((p-1)/2 : ℕ) : ℤ))*
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent=
        invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent := by
    conv_lhs => rw [actual_low_F_weighted_reflection p hp]
    rw [←mul_assoc,ht,one_mul]
  rw [hf]
  exact he

noncomputable def actualLowWeightedTrace (hp : 19≤p) (J : (ZMod p)[T;T⁻¹]) : ZMod p :=
  originalWeightedFieldTrace p (T (-(((p-1)/2 : ℕ) : ℤ))*
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent*J)

/-- This is the SAME trace weight before and after the complete Green integration by parts. -/
theorem actual_low_weight_euler (hp : 19≤p) (J : (ZMod p)[T;T⁻¹]) :
    actualLowWeightedTrace p hp J=originalWeightedFieldTrace p J+
      kwFieldTrace p (D (commonHField p)*J) := by
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent=
      (LaurentPoleField.fieldAbar p).toLaurent := by
    congr 1
    unfold WPFiniteZSource.Abar LaurentPoleField.fieldAbar
    ring
  have he : (LaurentPoleField.fieldAbar p).toLaurent*
      (3*(R : (ZMod p)[T;T⁻¹])^p*(D (commonHField p)*J))=
        (3*R^p*dlogQNumerator)*
          ((T (-(((p-1)/2 : ℕ) : ℤ))*
            (NativeChiFieldSource.halfPullbackField p hp).toLaurent-1)*J) := by
    rw [←hA]
    linear_combination 3*(R : (ZMod p)[T;T⁻¹])^p*J*
      actual_common_H_field_euler p hp
  have ht := congrArg (LaurentPoleField.fieldTrace p (p+1)) he
  rw [LaurentPoleField.fieldTrace_cleared p p hp] at ht
  change kwFieldTrace p (D (commonHField p)*J)=
    originalWeightedFieldTrace p ((T (-(((p-1)/2 : ℕ) : ℤ))*
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent-1)*J) at ht
  rw [sub_mul,one_mul,weighted_sub] at ht
  change kwFieldTrace p (D (commonHField p)*J)=
    actualLowWeightedTrace p hp J-originalWeightedFieldTrace p J at ht
  linear_combination -ht

/-- A Frobenius-invisible homogeneous phase has the original entire weight. -/
theorem actual_low_weight_invisible (hp : 19≤p) (J : (ZMod p)[T;T⁻¹])
    (hJ : D J=0) : actualLowWeightedTrace p hp J=originalWeightedFieldTrace p J := by
  have hi := kwFieldTrace_IBP p hp (commonHField p) J
  rw [hJ,mul_zero] at hi
  have hz : kwFieldTrace p (0 : (ZMod p)[T;T⁻¹])=0 := by
    simp only [kwFieldTrace,mul_zero,map_zero]
  rw [hz,add_zero] at hi
  rw [actual_low_weight_euler p hp J,hi,add_zero]

end WPFieldAssembly.SourceClosureBalancedTraceEuler
