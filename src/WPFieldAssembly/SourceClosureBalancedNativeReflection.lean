import WPFieldAssembly.SourceClosureBalancedUVSource
import WPFieldAssembly.SourceClosureBalancedPrimitiveReflection

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedPrimitiveReflection

namespace WPFieldAssembly.SourceClosureBalancedNativeReflection

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_low_F_weighted_reflection (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent=
      T (((p-1)/2 : ℕ) : ℤ)*invert
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent := by
  have hf := actual_low_multiplier_field p hp
  simpa only [actualLowMIntegral,map_mul,coefficientMap_T,coefficientMap_invert,
    actualLowFIntegral_field p hp] using hf.symm

theorem actual_clearing_L_reflection :
    invert (nativeClearingL : (ZMod p)[T;T⁻¹])=T (-5)*nativeClearingL := by
  change invert (2*T 1*(T 1+1)*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)=
    T (-5)*(2*T 1*(T 1+1)*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)
  have ha := WPFiniteZSource.invert_Abar (K:=ZMod p)
  have ht4 : (T (-1)*T (-1)*T (-2) : (ZMod p)[T;T⁻¹])=T (-4) := by
    rw [←T_add,←T_add]
    norm_num
  have ht3 : (T (-1)*T (-2) : (ZMod p)[T;T⁻¹])=T (-3) := by
    rw [←T_add]
    norm_num
  have hr4 : (T (-5)*T 1 : (ZMod p)[T;T⁻¹])=T (-4) := by
    rw [←T_add]
    norm_num
  have hr3 : (T (-5)*T 1*T 1 : (ZMod p)[T;T⁻¹])=T (-3) := by
    rw [←T_add,←T_add]
    norm_num
  simp only [map_mul,map_add,map_ofNat,map_one,invert_T,ha]
  linear_combination
    2*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*ht4+
      2*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*ht3-
        2*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*hr4-
          2*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*hr3

theorem actual_zeta_phase (hp : 19≤p) :
    (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1/3 : ZMod p)*WPFiniteZSource.phase p := by
  have ht : (T (-(p : ℤ))*T (p : ℤ) : (ZMod p)[T;T⁻¹])=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  rw [ActualChiEndpoints.zeta,WPFiniteZSource.phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1/3 : ZMod p)*WPFiniteZSource.phase p*ht

theorem actual_zeta_reflection (hp : 19≤p) :
    invert (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹])=ActualChiEndpoints.zeta p := by
  rw [actual_zeta_phase p hp]
  simp only [WPFiniteZSource.phase,map_mul,map_sub,map_ofNat,invert_C,invert_T,neg_neg]
  ring

theorem actual_native_U_reflection (hp : 19≤p) :
    invert (coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p))=
      T (-(((p-1)/2 : ℕ) : ℤ)-3)*
        coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p) := by
  let N : ℤ := ((p-1)/2 : ℕ)
  have ht2 : (T (-1)*T (-1)*T (-N) : (ZMod p)[T;T⁻¹])=T (-N-2) := by
    rw [←T_add,←T_add]
    congr 1
    omega
  have ht1 : (T (-1)*T (-N) : (ZMod p)[T;T⁻¹])=T (-N-1) := by
    rw [←T_add]
    congr 1
    omega
  have hr1 : (T (-N-3)*T 1*T 1 : (ZMod p)[T;T⁻¹])=T (-N-1) := by
    rw [←T_add,←T_add]
    congr 1
    omega
  have hr2 : (T (-N-3)*T 1 : (ZMod p)[T;T⁻¹])=T (-N-2) := by
    rw [←T_add]
    congr 1
    omega
  rw [actual_proper_U_field p hp]
  simp only [map_mul,map_add,map_ofNat,map_one,invert_T,actual_zeta_reflection p hp,
    WPFiniteZSource.invert_squared_power]
  change _=T (-N-3)*_
  linear_combination
    3*ActualChiEndpoints.zeta p*
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent^((p-1)/2)*
        (ht2+ht1-hr1-hr2)

noncomputable def actualWholeProperParticular (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  actualLocalProperParticular p hp+T (((p-1)/2 : ℕ) : ℤ)*
    invert (actualLocalProperParticular p hp)

/-- Both actual proper halves satisfy the whole SB99 primitive source. -/
theorem actual_whole_proper_particular_source (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let U := coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p)
    let G := coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperGIntegral p hp)
    let delta := coefficientMap (WPPIntegralReduction.residueHom p) (actualReflectionDefectIntegral p hp)
    let TB := (actualTBPullback p).toLaurent
    nativeClearingL*(f*D (actualWholeProperParticular p hp)-
      actualWholeProperParticular p hp*D f)=
        U*(3*(f*SourceClosureUVFieldTransport.descendedP p+G-delta)+
          LaurentPolynomial.C (WPActualGaussBottom.fieldHarmonic p (p/6))*
            f^2*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+f*(TB-invert TB)) := by
  have hlocal := actual_local_proper_particular_source p hp
  dsimp only at hlocal
  rw [←actual_proper_U_field p hp] at hlocal
  have href := weighted_proper_source_reflection (((p-1)/2 : ℕ) : ℤ)
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent nativeClearingL
    (coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p))
    (actualLocalProperParticular p hp) (actualSigmaPullback p hp).toLaurent
    (actualTBPullback p).toLaurent (WPActualGaussBottom.fieldHarmonic p (p/6))
    (actual_low_F_weighted_reflection p hp) (actual_clearing_L_reflection p)
    (actual_native_U_reflection p hp) hlocal
  have hdelta := actual_native_defect_descended_source p hp
  dsimp only [actualWholeProperParticular]
  simp only [map_add]
  linear_combination
    hlocal+href+
      coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p)*hdelta

end WPFieldAssembly.SourceClosureBalancedNativeReflection
