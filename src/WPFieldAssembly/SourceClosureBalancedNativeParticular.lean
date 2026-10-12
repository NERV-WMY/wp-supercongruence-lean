import WPFieldAssembly.SourceClosureBalancedFirstSource
import WPFieldAssembly.SourceClosureBalancedConicPrimitive
import WPFieldAssembly.SourceClosureVbalNativePrimitiveReflection

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteLaurentDifferential
  WPActualRankTwoLegendreField WPActualRankTwoProper WPActualRankTwoResidueSource
  WPActualGaussBottom WPPIntegralReduction WPFiniteWSource WPFiniteCubicLog
  WPFieldAssembly.NativeIR28 WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureVbalNativePrimitive
  WPFieldAssembly.SourceClosureBalancedConicPrimitive

namespace WPFieldAssembly.SourceClosureBalancedNativeParticular

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The original contract2 carrier of the complete proper primitive. -/
noncomputable def actualProperPrimitiveCarrier (hp : 19≤p) : (ZMod p)[X] :=
  (contract 2 (C (1/5 : ZMod p)*X^p*
    (actualNativeProperPrimitive p hp).comp (4*X^3-3*X))).comp squaredCoordinate

/-- The two additional sources are pulled back along the actual V polynomial. -/
noncomputable def actualSigmaPullback (hp : 19≤p) : (ZMod p)[X] :=
  (actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p)

noncomputable def actualTBPullback : (ZMod p)[X] :=
  (quadraticInverse (X*(WPFieldAssembly.ActualFirstGreen.B p))).comp
    (WPHasseIntegralTransport.fieldV p)

theorem actual_proper_primitive_carrier_conic (hp : 19≤p) :
    (actualProperPrimitiveCarrier p hp).comp (5*X^2-1)=
      C (1/5 : ZMod p)*X^p*(actualNativeProperPrimitive p hp).comp (4*X^3-3*X) := by
  have hs := WPFieldAssembly.ActualConicDescent.squaredCoordinate_conic p hp
  change (squaredCoordinate : (ZMod p)[X]).comp (5*X^2-1)=X^2 at hs
  rw [actualProperPrimitiveCarrier,comp_assoc,hs,←expand_eq_comp_X_pow]
  exact even_expand_contract_two p hp _ (actual_native_proper_carrier_even p hp)

/-- The rational cubic identity is transported through the original integral V. -/
theorem actual_V_conic (hp : 19≤p) :
    (WPHasseIntegralTransport.fieldV p).comp (5*X^2-1)=1-(4*X^3-3*X)^2 := by
  simpa only [WPFiniteJHighCoefficient.conic, WPFiniteCubicLog.Tc] using
    WPActualNativeJacobiJet.actual_native_V_conic p hp

theorem actual_Sigma_pullback_conic (hp : 19≤p) :
    (actualSigmaPullback p hp).comp (5*X^2-1)=
      (actualLegendreJacobi p*actualRankDividedField p (by omega)).comp (4*X^3-3*X) := by
  have hs := even_native_attachment p hp
    (actualLegendreJacobi p*actualRankDividedField p (by omega)) (actual_YR_even p hp)
  rw [actualSigmaPullback,actualSigmaNative,comp_assoc,actual_V_conic p hp,
    show (1-(4*X^3-3*X)^2 : (ZMod p)[X])=
      (1-X^2 : (ZMod p)[X]).comp (4*X^3-3*X) by
        simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,hs]

theorem actual_TB_pullback_conic (hp : 19≤p) :
    (actualTBPullback p).comp (5*X^2-1)=
      (X*(WPFieldAssembly.ActualFirstGreen.B p)).comp (4*X^3-3*X) := by
  have he : (X*(WPFieldAssembly.ActualFirstGreen.B p)).comp (-X)=
      X*(WPFieldAssembly.ActualFirstGreen.B p) := by
    rw [mul_comp,X_comp,WPFieldAssembly.ActualFirstGreen.actual_B_odd p hp]
    ring
  have hs := even_native_attachment p hp _ he
  rw [actualTBPullback,comp_assoc,actual_V_conic p hp,
    show (1-(4*X^3-3*X)^2 : (ZMod p)[X])=
      (1-X^2 : (ZMod p)[X]).comp (4*X^3-3*X) by
        simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,hs]

/-- This is the original proper primitive source after conic descent, without a source premise. -/
theorem actual_proper_primitive_polynomial_source (hp : 19≤p) :
    let f := NativeChiFieldSource.halfPullbackField p hp
    let H := actualProperPrimitiveCarrier p hp
    2*(X+1)*WPFiniteZSource.Abar*(f*H.derivative-H*f.derivative)=
      3*(X+1)*squaredCoordinate^((p-1)/2)*
        (actualSigmaPullback p hp+C (fieldHarmonic p (p/6))*f^2+f*actualTBPullback p) := by
  have hN := WPFiniteWSource.half_exponent p hp
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hsource := actual_native_proper_primitive_source p hp
  dsimp only at hsource
  have hf : (NativeChiFieldSource.halfPullbackField p hp).comp (5*X^2-1)=
      (actualLegendreJacobi p^2).comp (4*X^3-3*X) := by
    simpa only [pow_comp] using actual_low_F_conic_field p hp
  have hsource' :
      (1-X^2)*(actualLegendreJacobi p^2*(actualNativeProperPrimitive p hp).derivative-
        (actualLegendreJacobi p^2).derivative*actualNativeProperPrimitive p hp)=
      actualLegendreJacobi p*actualRankDividedField p (by omega)+
        C (fieldHarmonic p (p/6))*(actualLegendreJacobi p^2)^2+
          actualLegendreJacobi p^2*(X*WPFieldAssembly.ActualFirstGreen.B p) := by
    dsimp only [WPFieldAssembly.ActualFirstGreen.B]
    linear_combination hsource
  have hc := conic_primitive_cleared p ((p-1)/2) hN.symm
    (ZMod.natCast_self p) h5
    (NativeChiFieldSource.halfPullbackField p hp) (actualLegendreJacobi p^2)
    (actualNativeProperPrimitive p hp)
    (actualLegendreJacobi p*actualRankDividedField p (by omega))
    (X*WPFieldAssembly.ActualFirstGreen.B p)
    (actualProperPrimitiveCarrier p hp) (actualSigmaPullback p hp) (actualTBPullback p)
    (fieldHarmonic p (p/6)) hf
    (actual_proper_primitive_carrier_conic p hp)
    (actual_Sigma_pullback_conic p hp) (actual_TB_pullback_conic p hp) hsource'
  simpa only [WPFiniteZSource.Abar,squaredCoordinate,one_div] using hc

theorem actual_zeta_field_derivative :
    D (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹])=0 := by
  have hp0 : ((p : ℤ) : ZMod p)=0 := by
    simpa only [Int.cast_natCast] using ZMod.natCast_self p
  have hT : D (LaurentPolynomial.T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=0 := by
    rw [show (LaurentPolynomial.T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1 : ZMod p)*LaurentPolynomial.T (-(p : ℤ)) by simp,
      D_monomial]
    simp only [Int.cast_neg,hp0,neg_zero,mul_zero,map_zero,zero_mul]
  have hA : D ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent^p)=0 := by
    rw [←map_pow,D_toLaurent,derivative_pow,ZMod.natCast_self,Polynomial.C_0,
      zero_mul,zero_mul,map_zero]
  simp only [ActualChiEndpoints.zeta,D_mul,D_C,hT,hA,zero_mul,mul_zero,zero_add]

/-- The local particular is the actual conic carrier multiplied by the original zeta. -/
noncomputable def actualLocalProperParticular (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  ActualChiEndpoints.zeta p*(actualProperPrimitiveCarrier p hp).toLaurent

theorem actual_local_proper_particular_source (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let U := 3*LaurentPolynomial.T 1*(LaurentPolynomial.T 1+1)*
      ActualChiEndpoints.zeta p*(squaredCoordinate : (ZMod p)[X]).toLaurent^((p-1)/2)
    nativeClearingL*(f*D (actualLocalProperParticular p hp)-
      actualLocalProperParticular p hp*D f)=
        U*((actualSigmaPullback p hp).toLaurent+
          LaurentPolynomial.C (fieldHarmonic p (p/6))*f^2+f*(actualTBPullback p).toLaurent) := by
  have hs := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (actual_proper_primitive_polynomial_source p hp)
  simp only [map_mul,map_add,map_sub,map_pow,map_ofNat,map_one,
    Polynomial.toLaurent_X,Polynomial.toLaurent_C,←D_toLaurent] at hs
  have hL : (nativeClearingL : (ZMod p)[T;T⁻¹])=
      2*LaurentPolynomial.T 1*(LaurentPolynomial.T 1+1)*
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent := rfl
  dsimp only [actualLocalProperParticular]
  rw [hL]
  simp only [D_mul,actual_zeta_field_derivative,zero_mul,zero_add]
  linear_combination LaurentPolynomial.T 1*(ActualChiEndpoints.zeta p)*hs

end WPFieldAssembly.SourceClosureBalancedNativeParticular
