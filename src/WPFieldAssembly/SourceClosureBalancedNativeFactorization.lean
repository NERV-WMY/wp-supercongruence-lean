import WPFieldAssembly.SourceClosureBalancedNativeForcing
import WPFieldAssembly.BalancedVbalSuccessorProperSquareBase

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.NativeIR28
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureVbalNativePrimitive

namespace WPFieldAssembly.SourceClosureBalancedNativeFactorization

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- No J_L index is deleted from this prescribed original contract2 carrier. -/
noncomputable def actualNativeJCarrier : (ZMod p)[X] :=
  (contract 2 (Polynomial.C (1/5 : ZMod p)*X^p*
    (WPFiniteKSource.JLP p).comp (4*X^3-3*X))).comp WPFiniteWSource.squaredCoordinate

theorem actual_native_J_carrier_conic (hp : 19≤p) :
    (actualNativeJCarrier p).comp (5*X^2-1)=
      Polynomial.C (1/5 : ZMod p)*X^p*(WPFiniteKSource.JLP p).comp (4*X^3-3*X) := by
  let Tc : (ZMod p)[X] := 4*X^3-3*X
  have ht : Tc.comp (-X)=-Tc := by
    simp only [Tc,sub_comp,mul_comp,ofNat_comp,pow_comp,X_comp]
    ring
  have hj := congrArg (fun P : (ZMod p)[X] => P.comp Tc) (actual_JLP_odd p)
  simp only [comp_assoc,neg_comp,X_comp] at hj
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hxp : (-X : (ZMod p)[X])^p=-X^p := hpodd.neg_pow X
  have hev : (Polynomial.C (1/5 : ZMod p)*X^p*(WPFiniteKSource.JLP p).comp Tc).comp (-X)=
      Polynomial.C (1/5 : ZMod p)*X^p*(WPFiniteKSource.JLP p).comp Tc := by
    simp only [mul_comp,C_comp,pow_comp,X_comp,comp_assoc,ht,hj,hxp]
    ring
  have hs := WPFieldAssembly.ActualConicDescent.squaredCoordinate_conic p hp
  change (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).comp (5*X^2-1)=X^2 at hs
  rw [actualNativeJCarrier,comp_assoc,hs,←expand_eq_comp_X_pow]
  exact even_expand_contract_two p hp _ hev

theorem actual_CB_square_factor (hp : 19≤p) :
    WPFieldAssembly.ActualFirstGreen.CB p^2=
      NativeChiFieldSource.halfPullbackField p hp*
        Polynomial.C (1/25 : ZMod p)*actualProperSquareCarrier p := by
  have hxp : (X^2 : (ZMod p)[X])^p=(X^p)^2 := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have hscale : (Polynomial.C (1/5 : ZMod p))^2=Polynomial.C (1/25 : ZMod p) := by
    rw [←Polynomial.C_pow]
    congr 1
    simp only [one_div]
    norm_num
  apply actual_conic_polynomial_injective p hp
  have hCB := (WPFieldAssembly.ActualFirstGreen.actual_carrier_pullbacks p hp).1
  change (WPFieldAssembly.ActualFirstGreen.CB p).comp (5*X^2-1)=
    Polynomial.C (1/5 : ZMod p)*X^p*
      (WPActualRankTwoLegendreField.actualLegendreJacobi p*
        WPActualRankTwoProper.properLegendreJacobi p).comp (4*X^3-3*X) at hCB
  have hs := WPFieldAssembly.ActualConicDescent.squaredCoordinate_conic p hp
  change (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).comp (5*X^2-1)=X^2 at hs
  simp only [pow_comp,mul_comp,C_comp,actualProperSquareCarrier]
  rw [hCB,actual_low_F_conic_field p hp,hs,actual_proper_square_pullback_conic p hp]
  simp only [mul_comp,pow_comp,mul_pow]
  rw [hscale,hxp]
  ring

/-- The actual complete proper primitive has its printed native expansion.
The factor (4s-3)^p retains Tc^p rather than replacing it by t^p. -/
theorem actual_local_proper_polynomial_expansion (hp : 19≤p) :
    2*NativeChiFieldSource.halfPullbackField p hp*actualProperPrimitiveCarrier p hp=
      2*WPFieldAssembly.ActualFirstGreen.CB p*actualSigmaPullback p hp+
        NativeChiFieldSource.halfPullbackField p hp*Polynomial.C (1/5 : ZMod p)*
          actualProperSquareCarrier p*actualProperHighPhase p+
        2*NativeChiFieldSource.halfPullbackField p hp^2*actualNativeJCarrier p := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[X])*Polynomial.C (1/2 : ZMod p)=1 := by
    change Polynomial.C (2 : ZMod p)*Polynomial.C (1/2 : ZMod p)=1
    rw [←Polynomial.C_mul,mul_one_div_cancel h2,Polynomial.C_1]
  have hphase : (X^p*(4*X^3-3*X)^p : (ZMod p)[X])=
      (X^2)^p*(4*X^2-3)^p := by
    calc
      _=(X*(4*X^3-3*X) : (ZMod p)[X])^p := (mul_pow _ _ _).symm
      _=(X^2*(4*X^2-3) : (ZMod p)[X])^p := by congr 1; ring
      _=_ := mul_pow _ _ _
  apply actual_conic_polynomial_injective p hp
  have hCB := (WPFieldAssembly.ActualFirstGreen.actual_carrier_pullbacks p hp).1
  change (WPFieldAssembly.ActualFirstGreen.CB p).comp (5*X^2-1)=
    Polynomial.C (1/5 : ZMod p)*X^p*
      (WPActualRankTwoLegendreField.actualLegendreJacobi p*
        WPActualRankTwoProper.properLegendreJacobi p).comp (4*X^3-3*X) at hCB
  have hs := WPFieldAssembly.ActualConicDescent.squaredCoordinate_conic p hp
  change (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).comp (5*X^2-1)=X^2 at hs
  simp only [mul_comp,add_comp,ofNat_comp,C_comp,pow_comp,
    actualProperSquareCarrier,actualProperHighPhase,sub_comp]
  rw [actual_low_F_conic_field p hp,actual_proper_primitive_carrier_conic p hp,hCB,
    actual_Sigma_pullback_conic p hp,hs,actual_proper_square_pullback_conic p hp,
    actual_native_J_carrier_conic p hp]
  simp only [actualNativeProperPrimitive,add_comp,mul_comp,C_comp,pow_comp,X_comp]
  linear_combination
    (WPActualRankTwoLegendreField.actualLegendreJacobi p).comp (4*X^3-3*X)^2*
      Polynomial.C (1/5 : ZMod p)*
        (WPActualRankTwoProper.properLegendreJacobi p).comp (4*X^3-3*X)^2*
          (X^p*(4*X^3-3*X)^p*hhalf+hphase)

noncomputable def actualProperJLocal : (ZMod p)[T;T⁻¹] :=
  ActualChiEndpoints.zeta p*(actualNativeJCarrier p).toLaurent

theorem actual_native_square_field_factor (hp : 19≤p) :
    coefficientMap (residueHom p) (nativeProperGIntegral p hp)^2=
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
        (ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
          (actualProperSquareCarrier p).toLaurent) := by
  have he := congrArg (fun P : (ZMod p)[X] => P.toLaurent) (actual_CB_square_factor p hp)
  simp only [map_pow,map_mul,Polynomial.toLaurent_C] at he
  rw [actual_native_G_field p hp]
  linear_combination ActualChiEndpoints.zeta p^2*he

theorem actual_local_proper_field_expansion (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    2*f*actualLocalProperParticular p hp=
      2*coefficientMap (residueHom p) (nativeProperGIntegral p hp)*
        (actualSigmaPullback p hp).toLaurent+
        f*actualProperSquareLocal p+2*f^2*actualProperJLocal p := by
  have he := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (actual_local_proper_polynomial_expansion p hp)
  simp only [map_mul,map_add,map_pow,map_ofNat,Polynomial.toLaurent_C] at he
  rw [actual_native_G_field p hp]
  dsimp only [actualLocalProperParticular,actualProperSquareLocal,actualProperJLocal]
  linear_combination ActualChiEndpoints.zeta p*he

theorem actual_reflected_proper_field_expansion (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
    2*f*(phi*invert (actualLocalProperParticular p hp))=
      2*(phi*invert (coefficientMap (residueHom p) (nativeProperGIntegral p hp)))*
        (phi*invert (actualSigmaPullback p hp).toLaurent)+
        f*(phi*invert (actualProperSquareLocal p))+2*f^2*invert (actualProperJLocal p) := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
  have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => invert L)
    (actual_local_proper_field_expansion p hp)
  simp only [map_mul,map_add,map_pow,map_ofNat] at he
  change 2*invert f*invert (actualLocalProperParticular p hp)=
    2*invert (coefficientMap (residueHom p) (nativeProperGIntegral p hp))*
      invert (actualSigmaPullback p hp).toLaurent+
    invert f*invert (actualProperSquareLocal p)+
    2*(invert f)^2*invert (actualProperJLocal p) at he
  have hf := actual_low_F_weighted_reflection p hp
  change f=phi*invert f at hf
  calc
    2*f*(phi*invert (actualLocalProperParticular p hp))=
        phi^2*(2*invert f*invert (actualLocalProperParticular p hp)) := by
      linear_combination 2*phi*invert (actualLocalProperParticular p hp)*hf
    _=phi^2*(2*invert (coefficientMap (residueHom p) (nativeProperGIntegral p hp))*
        invert (actualSigmaPullback p hp).toLaurent+
      invert f*invert (actualProperSquareLocal p)+
      2*(invert f)^2*invert (actualProperJLocal p)) := by rw [he]
    _=2*(phi*invert (coefficientMap (residueHom p) (nativeProperGIntegral p hp)))*
        (phi*invert (actualSigmaPullback p hp).toLaurent)+
      (phi*invert f)*(phi*invert (actualProperSquareLocal p))+
      2*(phi*invert f)^2*invert (actualProperJLocal p) := by ring
    _=_ := by simp only [←hf,f,phi]

/-- The printed numerator is attached to the actual full carriers, including both high phases. -/
noncomputable def actualRootFreePrintedN (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
  let S := coefficientMap (residueHom p) (comparisonIntegral p)
  let B := phi*invert (actualSigmaPullback p hp).toLaurent
  6*f*actualNativeUVZeroBranch p hp-3*f*SourceClosureUVFieldTransport.descendedP p^2-
    2*S*B+3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
      (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
      phi*invert (actualProperSquareLocal p)+
      2*f*(actualProperJLocal p+invert (actualProperJLocal p))

theorem actual_cleared_printed_factorization (hp : 19≤p) :
    actualNativeClearedNumerator p hp=
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualRootFreePrintedN p hp := by
  let G := coefficientMap (residueHom p) (nativeProperGIntegral p hp)
  let B := T (((p-1)/2 : ℕ) : ℤ)*invert (actualSigmaPullback p hp).toLaurent
  have hd := actual_native_defect_descended_source p hp
  have hs := actual_native_seed_field p hp
  simp only [nativeProperHIntegral,map_mul,coefficientMap_T,coefficientMap_invert] at hs
  have hl := actual_local_proper_field_expansion p hp
  have hr := actual_reflected_proper_field_expansion p hp
  have hsq := actual_native_square_field_factor p hp
  /- The whole defect gives 6G*delta=6fGP+6G^2-2G*Sigma+2G*B.
  The two proper expansions cancel -2G*Sigma; the seed gives
  2(G+phi*invert G)*B=-2f*S*B. Both square phases and the complete
  Jlocal+invert Jlocal remain in the printed numerator below. -/
  dsimp only [actualRootFreePrintedN,actualNativeClearedNumerator,
    SourceClosureBalancedNativeAlgebra.clearedParticular,actualWholeProperParticular]
  linear_combination 2*G*hd+hl+hr+3*hsq+2*B*hs

end WPFieldAssembly.SourceClosureBalancedNativeFactorization
