import WPFieldAssembly.SourceClosureActualUVAttachment
import WPFieldAssembly.SourceClosureBalancedNativeParticular

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUVPrimitiveSource WPFieldAssembly.SourceClosureUVPositiveSource
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureBalancedFirstSource WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualCommonTraceReduction

namespace WPFieldAssembly.SourceClosureBalancedUVSource

set_option maxHeartbeats 1600000

variable {K L : Type*} [Field K] [Field L]

theorem originalR_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (WPFiniteZSource.R p)=WPFiniteZSource.R p := by
  simp only [WPFiniteZSource.R,map_mul,map_pow,coefficientMap_C,coefficientMap_T,
    coefficientMap_toLaurent,map_div₀,map_one,map_ofNat,Polynomial.map_mul,
    Polynomial.map_sub,Polynomial.map_ofNat,Polynomial.map_X,Polynomial.map_one,
    WPFiniteZSource.Abar,squaredCoordinate_transport]

/-- The actual descended P has its whole derivative in either quadratic branch. -/
theorem actual_descendedP_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    D (descendedP p : K[T;T⁻¹])=WPFiniteZSource.R p-
      LaurentPolynomial.C (1/2 : K)*T (-1) := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  apply coefficientMap_injective_field f
  simp only [derivative_coefficientMap,descendedP_transport,map_sub,map_mul,
    coefficientMap_C,coefficientMap_T,map_div₀,map_one,map_ofNat,originalR_transport]
  rw [←originalP_descended p hp u hu]
  exact WPFiniteZSource.P_derivative p hp u

theorem actual_clearing_pole_normalization (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (nativeClearingL : K[T;T⁻¹])=-8*poleProduct ∧
      (nativeClearingL : K[T;T⁻¹])*T (-1)=-8*poleProductOverX ∧
        (nativeClearingGamma : K[T;T⁻¹])=-4*twiceGammaNumerator := by
  have ht : (T 1*T (-1) : K[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have ht2 : (T 2 : K[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
  have ht3 : (T 3 : K[T;T⁻¹])=T 1^3 := by rw [T_pow]; norm_num
  have hfour : LaurentPolynomial.C (1/4 : K)*4=1 := by
    have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
    change LaurentPolynomial.C (1/4 : K)*LaurentPolynomial.C (4 : K)=1
    rw [←map_mul,one_div_mul_cancel h4,map_one]
  have hL : (nativeClearingL : K[T;T⁻¹])=
      2*T 1*(T 1+1)*(WPFiniteZSource.Abar : K[X]).toLaurent := rfl
  rw [hL]
  simp only [nativeClearingGamma,poleProduct,poleProductOverX,
    twiceGammaNumerator,WPFiniteZSource.Abar,map_mul,map_sub,map_ofNat,
    Polynomial.toLaurent_X,map_one,ht2,ht3]
  constructor
  · linear_combination
      -2*T 1*(T 1+1)*(T 1-4)*hfour
  constructor
  · linear_combination
      -2*(T 1+1)*(T 1-4)*(4*T 1-1)*ht-
        2*(T 1+1)*(T 1-4)*hfour
  · linear_combination
      -(T 1^2+4*T 1+8)*hfour

/-- Positive B retains the entire actual comparison and the original P. -/
theorem actual_positive_B_cleared (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    2*(nativeClearingL : (ZMod p)[T;T⁻¹])*descendedBgamma p hp=
      -2*nativeClearingGamma*comparisonField p+
        nativeClearingL*T (-1)*(comparisonField p-descendedP p) := by
  have hn := actual_clearing_pole_normalization (K:=ZMod p) p hp
  have hb := descendedBgamma_source (K:=ZMod p) p hp
  rw [hn.2.1,hn.1,hn.2.2,←descendedP_actual_comparison p hp]
  unfold descendedPositiveNumerator at hb
  linear_combination -4*hb

theorem actual_proper_U_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p)=
      3*T 1*(T 1+1)*ActualChiEndpoints.zeta p*
        (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent^((p-1)/2) := by
  simp only [nativeProperUIntegral,map_mul,map_pow,map_add,map_ofNat,map_one,
    coefficientMap_T,actualZetaIntegral_field p hp,coefficientMap_toLaurent,
    comparisonCoordinateI_field p hp]

theorem actual_R_native_normalization (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (nativeClearingL : (ZMod p)[T;T⁻¹])*WPFiniteZSource.R p=
      coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/2 : ZMod p)=1 := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/2 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  have hthird : (3 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/3 : ZMod p)=1 := by
    change LaurentPolynomial.C (3 : ZMod p)*LaurentPolynomial.C (1/3 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h3,map_one]
  let A := (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent
  let s := (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent
  have hL : (nativeClearingL : (ZMod p)[T;T⁻¹])=2*T 1*(T 1+1)*A := rfl
  have hpow : A^(p-1)*A=A^p := by rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤p)]
  rw [actual_proper_U_field p hp,hL]
  change (2*T 1*(T 1+1)*A)*
      (LaurentPolynomial.C (1/2 : ZMod p)*T (-(p : ℤ))*A^(p-1)*s^((p-1)/2))=
    3*T 1*(T 1+1)*(LaurentPolynomial.C (1/3 : ZMod p)*T (-(p : ℤ))*A^p)*s^((p-1)/2)
  linear_combination
    T 1*(T 1+1)*T (-(p : ℤ))*
      s^((p-1)/2)*
        (A^(p-1)*A*hhalf-A^p*hthird+hpow)

/-- The original P source is cleared by the SAME U used in the proper metric. -/
theorem actual_P_native_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    2*(nativeClearingL : (ZMod p)[T;T⁻¹])*D (descendedP p)=
      2*coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p)-
        nativeClearingL*T (-1) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/2 : ZMod p)=1 := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/2 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  linear_combination
    2*(nativeClearingL : (ZMod p)[T;T⁻¹])*actual_descendedP_derivative (K:=ZMod p) p hp+
      2*actual_R_native_normalization p hp-nativeClearingL*T (-1)*hhalf

theorem actual_zeta_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (ActualChiEndpoints.zeta p)=ActualChiEndpoints.zeta p := by
  simp only [ActualChiEndpoints.zeta,map_mul,map_pow,coefficientMap_C,
    coefficientMap_T,coefficientMap_toLaurent,map_div₀,map_one,map_ofNat,
    WPFiniteZSource.Abar,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_ofNat,
    Polynomial.map_X,Polynomial.map_one]

/-- Descent retains both quadratic branches and the original three invisible chi slots. -/
theorem actual_halfChi_descended_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    NativeChiFieldSource.halfChiField p hp=
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*descendedP p+
        ActualChiEndpoints.zeta p*(ActualFirstGreen.CB p).toLaurent := by
  let K := AlgebraicClosure (ZMod p)
  have : CharP K p := charP_of_injective_ringHom
    (algebraMap (ZMod p) K).injective p
  let f : ZMod p →+* K := ActualThreePhase.φ p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : K)
    (by decide : 0<(2 : ℕ))
  have hc := ActualGreenResidue.actual_chi_finite_P (K:=K) p hp u hu
  rw [originalP_descended p hp u hu] at hc
  apply coefficientMap_injective_field f
  simpa only [map_add,map_mul,coefficientMap_toLaurent,descendedP_transport,
    actual_zeta_transport,ActualThreePhase.χK,ActualThreePhase.fK,
    ActualThreePhase.CBK] using hc

theorem actual_native_G_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperGIntegral p hp)=
      ActualChiEndpoints.zeta p*(ActualFirstGreen.CB p).toLaurent := by
  simp only [nativeProperGIntegral,map_mul,actualZetaIntegral_field p hp,
    coefficientMap_toLaurent,actualCBIntegral_field p hp]

/-- The original defect is attached to the whole chi and actual Sigma reflection. -/
theorem actual_native_defect_descended_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    3*coefficientMap (WPPIntegralReduction.residueHom p) (actualReflectionDefectIntegral p hp)=
      3*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*descendedP p+
        3*coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperGIntegral p hp)-
          (SourceClosureBalancedNativeParticular.actualSigmaPullback p hp).toLaurent+
            T (((p-1)/2 : ℕ) : ℤ)*invert
              (SourceClosureBalancedNativeParticular.actualSigmaPullback p hp).toLaurent := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hthird : (3 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/3 : ZMod p)=1 := by
    change LaurentPolynomial.C (3 : ZMod p)*LaurentPolynomial.C (1/3 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h3,map_one]
  rw [actual_reflection_defect_field p hp,actual_halfChi_descended_source p hp,
    actual_native_G_field p hp]
  dsimp only [weightedReflectionDifference,SourceClosureBalancedNativeParticular.actualSigmaPullback]
  linear_combination
    -(((ActualNormCrossAttachment.actualSigmaNative p hp).comp
        (WPHasseIntegralTransport.fieldV p)).toLaurent-
          T (((p-1)/2 : ℕ) : ℤ)*invert
            ((ActualNormCrossAttachment.actualSigmaNative p hp).comp
              (WPHasseIntegralTransport.fieldV p)).toLaurent)*hthird

/-- SB99 uses the SAME original Ucan-u0-VS and its actual integral Sigma. -/
theorem actual_UV_native_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    2*(nativeClearingL : (ZMod p)[T;T⁻¹])*D (actualUV p hp)=
      2*nativeClearingL*commonSigmaField p hp-
        2*nativeClearingGamma*comparisonField p+
          nativeClearingL*T (-1)*(comparisonField p-descendedP p) := by
  linear_combination
    2*(nativeClearingL : (ZMod p)[T;T⁻¹])*actualUV_derivative p hp+
      actual_positive_B_cleared p hp

end WPFieldAssembly.SourceClosureBalancedUVSource
