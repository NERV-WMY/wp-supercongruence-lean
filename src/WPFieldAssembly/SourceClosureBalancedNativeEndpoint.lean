import WPFieldAssembly.SourceClosureBalancedNativeReciprocal

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureLaurentBranchJets

namespace WPFieldAssembly.SourceClosureBalancedNativeEndpoint

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- Changing the fifth logarithm parameter changes only the complete original phase. -/
theorem original_P_parameter_difference (u : ZMod p) :
    WPFiniteZSource.P p u-descendedP p=
      LaurentPolynomial.C ((WPFifthEntropy.C p u-descendedC p)/15)*WPFiniteZSource.phase p := by
  rw [originalP_decomposition]
  simp only [descendedP,originalInvisibleP,WPFiniteABSourceTail.uSlot,
    descendedInvisibleP,WPFiniteZSource.phase,div_eq_mul_inv,map_add,map_sub,
    map_mul,map_neg,map_ofNat]
  ring

theorem original_phase_zero_ends (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
        (WPFiniteZSource.phase p)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
        (WPFiniteZSource.phase p)=0 := by
  have hv : (ActualChiEndpoints.fourUnit (K:=ZMod p) p hp : ZMod p)=4 := rfl
  have h4 : (4 : ZMod p)≠0 := (ActualChiEndpoints.fourUnit (K:=ZMod p) p hp).ne_zero
  have h4p : (4 : ZMod p)^p=4 := ZMod.pow_card _
  constructor <;>
    simp only [WPFiniteZSource.phase,map_sub,map_mul,map_ofNat,
      LaurentPolynomial.eval₂_T_n,LaurentPolynomial.eval₂_T_neg_n,
      Units.val_inv_eq_inv_val,hv,inv_inv,inv_pow,h4p]
  · field_simp [h4]
    ring
  · field_simp [h4]
    ring

theorem actual_P_unit_endpoints (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
        (descendedP p)=-(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
        (descendedP p)=(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have hphase := original_phase_zero_ends p hp
  have hP := ActualChiEndpoints.finite_P_endpoints (K:=ZMod p) p hp 0
  have hd := original_P_parameter_difference p 0
  have h4 := congrArg (LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
    (ActualChiEndpoints.fourUnit p hp)) hd
  have hq := congrArg (LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
    (ActualChiEndpoints.fourUnit p hp)⁻¹) hd
  rw [map_sub,map_mul,hphase.1,mul_zero] at h4
  rw [map_sub,map_mul,hphase.2,mul_zero] at hq
  constructor
  · linear_combination hP.1-h4
  · linear_combination hP.2-hq

theorem actual_low_F_unit_endpoints (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp) f=1 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹ f=1 := by
  have hc := congrArg (fun P : (ZMod p)[X] => P.eval 1) (actual_low_F_conic_field p hp)
  norm_num only [eval_comp,eval_sub,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one,one_pow] at hc
  rw [WPActualRankTwoComparison.actualLegendreJacobi_endpoint_one,one_pow] at hc
  have hv : (ActualChiEndpoints.fourUnit (K:=ZMod p) p hp : ZMod p)=4 := rfl
  have h4 : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent=1 := by
    simpa only [LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,hv] using hc
  have hr := congrArg (LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
    (ActualChiEndpoints.fourUnit p hp)) (SourceClosureBalancedNativeReflection.actual_low_F_weighted_reflection p hp)
  rw [map_mul,laurent_inversion_eval,LaurentPolynomial.eval₂_T_n,h4] at hr
  simp only [hv,WPFiniteWSource.four_half_power p hp,one_mul] at hr
  exact ⟨h4,hr.symm⟩

theorem actual_native_G_zero_ends (hp : 19≤p) :
    let G := coefficientMap (residueHom p) (nativeProperGIntegral p hp)
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp) G=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹ G=0 := by
  rw [actual_native_G_field p hp]
  exact ActualChiEndpoints.zeta_CB_endpoints p hp _

theorem actual_whole_proper_zero_ends (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
        (actualWholeProperParticular p hp)=0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
        (actualWholeProperParticular p hp)=0 := by
  have hl := ActualChiEndpoints.zeta_CB_endpoints (K:=ZMod p) p hp
    (actualProperPrimitiveCarrier p hp).toLaurent
  change LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
      (actualLocalProperParticular p hp)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
      (actualLocalProperParticular p hp)=0 at hl
  constructor
  · rw [actualWholeProperParticular,map_add,map_mul,laurent_inversion_eval,hl.1,hl.2,
      mul_zero,add_zero]
  · rw [actualWholeProperParticular,map_add,map_mul,laurent_inversion_eval,inv_inv,hl.1,hl.2,
      mul_zero,add_zero]

/-- The original reciprocal endpoint fixes the SAME quotient to six times the original mu. -/
theorem actual_native_ratio_unit_endpoint (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹ R=
      6*actualMu p hp := by
  let ev := LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let G := coefficientMap (residueHom p) (nativeProperGIntegral p hp)
  let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
  let q : ZMod p := WPFiniteInversion.integerFermatQuotient p 2
  have hP := (actual_P_unit_endpoints p hp).2
  have hf := (actual_low_F_unit_endpoints p hp).2
  have hG := (actual_native_G_zero_ends p hp).2
  have hT := (actual_whole_proper_zero_ends p hp).2
  have hE := (actual_balanced_zero_ends_field p hp).2
  change ev (descendedP p)=q at hP
  change ev f=1 at hf
  change ev G=0 at hG
  change ev (actualWholeProperParticular p hp)=0 at hT
  change ev (actualBalancedField p hp)=0 at hE
  have hUV : ev (actualNativeUVZeroBranch p hp)=ev (actualUV p hp)-
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp) := by
    rw [actualNativeUVZeroBranch,map_sub,LaurentPolynomial.eval₂_C,RingHom.id_apply]
  have hu : SourceClosureSigmaProperEndpoint.fourUnitField p hp=
      ActualChiEndpoints.fourUnit p hp := by apply Units.ext; rfl
  have he := congrArg ev hfactor
  change ev (6*f^2*actualNativeUVZeroBranch p hp-3*f^2*descendedP p^2-
    3*G^2-6*f*G*descendedP p+6*G*delta+2*f*actualWholeProperParticular p hp-
      6*f*actualBalancedField p hp)=ev (f^2*R) at he
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,hP,hf,hG,hT,hE,hUV] at he
  change ev R=6*actualMu p hp
  rw [actualMu,hu]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hhalf : (2 : ZMod p)*(q^2/2)=q^2 := by field_simp [h2]
  linear_combination -he+3*hhalf

/-- The actual reciprocal unit point fixes the middle and extreme coefficients together. -/
theorem actual_native_three_slot_unit_constraint (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R)
    (hR : R=LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    R.coeff 0+(17/4 : ZMod p)*R.coeff (p : ℤ)+(257/16 : ZMod p)*R.coeff (2*(p : ℤ))=
      6*actualMu p hp := by
  let ev := LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
  have hv : (ActualChiEndpoints.fourUnit (K:=ZMod p) p hp : ZMod p)=4 := rfl
  have h4 : (4 : ZMod p)≠0 := (ActualChiEndpoints.fourUnit (K:=ZMod p) p hp).ne_zero
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4^2 by ring]
    exact pow_ne_zero _ h4
  have h4p : (4 : ZMod p)^p=4 := ZMod.pow_card _
  have ht : ev (T (p : ℤ))=1/4 := by
    simp only [ev,LaurentPolynomial.eval₂_T_n,Units.val_inv_eq_inv_val,hv,
      inv_pow,h4p,one_div]
  have hti : ev (T (-(p : ℤ)))=4 := by
    simp only [ev,LaurentPolynomial.eval₂_T_neg_n,inv_inv,hv,h4p]
  have hdouble (n : ℤ) : (T (2*n) : (ZMod p)[T;T⁻¹])=T n^2 := by
    rw [T_pow]
    congr 1
  have ht2 : ev (T (2*(p : ℤ)))=1/16 := by
    rw [hdouble,map_pow,ht]
    field_simp [h4,h16]
    ring
  have hti2 : ev (T (-2*(p : ℤ)))=16 := by
    rw [show -2*(p : ℤ)=2*(-(p : ℤ)) by ring,hdouble,map_pow,hti]
    norm_num
  have he := congrArg ev hR
  simp only [map_add,map_mul,ev,LaurentPolynomial.eval₂_C,RingHom.id_apply] at he
  change ev R=R.coeff 0+R.coeff (p : ℤ)*(ev (T (p : ℤ))+ev (T (-(p : ℤ))))+
    R.coeff (2*(p : ℤ))*(ev (T (2*(p : ℤ)))+ev (T (-2*(p : ℤ)))) at he
  rw [ht,hti,ht2,hti2] at he
  have hvalue := actual_native_ratio_unit_endpoint p hp R hfactor
  change ev R=6*actualMu p hp at hvalue
  field_simp [h4,h16] at he ⊢
  linear_combination 64*hvalue-he

/-- The two actual normalizations leave precisely one unassigned extreme coefficient. -/
theorem three_slot_coefficient_normalization {K : Type*} [Field K]
    (h2 : (2 : K)≠0) (h5 : (5 : K)≠0) (c0 c1 c2 mu b : K)
    (hbranch : c0-2*c1+2*c2=-6*b)
    (hend : c0+(17/4 : K)*c1+(257/16 : K)*c2=6*mu) :
    c1=(24/25 : K)*(mu+b)-(9/4 : K)*c2 ∧
      c0=(48/25 : K)*(mu+b)-6*b-(13/2 : K)*c2 := by
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h16 : (16 : K)≠0 := by rw [show (16 : K)=4^2 by ring]; exact pow_ne_zero _ h4
  have h25 : (25 : K)≠0 := by rw [show (25 : K)=5^2 by ring]; exact pow_ne_zero _ h5
  have he := hend
  field_simp [h4,h16] at he
  have hmiddle : 100*c1=96*mu+96*b-225*c2 := by
    apply mul_left_cancel₀ h4
    linear_combination he-64*hbranch
  have hzero : 50*c0=96*mu-204*b-325*c2 := by
    linear_combination 50*hbranch+hmiddle
  constructor
  · field_simp [h4,h25]
    linear_combination hmiddle
  · field_simp [h2,h25]
    linear_combination hzero

end WPFieldAssembly.SourceClosureBalancedNativeEndpoint
