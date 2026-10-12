import WPFieldAssembly.SourceClosureBalancedNativeForcing
import WPFieldAssembly.SourceClosureUVSupport
import WPFieldAssembly.SourceClosureSigmaVSSupport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualGreenPrimitive WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeAlgebra
  WPFieldAssembly.SourceClosureUVSupport
  WPFieldAssembly.SourceClosureUVCanonicalHoles
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureSigmaActualVS

namespace WPFieldAssembly.SourceClosureBalancedNativeSupport

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_UV_bounds (hp : 19≤p) :
    Above (actualUV p hp) (3*(((p-1)/2 : ℕ) : ℤ)+1) ∧
      Above (invert (actualUV p hp)) (3*(((p-1)/2 : ℕ) : ℤ)+1) := by
  have hu := descendedU_bounds (K:=ZMod p) p hp
  have hvs : Above (actualVSField p hp) (3*(((p-1)/2 : ℕ) : ℤ)+1) := by
    intro j hj
    exact WPFieldAssembly.SourceClosureSigmaVSSupport.actualVSField_support p hp j
      (Or.inr (by omega))
  have hvsi : Above (invert (actualVSField p hp)) (3*(((p-1)/2 : ℕ) : ℤ)+1) := by
    rw [actualVSField_reflection p hp]
    exact hvs
  constructor
  · exact above_sub_same _ _ _ (Above_mono hu.1 (by omega)) hvs
  · simpa only [actualUV,map_sub] using
      above_sub_same _ _ _ (Above_mono hu.2 (by omega)) hvsi

theorem actual_UV_zero_branch_bounds (hp : 19≤p) :
    Above (actualNativeUVZeroBranch p hp) (3*(((p-1)/2 : ℕ) : ℤ)+1) ∧
      Above (invert (actualNativeUVZeroBranch p hp)) (3*(((p-1)/2 : ℕ) : ℤ)+1) := by
  have hu := actual_UV_bounds p hp
  have hc := Above_mono (Above_C
    (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp)))
      (by omega : 0≤3*(((p-1)/2 : ℕ) : ℤ)+1)
  constructor
  · exact above_sub_same _ _ _ hu.1 hc
  · simpa only [actualNativeUVZeroBranch,map_sub,invert_C] using
      above_sub_same _ _ _ hu.2 hc

theorem above_residue_from_rational (L : (integralRationals p)[T;T⁻¹]) (b : ℤ)
    (hL : Above (coefficientMap (integralRationals p).subtype L) b) :
    Above (coefficientMap (residueHom p) L) b := by
  intro j hj
  have hz : L.coeff j=0 := by
    apply Subtype.ext
    change (L.coeff j : ℚ)=0
    simpa only [coefficientMap_coeff,Subring.subtype_apply] using hL j hj
  rw [coefficientMap_coeff,hz,map_zero]

/-- Reflection retains the actual order N-3d at the origin. -/
theorem actual_low_F_bounds (hp : 19≤p) :
    Above (NativeChiFieldSource.halfPullbackField p hp).toLaurent
      (3*((p/6 : ℕ) : ℤ)) ∧
      Above (invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent)
        (3*((p/6 : ℕ) : ℤ)-(((p-1)/2 : ℕ) : ℤ)) := by
  have hd := actual_balanced_multiplier_exact_degree p hp
  have hf := Above_toLaurent _ _ hd.le
  have hf' : Above (NativeChiFieldSource.halfPullbackField p hp).toLaurent
      (3*((p/6 : ℕ) : ℤ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hf
  have he : invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent=
      T (-(((p-1)/2 : ℕ) : ℤ))*(NativeChiFieldSource.halfPullbackField p hp).toLaurent := by
    have hr := actual_low_F_weighted_reflection p hp
    have ht : (T (-(((p-1)/2 : ℕ) : ℤ))*T (((p-1)/2 : ℕ) : ℤ) : (ZMod p)[T;T⁻¹])=1 := by
      rw [←T_add,neg_add_cancel,T_zero]
    linear_combination -T (-(((p-1)/2 : ℕ) : ℤ))*hr-
      invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent*ht
  refine ⟨hf',?_⟩
  rw [he]
  simpa only [sub_eq_add_neg,add_comm] using Above_shift hf' (-(((p-1)/2 : ℕ) : ℤ))

theorem actual_zeta_bounds (hp : 19≤p) :
    Above (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹]) (p : ℤ) ∧
      Above (invert (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹])) (p : ℤ) := by
  have hphase : Above (WPFiniteZSource.phase p : (ZMod p)[T;T⁻¹]) (p : ℤ) := by
    exact above_sub_same _ _ _ (above_sub_same _ _ _
      (Above_mono (Above_C (17 : ZMod p)) (by omega))
      (Above_C_mul (above_T (p : ℤ)) (4 : ZMod p)))
      (Above_mono (Above_C_mul (above_T (-(p : ℤ))) (4 : ZMod p)) (by omega))
  have hz : Above (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹]) (p : ℤ) := by
    rw [actual_zeta_phase p hp]
    exact Above_C_mul hphase _
  exact ⟨hz,by rw [actual_zeta_reflection p hp]; exact hz⟩

/-- The original proper carrier has degree at most 2p+3d-3, before multiplying by zeta. -/
theorem actual_proper_primitive_carrier_degree (hp : 19≤p) :
    (actualProperPrimitiveCarrier p hp).natDegree≤2*p+3*(p/6)-3 := by
  have hTc : (4*X^3-3*X : (ZMod p)[X]).natDegree≤3 := by compute_degree
  have hH := WPFieldAssembly.SourceClosureVbalNativePrimitive.actual_native_proper_primitive_degree p hp
  have hc := natDegree_comp_le.trans (Nat.mul_le_mul hH hTc)
  have hxp : (Polynomial.C (1/5 : ZMod p)*X^p : (ZMod p)[X]).natDegree≤p :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le p)
  have hwhole := natDegree_mul_le_of_le hxp hc
  have hcontract : (contract 2 (Polynomial.C (1/5 : ZMod p)*X^p*
      (WPFieldAssembly.SourceClosureVbalNativePrimitive.actualNativeProperPrimitive p hp).comp
        (4*X^3-3*X))).natDegree≤2*p+3*(p/6)-3 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_contract (by norm_num : (2 : ℕ)≠0)]
    apply coeff_eq_zero_of_natDegree_lt
    omega
  have hs : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).natDegree≤1 := by
    unfold WPFiniteWSource.squaredCoordinate
    compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hcontract hs).trans (by omega))

theorem actual_local_proper_particular_bounds (hp : 19≤p) :
    Above (actualLocalProperParticular p hp) (3*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3) ∧
      Above (invert (actualLocalProperParticular p hp)) (p : ℤ) := by
  have hz := actual_zeta_bounds p hp
  have hH := Above_toLaurent _ _ (actual_proper_primitive_carrier_degree p hp)
  constructor
  · change Above
      (ActualChiEndpoints.zeta p*(actualProperPrimitiveCarrier p hp).toLaurent)
        (3*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3)
    exact Above_mono (Above_mul hz.1 hH) (by omega)
  · simpa only [actualLocalProperParticular,map_mul,add_zero] using
      Above_mul hz.2 (Above_invert_toLaurent (actualProperPrimitiveCarrier p hp))

/-- Both proper halves keep their full reflected support. -/
theorem actual_whole_proper_particular_bounds (hp : 19≤p) :
    Above (actualWholeProperParticular p hp) (3*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3) ∧
      Above (invert (actualWholeProperParticular p hp))
        (3*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-(((p-1)/2 : ℕ) : ℤ)-3) := by
  have hi (L : (ZMod p)[T;T⁻¹]) : invert (invert L)=L :=
    LaurentPolynomial.involutive_invert L
  have hh : 2*(((p-1)/2 : ℕ) : ℤ)+1=(p : ℤ) := by
    exact_mod_cast (WPFiniteWSource.half_exponent p hp).symm
  have ht := actual_local_proper_particular_bounds p hp
  constructor
  · exact above_add_same _ _ _ ht.1 (Above_mono (Above_shift ht.2 _ ) (by omega))
  · simpa only [actualWholeProperParticular,map_add,map_mul,invert_T,
      hi] using
      above_add_same _ _ _ (Above_mono ht.2 (by omega))
        (Above_mono (Above_shift ht.1 (-(((p-1)/2 : ℕ) : ℤ))) (by omega))

theorem actual_CB_field_degree (hp : 19≤p) :
    (WPFieldAssembly.ActualFirstGreen.CB p).natDegree≤(p-1)/2+3*(p/6)-1 := by
  rw [←actualCBIntegral_field p hp]
  apply natDegree_map_le.trans
  rw [←natDegree_map_eq_of_injective (Subring.subtype_injective (integralRationals p)) _,
    actual_CB_rational_value p hp]
  exact actual_CB_degree_bound p hp

theorem actual_native_G_bounds (hp : 19≤p) :
    Above (coefficientMap (residueHom p) (nativeProperGIntegral p hp))
      ((p : ℤ)+(((p-1)/2 : ℕ) : ℤ)+3*((p/6 : ℕ) : ℤ)-1) ∧
      Above (invert (coefficientMap (residueHom p) (nativeProperGIntegral p hp))) (p : ℤ) := by
  rw [actual_native_G_field p hp]
  have hz := actual_zeta_bounds p hp
  have hc := Above_toLaurent _ _ (actual_CB_field_degree p hp)
  constructor
  · exact Above_mono (Above_mul hz.1 hc) (by omega)
  · simpa only [map_mul,add_zero] using
      Above_mul hz.2 (Above_invert_toLaurent (WPFieldAssembly.ActualFirstGreen.CB p))

/-- The defect is supported in [0,N] by its actual characteristic-zero p-division. -/
theorem actual_reflection_defect_bounds (hp : 19≤p) :
    Above (coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp))
      (((p-1)/2 : ℕ) : ℤ) ∧
      Above (invert (coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp))) 0 := by
  have hi (L : ℚ[T;T⁻¹]) : invert (invert L)=L :=
    LaurentPolynomial.involutive_invert L
  let n : ℤ := (((p-1)/2 : ℕ) : ℤ)
  let F : ℚ[T;T⁻¹] := lowFpullQ p
  let delta : ℚ[T;T⁻¹] := coefficientMap (integralRationals p).subtype
    (actualReflectionDefectIntegral p hp)
  have hn : 2*n+1=(p : ℤ) := by
    dsimp only [n]
    exact_mod_cast (WPFiniteWSource.half_exponent p hp).symm
  have hdn : (3*((p/6 : ℕ) : ℤ))≤n := by
    dsimp only [n] at hn ⊢
    omega
  have hd : ((WPFieldAssembly.NativeOriginalResidues.squareQ p).comp
      WPActualPullbackSource.Vpolynomial).natDegree≤3*(p/6) := by
    have hV : (WPActualPullbackSource.Vpolynomial : ℚ[X]).natDegree≤3 := by
      unfold WPActualPullbackSource.Vpolynomial
      compute_degree
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul (WPFieldAssembly.NativeOriginalResidues.actual_squareQ_degree p hp) hV).trans
        (by omega))
  have hF : Above F n := by
    apply Above_mono (Above_toLaurent _ _ hd)
    exact_mod_cast hdn
  have hFi : Above (invert F) 0 := Above_invert_toLaurent _
  have hnum : Above (F-T n*invert F) n :=
    above_sub_same _ _ _ hF (by simpa only [add_zero] using Above_shift hFi n)
  have hnumi : Above (invert (F-T n*invert F)) 0 := by
    simpa only [map_sub,map_mul,invert_T,hi] using
      above_sub_same _ _ _ hFi (Above_mono (Above_shift hF (-n)) (by omega))
  have hsource : F-T n*invert F=LaurentPolynomial.C (p : ℚ)*delta := by
    have hs := congrArg (coefficientMap (integralRationals p).subtype)
      (actual_low_reflection_defect_source p hp)
    simpa only [actualLowReflectionNumeratorIntegral,weightedReflectionDifference,
      map_sub,map_mul,coefficientMap_T,coefficientMap_invert,coefficientMap_toLaurent,
      Polynomial.map_comp,NativeOriginalResidues.squareQIntegral_value p hp,
      WPHasseIntegralTransport.integralV_map_rational,coefficientMap_C,map_natCast,
      lowFpullQ,n,F,delta] using hs
  have hpq : (p : ℚ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hdq : Above delta n ∧ Above (invert delta) 0 := by
    constructor
    · intro j hj
      have hz := hnum j hj
      rw [hsource,constant_mul_coeff] at hz
      exact (mul_eq_zero.mp hz).resolve_left hpq
    · intro j hj
      have hz := hnumi j hj
      rw [hsource,map_mul,invert_C,constant_mul_coeff] at hz
      exact (mul_eq_zero.mp hz).resolve_left hpq
  constructor
  · exact above_residue_from_rational p _ _ hdq.1
  · rw [←coefficientMap_invert]
    apply above_residue_from_rational p
    simpa only [coefficientMap_invert] using hdq.2

/-- Every term of the cleared particular retains the precise reflected lower order. -/
theorem cleared_particular_bounds {K : Type*} [Field K]
    (p N d : ℤ) (hp : 19≤p) (hN : 2*N+1=p) (hd : 1≤d) (hdN : d≤N)
    (f G P delta T0 Tproper : K[T;T⁻¹])
    (hf : Above f d) (hfi : Above (invert f) (d-N))
    (hG : Above G (p+N+d-1)) (hGi : Above (invert G) p)
    (hP : Above P (3*N)) (hPi : Above (invert P) p)
    (hdelta : Above delta N) (hdeltai : Above (invert delta) 0)
    (hT0 : Above T0 (3*N+1)) (hT0i : Above (invert T0) (3*N+1))
    (hT : Above Tproper (3*p+d-3)) (hTi : Above (invert Tproper) (3*p+d-N-3)) :
    Above (clearedParticular f G P delta T0 Tproper) (3*p+2*d-3) ∧
      Above (invert (clearedParticular f G P delta T0 Tproper)) (3*p+2*d-2*N-3) := by
  let b := 3*p+2*d-3
  let bi := 3*p+2*d-2*N-3
  have hf2 : Above (f^2) (2*d) := by
    simpa only [Nat.cast_ofNat] using Above_pow hf 2
  have hfi2 : Above ((invert f)^2) (2*(d-N)) := by
    simpa only [Nat.cast_ofNat] using Above_pow hfi 2
  have hp2 : Above (P^2) (2*(3*N)) := by
    simpa only [Nat.cast_ofNat] using Above_pow hP 2
  have hpi2 : Above ((invert P)^2) (2*p) := by
    simpa only [Nat.cast_ofNat] using Above_pow hPi 2
  have hg2 : Above (G^2) (2*(p+N+d-1)) := by
    simpa only [Nat.cast_ofNat] using Above_pow hG 2
  have hgi2 : Above ((invert G)^2) (2*p) := by
    simpa only [Nat.cast_ofNat] using Above_pow hGi 2
  have h0 : Above (6*f^2*T0) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hf2 (6 : K)) hT0) (by dsimp only [b]; omega)
  have h1 : Above (3*f^2*P^2) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hf2 (3 : K)) hp2) (by dsimp only [b]; omega)
  have h2 : Above (3*G^2) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_C_mul hg2 (3 : K)) (by dsimp only [b]; omega)
  have h3 : Above (6*f*G*P) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_mul (Above_C_mul hf (6 : K)) hG) hP)
        (by dsimp only [b]; omega)
  have h4 : Above (6*G*delta) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hG (6 : K)) hdelta) (by dsimp only [b]; omega)
  have h5 : Above (2*f*Tproper) b := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hf (2 : K)) hT) (by dsimp only [b]; omega)
  have hi0 : Above (6*(invert f)^2*invert T0) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hfi2 (6 : K)) hT0i) (by dsimp only [bi]; omega)
  have hi1 : Above (3*(invert f)^2*(invert P)^2) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hfi2 (3 : K)) hpi2) (by dsimp only [bi]; omega)
  have hi2 : Above (3*(invert G)^2) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_C_mul hgi2 (3 : K)) (by dsimp only [bi]; omega)
  have hi3 : Above (6*invert f*invert G*invert P) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_mul (Above_C_mul hfi (6 : K)) hGi) hPi)
        (by dsimp only [bi]; omega)
  have hi4 : Above (6*invert G*invert delta) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hGi (6 : K)) hdeltai) (by dsimp only [bi]; omega)
  have hi5 : Above (2*invert f*invert Tproper) bi := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hfi (2 : K)) hTi) (by dsimp only [bi]; omega)
  constructor
  · exact above_add_same b _ _ (above_add_same b _ _ (above_sub_same b _ _
      (above_sub_same b _ _ (above_sub_same b _ _ h0 h1) h2) h3) h4) h5
  · simpa only [clearedParticular,map_add,map_sub,map_mul,map_pow,map_ofNat] using
      above_add_same bi _ _ (above_add_same bi _ _ (above_sub_same bi _ _
        (above_sub_same bi _ _ (above_sub_same bi _ _ hi0 hi1) hi2) hi3) hi4) hi5

theorem actual_native_cleared_numerator_bounds (hp : 19≤p) :
    Above (actualNativeClearedNumerator p hp) (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-3) ∧
      Above (invert (actualNativeClearedNumerator p hp))
        (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-2*(((p-1)/2 : ℕ) : ℤ)-3) := by
  have hhalf : 2*(((p-1)/2 : ℕ) : ℤ)+1=(p : ℤ) := by
    exact_mod_cast (WPFiniteWSource.half_exponent p hp).symm
  have hdn : 3*((p/6 : ℕ) : ℤ)≤(((p-1)/2 : ℕ) : ℤ) := by omega
  have hf := actual_low_F_bounds p hp
  have hg := actual_native_G_bounds p hp
  have hpairs := descendedP_bounds (K:=ZMod p) p hp
  have hd := actual_reflection_defect_bounds p hp
  have h0 := actual_UV_zero_branch_bounds p hp
  have ht := actual_whole_proper_particular_bounds p hp
  have he := cleared_particular_bounds (p : ℤ) (((p-1)/2 : ℕ) : ℤ)
    (3*((p/6 : ℕ) : ℤ)) (by omega) hhalf (by omega) hdn
    _ _ _ _ _ _ hf.1 hf.2 hg.1 hg.2 hpairs.1 hpairs.2 hd.1 hd.2 h0.1 h0.2 ht.1 ht.2
  simpa only [actualNativeClearedNumerator,show 2*(3*((p/6 : ℕ) : ℤ))=6*((p/6 : ℕ) : ℤ) by ring]
    using he

theorem actual_native_balanced_difference_bounds (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    Above (actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp)
      (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-3) ∧
      Above (invert (actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp))
        (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-2*(((p-1)/2 : ℕ) : ℤ)-3) := by
  have hn : 2*(((p-1)/2 : ℕ) : ℤ)+1=(p : ℤ) := by
    exact_mod_cast (WPFiniteWSource.half_exponent p hp).symm
  have hf := actual_low_F_bounds p hp
  have hQ := actual_native_cleared_numerator_bounds p hp
  have hE : Above (actualBalancedField p hp) (4*(((p-1)/2 : ℕ) : ℤ)+1) := by
    intro j hj
    exact actual_balanced_support_field p hp j (Or.inr hj)
  have hEi : Above (invert (actualBalancedField p hp))
      (2*(((p-1)/2 : ℕ) : ℤ)+3*((p/6 : ℕ) : ℤ)+1) := by
    intro j hj
    rw [invert_apply]
    exact actual_balanced_support_field p hp (-j) (Or.inl (by omega))
  have hFE : Above (6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      actualBalancedField p hp) (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-3) := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hf.1 (6 : ZMod p)) hE) (by omega)
  have hFEi : Above (6*invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      invert (actualBalancedField p hp))
        (3*(p : ℤ)+6*((p/6 : ℕ) : ℤ)-2*(((p-1)/2 : ℕ) : ℤ)-3) := by
    simpa only [map_ofNat] using
      Above_mono (Above_mul (Above_C_mul hf.2 (6 : ZMod p)) hEi) (by omega)
  constructor
  · exact above_sub_same _ _ _ hQ.1 hFE
  · simpa only [map_sub,map_mul,map_ofNat] using above_sub_same _ _ _ hQ.2 hFEi

end WPFieldAssembly.SourceClosureBalancedNativeSupport
