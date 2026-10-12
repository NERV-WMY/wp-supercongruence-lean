import WPFieldAssembly.SourceClosurePeriodTransport
import WPFieldAssembly.SourceClosureBalancedNativeBranch
import WPFieldAssembly.SourceClosureLogInversion

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUniversalLog WPFieldAssembly.SourceClosureLogInversion
  WPFieldAssembly.SourceClosureUVSupport WPFieldAssembly.SourceClosureSigmaActualVS
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeAlgebra
  WPFieldAssembly.SourceClosureLaurentBranchJets WPFieldAssembly.SourceClosureLaurentBounds

namespace WPFieldAssembly.SourceClosureBalancedNativeReciprocal

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem original_Jab_reflection (hp : 19≤p) :
    invert (originalJa p+originalJb p : (ZMod p)[T;T⁻¹])=originalJa p+originalJb p := by
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have ha : (1/4 : ZMod p)≠0 := div_ne_zero one_ne_zero h4
  have h4p : (4 : ZMod p)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : ZMod p)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have htp : (T (p : ℤ)*T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hca : LaurentPolynomial.C (1/4 : ZMod p)*LaurentPolynomial.C (4 : ZMod p)=1 := by
    rw [←map_mul,one_div_mul_cancel h4,map_one]
  simp only [originalJa,originalJb,map_add,map_mul,map_sub,invert_C,invert_T,neg_neg,
    scaledLog_invert p 4 h4,scaledLog_invert p (1/4) ha,h4p,hap,
    show (4 : ZMod p)⁻¹=1/4 by rw [one_div],
    show (1/4 : ZMod p)⁻¹=4 by simp only [one_div,inv_inv]]
  linear_combination
    -LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
      (LaurentPolynomial.C (4 : ZMod p)*scaledLog p (1/4)+
        LaurentPolynomial.C (1/4 : ZMod p)*scaledLog p 4)*htp+
    LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*T (-(p : ℤ))*
      (scaledLog p 4+scaledLog p (1/4))*hca

theorem actual_UV_reflection (hp : 19≤p) : invert (actualUV p hp)=actualUV p hp := by
  have hu : invert (descendedUcan p : (ZMod p)[T;T⁻¹])=descendedUcan p := by
    simp only [descendedUcan,map_sub,map_mul,invert_C,originalK0_reflection,
      originalHsym_symmetric,original_Jab_reflection p hp,originalJ2log_invert p hp]
  simp only [actualUV,descendedU,map_sub,invert_C,hu,actualVSField_reflection p hp]

theorem actual_UV_zero_branch_reflection (hp : 19≤p) :
    invert (actualNativeUVZeroBranch p hp)=actualNativeUVZeroBranch p hp := by
  simp only [actualNativeUVZeroBranch,map_sub,invert_C,actual_UV_reflection p hp]

theorem actual_whole_proper_weighted_reflection (hp : 19≤p) :
    T (((p-1)/2 : ℕ) : ℤ)*invert (actualWholeProperParticular p hp)=
      actualWholeProperParticular p hp := by
  have hi (L : (ZMod p)[T;T⁻¹]) : invert (invert L)=L :=
    LaurentPolynomial.involutive_invert L
  have ht : (T (((p-1)/2 : ℕ) : ℤ)*T (-(((p-1)/2 : ℕ) : ℤ)) :
      (ZMod p)[T;T⁻¹])=1 := by rw [←T_add,add_neg_cancel,T_zero]
  simp only [actualWholeProperParticular,map_add,map_mul,invert_T,hi]
  linear_combination actualLocalProperParticular p hp*ht

/-- Weight two reflects the entire cleared numerator, including its defect term. -/
theorem cleared_particular_weighted_reflection {K : Type*} [Field K]
    (phi f G P delta T0 Tproper : K[T;T⁻¹])
    (hf : f=phi*invert f) (h0 : invert T0=T0) :
    phi^2*invert (clearedParticular f G P delta T0 Tproper)=
      clearedParticular f (phi*invert G) (invert P) (phi*invert delta) T0
        (phi*invert Tproper) := by
  simp only [clearedParticular,map_add,map_sub,map_mul,map_pow,map_ofNat,h0]
  linear_combination
    -((f+phi*invert f)*(6*T0-3*(invert P)^2)-
      6*phi*invert G*invert P+2*phi*invert Tproper)*hf

theorem actual_cleared_numerator_weighted_reflection (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let S := coefficientMap (residueHom p) (comparisonIntegral p)
    let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
    T (((p-1)/2 : ℕ) : ℤ)^2*invert (actualNativeClearedNumerator p hp)=
      actualNativeClearedNumerator p hp+6*f*S*delta := by
  let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let G := coefficientMap (residueHom p) (nativeProperGIntegral p hp)
  let S := coefficientMap (residueHom p) (comparisonIntegral p)
  let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
  have hP : invert (SourceClosureUVFieldTransport.descendedP p : (ZMod p)[T;T⁻¹])=
      S-SourceClosureUVFieldTransport.descendedP p := by
    have he := descendedP_actual_comparison (K:=ZMod p) p hp
    rw [←comparisonIntegral_field p hp] at he
    linear_combination he
  have hG : phi*invert G=-f*S-G := by
    have he := actual_native_seed_field p hp
    simp only [nativeProperHIntegral,map_mul,coefficientMap_T,coefficientMap_invert] at he
    change G+phi*invert G+f*S=0 at he
    linear_combination he
  have hd := actual_defect_weighted_anti_field p hp
  have ht := actual_whole_proper_weighted_reflection p hp
  have hr := cleared_particular_weighted_reflection phi f G
    (SourceClosureUVFieldTransport.descendedP p) delta (actualNativeUVZeroBranch p hp)
    (actualWholeProperParticular p hp) (actual_low_F_weighted_reflection p hp)
    (actual_UV_zero_branch_reflection p hp)
  rw [hG,hP,hd,ht,native_cleared_reflected_identity] at hr
  exact hr

theorem actual_balanced_weighted_reflection_field (hp : 19≤p) :
    let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
    let S := coefficientMap (residueHom p) (comparisonIntegral p)
    T (((p-1)/2 : ℕ) : ℤ)*invert (actualBalancedField p hp)=
      actualBalancedField p hp+delta*S := by
  have he := congrArg (coefficientMap (residueHom p)) (actual_balanced_quotient_reflection p hp)
  simpa only [map_add,map_mul,coefficientMap_T,coefficientMap_invert,actualBalancedField] using he

theorem actual_difference_weighted_reflection (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    T (((p-1)/2 : ℕ) : ℤ)^2*
      invert (actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp)=
        actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp := by
  let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let S := coefficientMap (residueHom p) (comparisonIntegral p)
  let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
  have hQ := actual_cleared_numerator_weighted_reflection p hp
  have hE := actual_balanced_weighted_reflection_field p hp
  have hf := actual_low_F_weighted_reflection p hp
  change phi^2*invert (actualNativeClearedNumerator p hp)=
    actualNativeClearedNumerator p hp+6*f*S*delta at hQ
  change phi*invert (actualBalancedField p hp)=actualBalancedField p hp+delta*S at hE
  change f=phi*invert f at hf
  change phi^2*invert (actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp)=_
  simp only [map_sub,map_mul,map_ofNat]
  linear_combination hQ-6*phi*invert f*hE+6*(actualBalancedField p hp+delta*S)*hf

/-- The actual quotient is reciprocal, with both positive and negative extreme slots retained. -/
theorem actual_native_ratio_reciprocal (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R) : invert R=R := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let phi : (ZMod p)[T;T⁻¹] := T (((p-1)/2 : ℕ) : ℤ)
  let M := actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp
  have hdegree := actual_balanced_multiplier_exact_degree p hp
  have hF : NativeChiFieldSource.halfPullbackField p hp≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hdegree
    omega
  have hf0 : f≠0 := by
    intro hz
    apply hF
    apply Polynomial.toLaurent_injective
    simpa only [map_zero] using hz
  have hf := actual_low_F_weighted_reflection p hp
  change f=phi*invert f at hf
  change M=f^2*R at hfactor
  have heM := actual_difference_weighted_reflection p hp
  change phi^2*invert M=M at heM
  have he : f^2*invert R=f^2*R := by
    calc
      f^2*invert R=(phi*invert f)^2*invert R := by rw [←hf]
      _=phi^2*invert (f^2*R) := by simp only [map_mul,map_pow]; ring
      _=phi^2*invert M := by rw [←hfactor]
      _=M := heM
      _=f^2*R := hfactor
  exact mul_left_cancel₀ (pow_ne_zero 2 hf0) he

theorem reciprocal_coeff_pair {K : Type*} [Field K] (R : K[T;T⁻¹])
    (hR : invert R=R) (j : ℤ) : R.coeff (-j)=R.coeff j := by
  have he := congrArg (fun L : K[T;T⁻¹] => L.coeff j) hR
  simpa only [invert_apply] using he

/-- The SAME actual quotient has three reciprocal coefficients, with its full branch value. -/
theorem actual_native_reciprocal_three_slots (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    ∃ R : (ZMod p)[T;T⁻¹], actualNativeClearedNumerator p hp-
        6*f*actualBalancedField p hp=f^2*R ∧
      R=LaurentPolynomial.C (R.coeff 0)+
        LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
        LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ))) ∧
      branchEval R=12*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
        9*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  obtain ⟨R,hfactor,hD,htop,hbot⟩ :=
    WPFieldAssembly.SourceClosureBalancedNativeKernel.actual_native_balanced_ratio_full_band p hp
  have hr := actual_native_ratio_reciprocal p hp R hfactor
  have h1 := reciprocal_coeff_pair R hr (p : ℤ)
  have h2 := reciprocal_coeff_pair R hr (2*(p : ℤ))
  have h2' : R.coeff (-2*(p : ℤ))=R.coeff (2*(p : ℤ)) := by
    simpa only [neg_mul] using h2
  have he := derivative_kernel_five_expansion p hp R hD htop hbot
  rw [h1,h2'] at he
  refine ⟨R,hfactor,?_,SourceClosureBalancedNativeBranch.actual_native_ratio_branch_value p hp R hfactor⟩
  linear_combination he

theorem actual_native_reciprocal_branch_constraint (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R)
    (hR : R=LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    R.coeff 0-2*R.coeff (p : ℤ)+2*R.coeff (2*(p : ℤ))=
      12*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
        9*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpval : (-1 : ZMod p)^p=-1 := by rw [hpodd.neg_pow,one_pow]
  have ht : branchEval (T (p : ℤ) : (ZMod p)[T;T⁻¹])=-1 := by
    simpa only [branchEval,LaurentPolynomial.eval₂_T_n,Units.val_pow_eq_pow_val,
      Units.val_neg,Units.val_one] using hpval
  have hti : branchEval (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=-1 := by
    have he := congrArg (branchEval (K:=ZMod p)) (invert_T (R:=ZMod p) (p : ℤ))
    rw [branch_eval_invert,ht] at he
    exact he.symm
  have htwo : (T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=T (p : ℤ)^2 := by
    rw [T_pow]
    congr 1
  have ht2 : branchEval (T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=1 := by
    rw [htwo,map_pow,ht]
    norm_num
  have hti2 : branchEval (T (-2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=1 := by
    have he := congrArg (branchEval (K:=ZMod p)) (invert_T (R:=ZMod p) (2*(p : ℤ)))
    rw [branch_eval_invert,ht2] at he
    simpa only [neg_mul] using he.symm
  have he := congrArg (branchEval (K:=ZMod p)) hR
  simp only [map_add,map_mul,branchEval,LaurentPolynomial.eval₂_C,RingHom.id_apply] at he
  change branchEval R=R.coeff 0+R.coeff (p : ℤ)*
    (branchEval (T (p : ℤ))+branchEval (T (-(p : ℤ))))+
      R.coeff (2*(p : ℤ))*(branchEval (T (2*(p : ℤ)))+branchEval (T (-2*(p : ℤ)))) at he
  rw [ht,hti,ht2,hti2] at he
  have hv := SourceClosureBalancedNativeBranch.actual_native_ratio_branch_value p hp R hfactor
  linear_combination hv-he

end WPFieldAssembly.SourceClosureBalancedNativeReciprocal
