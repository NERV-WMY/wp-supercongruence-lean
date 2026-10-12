import WPFieldAssembly.SourceClosureBalancedHomogeneousTrace
import WPFieldAssembly.SourceClosureBalancedTraceEuler

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualCommonTraceReduction
  WPFieldAssembly.ActualCommonFieldIBP WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.SourceClosureCommonWholeSource
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
  WPFieldAssembly.SourceClosureBalancedNativeNormalization
  WPFieldAssembly.SourceClosureBalancedHomogeneousTrace
  WPFieldAssembly.SourceClosureBalancedTraceEuler
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWholeContraction

namespace WPFieldAssembly.SourceClosureBalancedOriginalDensity

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- Both proper square halves and the entire reflected Sigma product remain together. -/
noncomputable def actualProperLowNumerator (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
    (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
    T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p)-
    2*coefficientMap (residueHom p) (comparisonIntegral p)*
      (T (((p-1)/2 : ℕ) : ℤ)*invert (actualSigmaPullback p hp).toLaurent)

theorem actual_balanced_field_original_Z (hp : 19≤p) :
    actualBalancedField p hp=
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
        (actualNativeUVZeroBranch p hp+originalDescendedZ p-
          LaurentPolynomial.C (1/6 : ZMod p)*actualNativeHomogeneousR p hp)+
      LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let A := actualNativeUVZeroBranch p hp+originalDescendedZ p
  have hd := actual_balanced_multiplier_exact_degree p hp
  have hP : NativeChiFieldSource.halfPullbackField p hp≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hd
    omega
  have hf : f≠0 := by
    intro hz
    apply hP
    apply Polynomial.toLaurent_injective
    simpa only [map_zero] using hz
  have h6 : (6 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 6
    (by omega) (by omega)
  have hu : (6 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/6 : ZMod p)=1 := by
    change LaurentPolynomial.C (6 : ZMod p)*LaurentPolynomial.C (1/6 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h6,map_one]
  have hZ := actual_cleared_original_Z_decomposition p hp
  have hM := actual_original_homogeneous_normalization p hp
  apply mul_left_cancel₀ hf
  dsimp only [actualProperLowNumerator]
  linear_combination LaurentPolynomial.C (1/6 : ZMod p)*hZ-
    LaurentPolynomial.C (1/6 : ZMod p)*hM-(f*actualBalancedField p hp-f^2*A)*hu

theorem actual_original_Z_derivative (hp : 19≤p) :
    D (originalDescendedZ p : (ZMod p)[T;T⁻¹])=
      WPFiniteZSource.R p*(-descendedP p+LaurentPolynomial.C (1/3 : ZMod p)*
        ((WPFiniteLVSource.LV p).toLaurent-T (-(((p-1)/2 : ℕ) : ℤ))*
          invert (WPFiniteLVSource.LV p).toLaurent))+
      LaurentPolynomial.C (1/2 : ZMod p)*T (-1)*descendedP p := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  rw [originalDescendedZ,neg_mul,map_add,map_neg,D_half_square _ h2,
    SourceClosureBalancedUVSource.actual_descendedP_derivative p hp,
    WPFiniteZSource.GJ_derivative p hp]
  ring

/-- The actual homogeneous normal form is invisible to the full derivative. -/
theorem actual_homogeneous_R_derivative_zero (hp : 19≤p) :
    D (actualNativeHomogeneousR p hp)=0 := by
  have hT (n : ℤ) : D (T ((p : ℤ)*n) : (ZMod p)[T;T⁻¹])=0 := by
    rw [show (T ((p : ℤ)*n) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1 : ZMod p)*T ((p : ℤ)*n) by simp,D_monomial]
    simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,
      mul_zero,map_zero]
  have h1 : D (T (p : ℤ) : (ZMod p)[T;T⁻¹])=0 := by simpa only [mul_one] using hT 1
  have hn1 : D (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=0 := by
    simpa only [mul_neg,mul_one] using hT (-1)
  have h2 : D (T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=0 := by
    simpa only [mul_comm] using hT 2
  have hn2 : D (T (-2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=0 := by
    simpa only [mul_neg,neg_mul,mul_comm] using hT (-2)
  unfold actualNativeHomogeneousR
  simp only [map_add,D_C,D_C_mul,h1,hn1,h2,hn2,mul_zero,add_zero]

theorem actual_low_weight_zero_branch (hp : 19≤p) :
    actualLowWeightedTrace p hp (actualNativeUVZeroBranch p hp)=
      actualLowWeightedTrace p hp (actualUV p hp) := by
  let c := LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp)
  have hc : actualLowWeightedTrace p hp (LaurentPolynomial.C c)=0 := by
    rw [actual_low_weight_invisible p hp _ (D_C c),weighted_constant_zero p hp]
  unfold actualNativeUVZeroBranch
  change originalWeightedFieldTrace p
    (T (-(((p-1)/2 : ℕ) : ℤ))*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      (actualUV p hp-LaurentPolynomial.C c))=actualLowWeightedTrace p hp (actualUV p hp)
  rw [mul_sub,weighted_sub]
  change actualLowWeightedTrace p hp (actualUV p hp)-
    actualLowWeightedTrace p hp (LaurentPolynomial.C c)=_
  rw [hc,sub_zero]

theorem actual_balanced_trace_original_Z (hp : 19≤p) :
    residueHom p (balancedTraceIntegral p hp)=
      originalWeightedFieldTrace p (actualUV p hp)+
      kwFieldTrace p (D (commonHField p)*actualUV p hp)+
      originalWeightedFieldTrace p (originalDescendedZ p)+
      kwFieldTrace p (D (commonHField p)*originalDescendedZ p)-
      (1/6 : ZMod p)*originalWeightedFieldTrace p (actualNativeHomogeneousR p hp)+
      LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ))*
          (LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp)) := by
  rw [balancedTrace_field_source p hp]
  change LaurentPoleField.fieldTrace p (p+1)
    (3*(R : (ZMod p)[T;T⁻¹])^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ))*
      actualBalancedField p hp)=_
  rw [actual_balanced_field_original_Z p hp]
  have he : (3*(R : (ZMod p)[T;T⁻¹])^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
      ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
        (actualNativeUVZeroBranch p hp+originalDescendedZ p-
          LaurentPolynomial.C (1/6 : ZMod p)*actualNativeHomogeneousR p hp)+
      LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp)=
      (3*R^p*dlogQNumerator)*(T (-(((p-1)/2 : ℕ) : ℤ))*
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualNativeUVZeroBranch p hp)+
      (3*R^p*dlogQNumerator)*(T (-(((p-1)/2 : ℕ) : ℤ))*
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent*originalDescendedZ p)-
      LaurentPolynomial.C (1/6 : ZMod p)*((3*R^p*dlogQNumerator)*
        (T (-(((p-1)/2 : ℕ) : ℤ))*
          (NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualNativeHomogeneousR p hp))+
      (3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
        (LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp) := by ring
  rw [he,map_add,map_sub,map_add,fieldTrace_C_mul]
  change actualLowWeightedTrace p hp (actualNativeUVZeroBranch p hp)+
    actualLowWeightedTrace p hp (originalDescendedZ p)-
    (1/6 : ZMod p)*actualLowWeightedTrace p hp (actualNativeHomogeneousR p hp)+_= _
  rw [actual_low_weight_zero_branch p hp,
    actual_low_weight_euler p hp (actualUV p hp),
    actual_low_weight_euler p hp (originalDescendedZ p),
    actual_low_weight_invisible p hp _ (actual_homogeneous_R_derivative_zero p hp)]
  ring

/-- The full original HF source before its three load-bearing low contractions. -/
noncomputable def actualOmegaHFNumerator (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  delta*comparisonField p-(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*R*
    (SourceClosureUVFieldTransport.descendedBgamma p hp+D (originalDescendedZ p))

/-- The low density retains both whole proper square halves, reflected Sigma and actual period. -/
noncomputable def actualOriginalLowDensity (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  3*R^(p-1)*commonHField p*actualOmegaHFNumerator p hp+
    (3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
      (LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp)-
    (LaurentPoleField.fieldAbar p).toLaurent^p*(dlogQNumerator*periodField p hp)

/-- This attaches the actual common and Z integration by parts to one original HF numerator. -/
theorem actual_common_original_HF_source (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)+
      kwFieldTrace p (D (commonHField p)*actualUV p hp)+
      kwFieldTrace p (D (commonHField p)*originalDescendedZ p)=
        LaurentPoleField.fieldTrace p (p+1)
          (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp) := by
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent=
      (LaurentPoleField.fieldAbar p).toLaurent := by
    congr 1
    unfold WPFiniteZSource.Abar LaurentPoleField.fieldAbar
    ring
  have hRp : (R : (ZMod p)[T;T⁻¹])^(p-1)*R=R^p := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤p)]
  have he : 3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp=
      3*(R^(p-1)*delta*commonHField p*comparisonField p)-
      (LaurentPoleField.fieldAbar p).toLaurent*
        (3*(R^(p-1)*commonHField p*actualPositiveB p hp))-
      (LaurentPoleField.fieldAbar p).toLaurent*
        (3*R^p*(commonHField p*D (originalDescendedZ p))) := by
    unfold actualOmegaHFNumerator actualPositiveB
    rw [hA]
    linear_combination
      -3*(LaurentPoleField.fieldAbar p).toLaurent*commonHField p*D (originalDescendedZ p)*hRp
  have ht := congrArg (LaurentPoleField.fieldTrace p (p+1)) he
  rw [map_sub,map_sub,fieldTrace_three_mul,
    LaurentPoleField.fieldTrace_cleared p p hp,
    LaurentPoleField.fieldTrace_cleared p p hp,fieldTrace_three_mul] at ht
  have hc := actualUV_common_trace_row p hp
  have hz := kwFieldTrace_IBP p hp (commonHField p) (originalDescendedZ p)
  change _=3*LaurentPoleField.fieldTrace p (p+1)
    (R^(p-1)*delta*commonHField p*comparisonField p)-
    3*LaurentPoleField.fieldTrace p p (R^(p-1)*commonHField p*actualPositiveB p hp)-
    kwFieldTrace p (commonHField p*D (originalDescendedZ p)) at ht
  linear_combination hc+hz-ht

/-- The SAME actual common+balanced-period source retains its original low density,
and has no caller source, derivative, endpoint, beta or trace-value premise. -/
theorem actual_whole_trace_original_density (hp : 19≤p) :
    (2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))=
      (2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp+originalDescendedZ p)-
      (66/25 : ZMod p)*(actualMu p hp+actualBalancedBranchB p)-
      (207/4 : ZMod p)*actualOriginalBeta p+
      (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp) := by
  have hb := actual_balanced_trace_original_Z p hp
  have hc := actual_common_original_HF_source p hp
  have hn := actual_homogeneous_trace_correction p hp
  have hpole := periodTrace_field_source p hp
  have hraise := LaurentPoleField.fieldTrace_cleared_pow p 1 p hp
    (dlogQNumerator*periodField p hp)
  rw [show 1+p=p+1 by omega] at hraise
  have hd : LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp)=
      LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp)+
      LaurentPoleField.fieldTrace p (p+1)
        ((3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
          (LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp))-
      residueHom p (periodCarryIntegral p hp) := by
    rw [actualOriginalLowDensity,map_sub,map_add,hraise,←hpole]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h6 : (6 : ZMod p)≠0 := by
    rw [show (6 : ZMod p)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have h9 : (9 : ZMod p)≠0 := by
    rw [show (9 : ZMod p)=3^2 by ring]
    exact pow_ne_zero _ h3
  rw [weighted_add]
  linear_combination (norm := (field_simp [h2,h3,h6,h9]; ring))
    (2/3 : ZMod p)*(hb+hc-hd)-hn

end WPFieldAssembly.SourceClosureBalancedOriginalDensity
