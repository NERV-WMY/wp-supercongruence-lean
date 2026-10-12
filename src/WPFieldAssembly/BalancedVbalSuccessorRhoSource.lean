import WPFieldAssembly.BalancedVbalSuccessorProperSquareTrace
import WPFieldAssembly.BalancedVbalSuccessorCoupledJResidue
import WPFieldAssembly.ActualBpairGreen

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPFiniteLaurentDifferential
  WPPIntegralReduction

namespace WPFieldAssembly.BalancedVbalSuccessorRhoSource

open ActualKwFieldTrace ActualIntegralGreenTrace ActualCommonTraceReduction
  ActualBpairLowHLocalPole ActualBpairContraction ActualSimplePoleResidue
  SourceClosureBalancedOriginalDensity SourceClosureBalancedNativeFactorization
  SourceClosureCommonWholeSource SourceClosureSigmaNativeKernel
  SourceClosureHFNativeTransport SourceClosureTraceOrigin SourceClosureTraceReduction
  SourceClosureUVPhaseTrace BalancedVbalSuccessorCoupledSource
  BalancedVbalSuccessorCoupledJResidue NativeJointSuccessorJSeries

set_option maxHeartbeats 2000000
variable (p : ℕ) [Fact p.Prime]

/- Every public source below uses the original density and existing literal
Jcoupled consumer. HF retains its full successor pole until its actual native
attachment is checked. The two actual period rows are retained separately.
Identification with the entire native Wneed is an open bridge, not a premise. -/

/-- The full original low density splits before any trace or slot is selected. -/
theorem actual_low_density_full_split (hp : 19≤p) :
    actualOriginalLowDensity p hp=
      3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp+
      ((3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
        (LaurentPolynomial.C (1/6 : ZMod p)*
          (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
              (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
            T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))))+
      actualReflectedSigmaWeightedNumerator p hp-
      (LaurentPoleField.fieldAbar p).toLaurent^p*(dlogQNumerator*periodField p hp) := by
  rw [actualOriginalLowDensity,actual_proper_low_whole_source p hp]
  unfold actualProperSquaresNumerator actualReflectedSigmaWeightedNumerator
  ring

/-- Proper squares and the literal reflected-Sigma/proper/J consumer stay coupled.
The original HF and period are still carried at their original denominators. -/
theorem actual_low_density_original_coupled_source (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp)+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)-
      (2/3 : ZMod p)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125+
      (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp)-
      (2/3 : ZMod p)*residueHom p (periodCarryIntegral p hp)+
      originPole (actualJjoint p hp) := by
  have hd := congrArg (LaurentPoleField.fieldTrace p (p+1))
    (actual_low_density_full_split p hp)
  rw [map_sub,map_add,map_add] at hd
  have hperiod : LaurentPoleField.fieldTrace p (p+1)
      ((LaurentPoleField.fieldAbar p).toLaurent^p*(dlogQNumerator*periodField p hp))=
        residueHom p (periodCarryIntegral p hp) := by
    rw [show p+1=1+p by omega,LaurentPoleField.fieldTrace_cleared_pow p 1 p hp,
      ←periodTrace_field_source p hp]
  rw [hperiod] at hd
  have hs := BalancedVbalSuccessorProperSquareTrace.actual_proper_squares_density_trace p hp
  change (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
    ((3*(R : (ZMod p)[T;T⁻¹])^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
      (LaurentPolynomial.C (1/6 : ZMod p)*
        (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
            (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
          T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))))=_ at hs
  have hj := actual_original_coupled_residue_identity p hp
  linear_combination (2/3 : ZMod p)*hd+hs+hj

/-- The same common+balanced-period consumer reaches the actual coupled pole.
All original homogeneous and beta corrections remain present. -/
theorem actual_common_balanced_period_coupled_source (hp : 19≤p) :
    (2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)-
      (2/3 : ZMod p)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      (2/3 : ZMod p)*originalWeightedFieldTrace p
        (SourceClosureActualUVAttachment.actualUV p hp+
          SourceClosureBalancedNativeBetaTransport.originalDescendedZ p)-
      (66/25 : ZMod p)*(SourceClosureActualUVAttachment.actualMu p hp+
        SourceClosureBalancedNativeNormalization.actualBalancedBranchB p)-
      (207/4 : ZMod p)*SourceClosureBalancedNativeBetaIdentification.actualOriginalBeta p+
      8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125+
      (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp)-
      (2/3 : ZMod p)*residueHom p (periodCarryIntegral p hp)+
      originPole (actualJjoint p hp) := by
  have hw := actual_whole_trace_original_density p hp
  have hl := actual_low_density_original_coupled_source p hp
  linear_combination hw+hl

/-- Anti-reflection and the full p-divided period give exactly both IR63 period rows. -/
theorem actual_period_simple_origin_rows (hp : 19≤p) :
    -(2/3 : ZMod p)*residueHom p (periodCarryIntegral p hp)=
      originPole
        ((33-12*T 1)*
          ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
            (ActualFirstGreen.CB p).toLaurent*
              (LaurentPolynomial.C (-10/9 : ZMod p)*
                (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p))))) := by
  let A := (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent
  have hA : (LaurentPoleField.fieldAbar p).toLaurent=A := by
    dsimp only [A]
    congr 1
    unfold LaurentPoleField.fieldAbar WPFiniteZSource.Abar
    ring
  have ht : (T (2*(p : ℤ))*T (-2)^p : (ZMod p)[T;T⁻¹])=1 := by
    have hpow : (T (-2) : (ZMod p)[T;T⁻¹])^p=T (-(2*(p : ℤ))) := by
      rw [T_pow]
      congr 1
      ring
    rw [hpow,←T_add,add_neg_cancel,T_zero]
  have hleft : LaurentPolynomial.C (2/3 : ZMod p)*T (2*(p : ℤ))*
      invert ((LaurentPoleField.fieldAbar p).toLaurent^p*
        (dlogQNumerator*periodField p hp))=
      A^p*(LaurentPolynomial.C (2/3 : ZMod p)*invert (dlogQNumerator*periodField p hp)) := by
    rw [hA]
    dsimp only [A]
    simp only [map_mul,map_pow,WPFiniteZSource.invert_Abar,mul_pow]
    linear_combination LaurentPolynomial.C (2/3 : ZMod p)*
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent^p*
        (invert dlogQNumerator*invert (periodField p hp))*ht
  have hpRows := actual_period_native_rows p hp
  rw [hleft] at hpRows
  have he : LaurentPolynomial.C (2/3 : ZMod p)*invert (dlogQNumerator*periodField p hp)=
      (33-12*T 1)*
        ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
          (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
            (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
              LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
          (ActualFirstGreen.CB p).toLaurent*
            (LaurentPolynomial.C (-10/9 : ZMod p)*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))) := by
    apply mul_left_cancel₀ (pow_ne_zero p (WPFiniteZSource.Abar_nonzero (K:=ZMod p) p hp))
    dsimp only [A] at hpRows
    linear_combination hpRows
  have hr := congrArg originPole he
  rw [originPole_C_mul] at hr
  rw [periodTrace_field_source p hp,fieldTrace_one_native_origin p hp]
  linear_combination hr

/-- The same HF and period retain the entire successor pole and both period rows. -/
theorem actual_original_HF_period_origin_pair (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp)-
      (2/3 : ZMod p)*residueHom p (periodCarryIntegral p hp)=
      originTrace p (p+1) (nativeHFOriginNumerator (K:=ZMod p) p hp)+
      originPole
        ((33-12*T 1)*
          ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
            (ActualFirstGreen.CB p).toLaurent*
              (LaurentPolynomial.C (-10/9 : ZMod p)*
                (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p))))) := by
  have hH := actual_HF_infinity_origin_numerator (K:=ZMod p) p hp
  rw [ActualBpairContraction.phi_self,ActualBpairContraction.coefficientMap_self] at hH
  have ho := congrArg (originTrace p (p+1)) hH
  rw [mul_assoc,originTrace_C_mul] at ho
  have hi := fieldTrace_successor_origin p
    (3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*actualOmegaHFNumerator p hp)
  have hpRows := actual_period_simple_origin_rows p hp
  linear_combination (2/3 : ZMod p)*hi+ho+hpRows

/-- This is the whole original proper/common/period consumer before the native Wneed bridge.
No HF contribution, period row, invisible source coefficient or original j term is assigned away. -/
theorem actual_common_balanced_period_native_coupled_source (hp : 19≤p) :
    (2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)-
      (2/3 : ZMod p)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      (2/3 : ZMod p)*originalWeightedFieldTrace p
        (SourceClosureActualUVAttachment.actualUV p hp+
          SourceClosureBalancedNativeBetaTransport.originalDescendedZ p)-
      (66/25 : ZMod p)*(SourceClosureActualUVAttachment.actualMu p hp+
        SourceClosureBalancedNativeNormalization.actualBalancedBranchB p)-
      (207/4 : ZMod p)*SourceClosureBalancedNativeBetaIdentification.actualOriginalBeta p+
      8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125+
      originTrace p (p+1) (nativeHFOriginNumerator (K:=ZMod p) p hp)+
      originPole
        ((33-12*T 1)*
          ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
            (ActualFirstGreen.CB p).toLaurent*
              (LaurentPolynomial.C (-10/9 : ZMod p)*
                (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))))+
      originPole (actualJjoint p hp) := by
  have hc := actual_common_balanced_period_coupled_source p hp
  have hpRows := actual_original_HF_period_origin_pair p hp
  linear_combination hc+hpRows

end WPFieldAssembly.BalancedVbalSuccessorRhoSource
