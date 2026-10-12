import WPFieldAssembly.SourceClosureWholeTraceCollection
import WPFieldAssembly.BalancedVbalSuccessorRhoSource
import WPFieldAssembly.BalancedVbalSuccessorRhoEvaluation
import WPFieldAssembly.NativeClosureWholeSource

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.BalancedVbalSuccessorDividedVbalConsumer

open ActualIntegralGreenTrace ActualSB101Trace ActualGreenCommonTrace
  ActualBalancedGreenTransfer ActualHFTransmutation ActualJointGreen
  ActualBalancedTrace ActualVbalCarry ActualEntropyFifth ActualWeightedF0Carry
  ActualComparisonKwAttachment ActualProperEndpointCarry ActualLogCCarry
  ActualBpairContraction ActualBpairLowHLocalPole ActualSimplePoleResidue ActualKwFieldTrace
  SourceClosureWholeTraceCollection SourceClosureCommonWholeSource
  SourceClosureBalancedOriginalDensity SourceClosureHFNativeTransport
  SourceClosureTraceOrigin BalancedVbalSuccessorRhoSource
  BalancedVbalSuccessorCoupledSource NativeJointSuccessorJSeries

set_option maxHeartbeats 2400000
variable (p : ℕ) [Fact p.Prime]

/-- The full original rational consumer is divided by p over Q before reduction.
Both common traces, the balanced quotient and the full period remain literal. -/
theorem actual_whole_consumer_rational_value (hp : 19≤p) :
    ((2*smallIntegralInverse p 3)*
      (vBalancedDividedIntegral p hp+commonSourceTraceIntegral p hp+
        balancedTraceIntegral p hp-periodCarryIntegral p hp)).val=
      (2/(3*(p : ℚ)))*
        (vBalancedQ p hp+(p : ℚ)*
          (kwTraceQ p (greenHAtQ p hp*actualSigmaQ p hp)+
            kwLogTraceQ p (greenHAtQ p hp*comparisonRational p hp)+
            xiTraceQ p (actualBalancedDividedQ p hp)-
            dlogQtrace
              (T (-(((p-1)/2 : ℕ) : ℤ))*lowReflectionDefectQ p hp*
                (finiteConicLogQ p).toLaurent))) := by
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change (2*(smallIntegralInverse p 3).val)*
    (vBalancedQ p hp/(p : ℚ)+
      (kwTraceQ p (greenHAtQ p hp*actualSigmaQ p hp)+
        kwLogTraceQ p (greenHAtQ p hp*comparisonRational p hp))+
      xiTraceQ p (actualBalancedDividedQ p hp)-
      dlogQtrace
        (T (-(((p-1)/2 : ℕ) : ℤ))*lowReflectionDefectQ p hp*
          (finiteConicLogQ p).toLaurent))=_
  rw [smallIntegralInverse_value p 3 (by omega) (by omega)]
  field_simp [hpq]
  ring

/-- The same integral consumer retains the complete rational first carry.
Its last term comes from the original p-squared numerator, before reduction. -/
theorem actual_whole_consumer_integral_carry (hp : 19≤p) :
    (2*smallIntegralInverse p 3)*
      (vBalancedDividedIntegral p hp+commonSourceTraceIntegral p hp+
        balancedTraceIntegral p hp-periodCarryIntegral p hp)=
      (2*smallIntegralInverse p 3)*
        (3*WPFiniteCarry.integralEvenLogEndpointCarry p hp-
          3*actualFifthCarryIntegral p-weightedF0CarryI p hp-
          comparisonKwCarryI p hp+3*endpointCarryIntegral p hp-
          2*endpointOriginIntegral p*logCDigitIntegral p-
          2*(p : integralRationals p)*endpointCarryIntegral p hp*logCDigitIntegral p+
          commonSourceTraceIntegral p hp+balancedTraceIntegral p hp-
          periodCarryIntegral p hp) := by
  rw [actual_vBalancedDividedIntegral p hp,vbalCarryI]

private theorem whole_consumer_residue (hp : 19≤p) :
    residueHom p
      ((2*smallIntegralInverse p 3)*
        (vBalancedDividedIntegral p hp+commonSourceTraceIntegral p hp+
          balancedTraceIntegral p hp-periodCarryIntegral p hp))=
      (2/3 : ZMod p)*(residueHom p (vBalancedDividedIntegral p hp)+
        residueHom p (commonSourceTraceIntegral p hp)+
        residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp)) := by
  simp only [map_mul,map_add,map_sub,map_ofNat,
    smallIntegralInverse_field p 3 (by omega) (by omega),Nat.cast_ofNat,div_eq_mul_inv]

variable {K : Type*} [Field K]

/-- Actual rational p-division and the original T5 pairing reach the complete finite alphabet.
The entire low density stays at its original successor pole, with no selected-slot premise. -/
theorem actual_whole_integral_finite_consumer [CharP K p] (hp : 19≤p)
    (f : ZMod p →+* K) (u w : K) (hu : u^2=1/5) (hw : w^2=3/11) :
    f (residueHom p
      ((2*smallIntegralInverse p 3)*
        (vBalancedDividedIntegral p hp+commonSourceTraceIntegral p hp+
          balancedTraceIntegral p hp-periodCarryIntegral p hp)))=
      ActualVbalFieldClosure.vbalMomentConsumer p u w+originalUVFiniteRemainder p u+
        SourceClosureNormalizedZFinite.normalizedZFiniteValue p u+
        (2/3 : K)*f (LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp)) := by
  have hf : f=ZMod.castHom (dvd_refl p) K := Subsingleton.elim _ _
  rw [whole_consumer_residue p hp,hf]
  exact actual_Vbal_whole_trace_collection p hp u w hu hw

/-- The SAME retained scalar consumer now includes its actual rational divided Vbal alphabet.
The original proper QO, inline Jcoupled, both period rows and whole HF all remain present.
This theorem does not compose or evaluate the native Wneed residue. -/
theorem actual_original_retained_divided_consumer [CharP K p] (hp : 19≤p)
    (f : ZMod p →+* K) (u w : K) (hu : u^2=1/5) (hw : w^2=3/11) :
    f ((2/3 : ZMod p)*(residueHom p (vBalancedDividedIntegral p hp)+
        residueHom p (commonSourceTraceIntegral p hp)+
        residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)-
      103*WPActualGaussBottom.fieldHarmonic p (p/6)^2/1000)-
      (2/3 : K)*f
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      ActualVbalFieldClosure.vbalMomentConsumer p u w+originalUVFiniteRemainder p u+
      SourceClosureNormalizedZFinite.normalizedZFiniteValue p u+
      f (8*WPActualGaussBottom.fieldHarmonic p (p/6)^2/125)-
      f (103*WPActualGaussBottom.fieldHarmonic p (p/6)^2/1000)+
      f (originTrace p (p+1) (nativeHFOriginNumerator (K:=ZMod p) p hp))+
      f (originPole
        ((33-12*T 1)*
          ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
            (ActualFirstGreen.CB p).toLaurent*
              (LaurentPolynomial.C (-10/9 : ZMod p)*
                (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p))))))+
      f (originPole (actualJjoint p hp)) := by
  have ht := actual_whole_integral_finite_consumer p hp f u w hu hw
  rw [whole_consumer_residue p hp] at ht
  have hl := congrArg f (actual_low_density_original_coupled_source p hp)
  have hr := congrArg f (actual_original_HF_period_origin_pair p hp)
  simp only [map_add,map_sub,map_mul,map_div₀,map_ofNat] at ht hl hr ⊢
  linear_combination ht+hl+hr

end WPFieldAssembly.BalancedVbalSuccessorDividedVbalConsumer

namespace WPFieldAssembly.BalancedVbalSuccessorRhoEvaluation

open WPActualChiSource ActualBpairContraction ActualThreePhase ActualGreenResidue
  ActualSimplePoleResidue SourceClosureCommonWholeSource SourceClosureHFNativeTransport
  NativeJointSuccessorWneedCore SourceClosureWholeTraceCollection

variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/-- The SAME rational divided Vbal and full rho consume T5 together, retaining
the original norm offset and the entire finite alphabet. -/
theorem actual_divided_Vbal_rho_joint_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=1/5) (hw : w^2=3/11) :
    φ (K:=K) p (actualDividedVbalScalar p hp)+
      originPole
        (coefficientMap (φ (K:=K) p) (wholeTraceProperNativeDensity p hp)-
          (actualWneedCoreCarrier p+
            (HpullK (K:=K) p).toLaurent*
              (nativeHFSigmaNumerator p+
                WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                  (4*T (-(p : ℤ))-11)*nativeHFBracket p u)))=
      ActualVbalFieldClosure.vbalMomentConsumer p u w+originalUVFiniteRemainder p u+
      SourceClosureNormalizedZFinite.normalizedZFiniteValue p u+
      (287/600 : K)*(WPFiniteNC122.h p)^2 := by
  have hr := actual_original_rho_full_alphabet (K:=K) p hp u hu
  have hv := ActualVbalFieldClosure.actual_vBalanced_T5_consumer (K:=K) p hp u w hu hw
  have hh : φ (K:=K) p (WPFiniteNC122.h p : ZMod p)=(WPFiniteNC122.h p : K) := by
    simp only [WPFiniteNC122.h,WPFiniteNC122.q,map_sub,map_mul,map_neg,
      map_div₀,map_intCast,map_ofNat]
  have hD : φ (K:=K) p (actualDividedVbalScalar p hp)=
      (2/3 : K)*φ (K:=K) p
        (WPPIntegralReduction.residueHom p
          (ActualIntegralGreenTrace.vBalancedDividedIntegral p hp))-
      103*(WPFiniteNC122.h p : K)^2/1000 := by
    unfold actualDividedVbalScalar
    rw [actual_harmonic_is_finite_h p hp]
    simp only [map_sub,map_mul,map_div₀,map_pow,map_ofNat,hh]
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h375 : (375 : K)≠0 := by
    rw [show (375 : K)=3*5^3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  have h600 : (600 : K)≠0 := by
    rw [show (600 : K)=2^3*3*5^2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) (pow_ne_zero _ h5)
  have h1000 : (1000 : K)≠0 := by
    rw [show (1000 : K)=2^3*5^3 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5)
  have hc : (218/375 : K)-103/1000=287/600 := by
    field_simp [h375,h600,h1000]
    ring
  change (2/3 : K)*φ (K:=K) p _+_= _ at hv
  linear_combination (norm := (field_simp [h375,h600,h1000]; ring))
    hD+hr+hv+(WPFiniteNC122.h p : K)^2*hc

end WPFieldAssembly.BalancedVbalSuccessorRhoEvaluation
