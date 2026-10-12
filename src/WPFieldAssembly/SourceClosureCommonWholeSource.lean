import WPFieldAssembly.SourceClosurePeriodTransport
import WPFieldAssembly.SourceClosureActualUVAttachment
import WPFieldAssembly.SourceClosureTraceOrigin
import WPFieldAssembly.SourceClosureTraceReduction

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPActualEtaIntegrality
  WPFieldAssembly.ActualSigmaIntegral
  WPFieldAssembly.ActualIntegralGreenTrace
  WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.ActualBalancedGreenTransfer
  WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen
  WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualCommonTraceReduction
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureTraceOrigin
  WPFieldAssembly.SourceClosureTraceReduction
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.SourceClosureCommonWholeSource

set_option maxHeartbeats 1600000

/- The original rational quotients are reduced after their actual p-division.
   The whole common, balanced and period source is then collected before
   converting infinity to origin. This supplies no independent scalar value. -/

noncomputable def balancedField (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  coefficientMap (residueHom p) (actualBalancedDividedIntegral p hp)

theorem periodSourceIntegral_rational (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    coefficientMap (integralRationals p).subtype (periodSourceIntegral p hp)=
      T (-(((p-1)/2 : ℕ) : ℤ))*lowReflectionDefectQ p hp*
        (finiteConicLogQ p).toLaurent := by
  simp only [periodSourceIntegral,map_mul,coefficientMap_T,lowReflectionDefectQ,
    coefficientMap_toLaurent,ActualJointGreen.finiteConicLogIntegral_value p hp]

noncomputable def balancedDensityIntegral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (integralRationals p)[T;T⁻¹] :=
  integralKw p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ))*
    actualBalancedDividedIntegral p hp

/-- The full rational xi numerator is identified before any field reduction. -/
theorem balancedTrace_rational_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (balancedTraceIntegral p hp).val=
      LaurentPoleTrace.trace (p+1)
        (coefficientMap (integralRationals p).subtype (balancedDensityIntegral p hp)) := by
  have ht : (T (p : ℤ) : ℚ[T;T⁻¹])*T (-1)=T ((p-1 : ℕ) : ℤ) := by
    rw [←T_add]
    congr 1
    omega
  unfold balancedTraceIntegral xiTraceQ
  change LaurentPoleTrace.trace (p+1)
    (LaurentPolynomial.C (9*5^(p-1) : ℚ)*T ((p-1 : ℕ) : ℤ)*(4*T 1-11)^p*
      (4-11*T 1)*(T (-(((p-1)/2 : ℕ) : ℤ))*actualBalancedDividedQ p hp))=_
  congr 1
  simp only [balancedDensityIntegral,map_mul,integralKw_rational,
    dlogQNumerator_map,coefficientMap_T,actualBalancedDividedIntegral_value]
  simp only [rationalKw,dlogQNumerator,map_mul,map_ofNat]
  symm
  calc
    _ = 9*LaurentPolynomial.C ((5 : ℚ)^(p-1))*(T (p : ℤ)*T (-1))*
        (4*T 1-11)^p*(4-11*T 1)*
          (T (-(((p-1)/2 : ℕ) : ℤ))*actualBalancedDividedQ p hp) := by ring
    _ = _ := by rw [ht]

/-- A supplied integral lift is transported as a whole, with its literal trace. -/
theorem trace_integral_source (p m : ℕ) [Fact p.Prime] (hp : 19≤p)
    (q : integralRationals p) (I : (integralRationals p)[T;T⁻¹])
    (hq : q.val=LaurentPoleTrace.trace m (coefficientMap (integralRationals p).subtype I)) :
    residueHom p q=LaurentPoleField.fieldTrace p m (coefficientMap (residueHom p) I) := by
  change ((q.val : ℚ) : ZMod p)=_
  rw [hq,LaurentPoleField.trace_reduce p m hp _ (mapped_integral p I),reduce_integral_map]

/-- This is the actual divided balanced carrier, with no assigned first jet. -/
theorem balancedTrace_field_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (balancedTraceIntegral p hp)=
      LaurentPoleField.fieldTrace p (p+1)
        (3*(R : (ZMod p)[T;T⁻¹])^p*dlogQNumerator*
          T (-(((p-1)/2 : ℕ) : ℤ))*balancedField p hp) := by
  rw [trace_integral_source p (p+1) hp _ _ (balancedTrace_rational_source p hp)]
  simp only [balancedDensityIntegral,map_mul,integralKw_residue p hp,
    dlogQNumerator_map,coefficientMap_T,balancedField]

theorem periodTrace_field_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (periodCarryIntegral p hp)=
      LaurentPoleField.fieldTrace p 1 (dlogQNumerator*periodField p hp) := by
  have hq : (periodCarryIntegral p hp).val=LaurentPoleTrace.trace 1
      (coefficientMap (integralRationals p).subtype
        (dlogQNumerator*periodSourceIntegral p hp)) := by
    rw [map_mul,dlogQNumerator_map,periodSourceIntegral_rational p hp]
    change ActualBalancedGreenTransfer.dlogQtrace _ = LaurentPoleTrace.trace 1
      (dlogQNumerator*(T (-(((p-1)/2 : ℕ) : ℤ))*lowReflectionDefectQ p hp*
        (finiteConicLogQ p).toLaurent))
    rw [ActualBalancedGreenTransfer.dlogQtrace,ActualGreenCommonTrace.trace_one_eq_inverseAtrace]
    rfl
  have h := trace_integral_source p 1 hp (periodCarryIntegral p hp)
    (dlogQNumerator*periodSourceIntegral p hp) hq
  simpa only [map_mul,dlogQNumerator_map,periodField] using h

noncomputable def commonTraceDensity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  3*(R^(p-1)*delta*commonHField p*comparisonField p)-
    (LaurentPoleField.fieldAbar p).toLaurent*
      (3*(R^(p-1)*commonHField p*actualPositiveB p hp))-
    (LaurentPoleField.fieldAbar p).toLaurent*
      (3*(R^p*D (commonHField p)*actualUV p hp))

/-- The original common source uses the proved whole UV derivative and unchanged sigma. -/
theorem commonTrace_field_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)=
      LaurentPoleField.fieldTrace p (p+1) (commonTraceDensity p hp) := by
  have h := actualUV_common_trace_row p hp
  rw [commonTraceDensity,map_sub,map_sub,
    LaurentPoleField.fieldTrace_cleared p p hp,
    LaurentPoleField.fieldTrace_cleared p p hp]
  simp only [fieldTrace_three_mul,ActualCommonFieldIBP.kwFieldTrace] at h ⊢
  have he : (3*(R : (ZMod p)[T;T⁻¹])^p)*(D (commonHField p)*actualUV p hp)=
      3*(R^p*D (commonHField p)*actualUV p hp) := by ring
  rw [he] at h
  simp only [fieldTrace_three_mul] at h
  linear_combination h

noncomputable def wholeTraceDensity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  commonTraceDensity p hp+
    3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ))*balancedField p hp-
    (LaurentPoleField.fieldAbar p).toLaurent^p*(dlogQNumerator*periodField p hp)

/-- The whole SB98--101 trace has one unchanged denominator before inversion. -/
theorem actual_whole_trace_field_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp)=
      LaurentPoleField.fieldTrace p (p+1) (wholeTraceDensity p hp) := by
  rw [wholeTraceDensity,map_sub,map_add,commonTrace_field_source p hp,
    balancedTrace_field_source p hp,periodTrace_field_source p hp,
    show p+1=1+p by omega,LaurentPoleField.fieldTrace_cleared_pow p 1 p hp]

noncomputable def wholeOriginDensity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] := T (2*(p : ℤ))*invert (wholeTraceDensity p hp)

/-- All three actual quotients reach the literal origin residue, with no support omission. -/
theorem actual_whole_trace_origin_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp)=
      -originTrace p (p+1) (wholeOriginDensity p hp) := by
  rw [actual_whole_trace_field_source p hp,fieldTrace_successor_origin]
  rfl

noncomputable def properSource (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  WPActualRankTwoLegendreField.actualLegendreJacobi p*
    WPActualRankTwoProper.properLegendreJacobi p*
      (WPFiniteKSource.OP p+X^p*WPFiniteKSource.EP p)

noncomputable def properOriginDensity (p : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ)*NativeScalarRows.reciprocalDensity
    (NativeQuadraticInverse.quadraticInverse (properSource p))

/-- The original OP+X^p EP product remains whole in the proper origin projection. -/
theorem actual_proper_origin_source (p : ℕ) [Fact p.Prime] :
    ActualDeltaUNextSource.QO p (properSource p)=(properOriginDensity p).coeff (-1) := by
  simpa only [ActualDeltaUNextSource.QO,ResidualProjection.Ij,Nat.zero_mul,Nat.add_zero,
    properOriginDensity,NativeScalarRows.reciprocalDensity] using
    (ResidualProjection.polar_projection ((p-1)/2)
      (NativeQuadraticInverse.quadraticInverse (properSource p))).symm

/-- This is the original collection, without assigning a norm, endpoint or scalar value. -/
theorem actual_whole_trace_proper_origin_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)=
    -(2/3 : ZMod p)*originTrace p (p+1) (wholeOriginDensity p hp)+
      (2/3 : ZMod p)*(properOriginDensity p).coeff (-1) := by
  rw [actual_whole_trace_origin_source p hp,actual_proper_origin_source]
  ring

noncomputable def wholeNativeOriginDensity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] := invert (successorPoleReduction p (wholeTraceDensity p hp))

/-- The actual three-part trace now reaches the native simple-pole origin operator. -/
theorem actual_whole_trace_native_origin_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp)=
      -originPole (wholeNativeOriginDensity p hp) := by
  rw [actual_whole_trace_field_source p hp,fieldTrace_successor_native_origin p hp]
  rfl

noncomputable def wholeTraceProperNativeDensity (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (-2/3 : ZMod p)*wholeNativeOriginDensity p hp+
    LaurentPolynomial.C (2/3 : ZMod p)*
      ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*properOriginDensity p)

/-- Both the actual divided trace and the original whole proper product use one native origin. -/
theorem actual_whole_trace_proper_native_origin_source
    (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p)=
    originPole (wholeTraceProperNativeDensity p hp) := by
  rw [actual_whole_trace_native_origin_source p hp,actual_proper_origin_source,
    wholeTraceProperNativeDensity,originPole_add,originPole_C_mul,originPole_C_mul,
    originPole_cleared p hp]
  ring

/-- Faithful-field consumers receive this same actual source, without a free origin value. -/
theorem actual_whole_trace_proper_native_origin_transport
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (f : ZMod p →+* K) :
    f ((2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp))+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p (properSource p))=
    originPole (coefficientMap f (wholeTraceProperNativeDensity p hp)) := by
  rw [actual_whole_trace_proper_native_origin_source p hp,originPole_transport]

end WPFieldAssembly.SourceClosureCommonWholeSource
