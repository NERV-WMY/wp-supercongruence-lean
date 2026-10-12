import WPFieldAssembly.BalancedVbalSuccessorRhoSource
import WPFieldAssembly.BalancedVbalSuccessorOriginSeriesTransport
import WPFieldAssembly.BalancedVbalSuccessorJSeriesTransport
import WPFieldAssembly.BalancedVbalSuccessorCoupledEvaluation
import WPFieldAssembly.ScalarFinalSuccessorWholeTraceSource

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource

namespace WPFieldAssembly.BalancedVbalSuccessorRhoEvaluation

open ActualBpairContraction ActualBpairLowHLocalPole ActualSimplePoleResidue
  ActualGreenResidue ActualThreePhase NativeJointSuccessorJSeries
  NativeJointSuccessorWneedCore SourceClosureBalancedOriginalDensity
  SourceClosureCommonWholeSource SourceClosureHFNativeTransport
  SourceClosureTraceReduction SourceClosureTraceOrigin SourceClosureWholeTraceCollection
  BalancedVbalSuccessorRhoSource BalancedVbalSuccessorOriginSeriesTransport
  BalancedVbalSuccessorJSeriesTransport BalancedVbalSuccessorCoupledSource
  BalancedVbalSuccessorCoupledEvaluation

variable {K : Type*} [Field K]
set_option maxHeartbeats 2000000

/- STATEMENT_FIDELITY: the original full proper/common density and the
existing native WneedCoreCarrier plus the entire H*WHF are kept literal.
The original metric/dlog Jcoupled is mapped as a complete Laurent series.
No rho value, HF deletion, series identification or endpoint equality is
assumed. This file is source-only until its affected dependency checks pass. -/

/-- Both original IR63 period rows commute with the actual coefficient map. -/
theorem actual_period_origin_base_change (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    φ (K:=K) p
      (originPole
        ((33-12*T 1)*
          ((NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : ZMod p)*(Dstar p : (ZMod p)[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))+
            (ActualFirstGreen.CB p).toLaurent*
              (LaurentPolynomial.C (-10/9 : ZMod p)*
                (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p))))))=
      originPole
        ((33-12*T 1)*
          ((fK (K:=K) p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : K)))+
            (CBK (K:=K) p).toLaurent*
              (LaurentPolynomial.C (-10/9 : K)*
                (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : K))))) := by
  rw [originPole_transport]
  congr 1
  simp only [map_mul,map_add,map_sub,map_neg,map_ofNat,coefficientMap_T,
    coefficientMap_C,map_div₀,coefficientMap_invert,
    coefficientMap_toLaurent,Dstar_natural,actual_LV_transport,
    WPFiniteNC122.q,map_intCast,fK,CBK]

/-- The actual low density and whole proper product equal the SAME full Wneed
origin, with the independently derived proper-square and coupled detectors. -/
theorem actual_low_proper_Wneed_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (2/3 : K)*φ (K:=K) p
        (LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp))+
      (2/3 : K)*φ (K:=K) p (ActualDeltaUNextSource.QO p (properSource p))=
      originPole
        (actualWneedCoreCarrier p+
          (HpullK (K:=K) p).toLaurent*
            (nativeHFSigmaNumerator p+
              WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                (4*T (-(p : ℤ))-11)*nativeHFBracket p u))+
      (218/375 : K)*(WPFiniteNC122.h p)^2 := by
  have hl := congrArg (φ (K:=K) p)
    (actual_low_density_original_coupled_source p hp)
  have hpair := congrArg (φ (K:=K) p)
    (actual_original_HF_period_origin_pair p hp)
  have hJ := congrArg (φ (K:=K) p) (actual_Jjoint_origin_finite_h p hp)
  have hh : φ (K:=K) p (WPFiniteNC122.h p : ZMod p)=(WPFiniteNC122.h p : K) := by
    simp only [WPFiniteNC122.h,WPFiniteNC122.q,map_sub,map_mul,map_neg,
      map_div₀,map_intCast,map_ofNat]
  rw [actual_harmonic_is_finite_h p hp] at hl
  simp only [map_add (φ (K:=K) p),map_sub (φ (K:=K) p)] at hl hpair
  rw [actual_original_Jcoupled_base_change p hp] at hl
  rw [actual_period_origin_base_change p hp] at hpair
  simp only [map_mul (φ (K:=K) p),map_div₀ (φ (K:=K) p),
    map_pow (φ (K:=K) p),map_ofNat (φ (K:=K) p),hh]
    at hl hpair hJ
  have hW := actual_originTrace_HF_period_J_Wneed_bridge (K:=K) p hp u hu
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K)≠0 := by
    rw [show (125 : K)=5^3 by ring]
    exact pow_ne_zero _ h5
  have h375 : (375 : K)≠0 := by
    rw [show (375 : K)=3*5^3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  have hc : (8/125 : K)+194/375=218/375 := by
    field_simp [h125,h375]
    ring
  linear_combination (norm := (field_simp [h125,h375]; ring))
    hl+hpair+hJ+hW+(WPFiniteNC122.h p : K)^2*hc

/-- The original full proper/common trace minus the SAME full Wneed has the
literal original T5, UV and normalized-Z alphabet and the evaluated rho term. -/
theorem actual_original_rho_full_alphabet (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originPole
      (coefficientMap (φ (K:=K) p) (wholeTraceProperNativeDensity p hp)-
        (actualWneedCoreCarrier p+
          (HpullK (K:=K) p).toLaurent*
            (nativeHFSigmaNumerator p+
              WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                (4*T (-(p : ℤ))-11)*nativeHFBracket p u)))=
      ActualKwOrderedEndpoints.originalT5 p u+originalUVFiniteRemainder p u+
      SourceClosureNormalizedZFinite.normalizedZFiniteValue p u+
      (218/375 : K)*(WPFiniteNC122.h p)^2 := by
  rw [originPole_sub,actual_native_proper_density_collection p hp (φ (K:=K) p) u hu]
  have h := actual_low_proper_Wneed_origin (K:=K) p hp u hu
  linear_combination h

end WPFieldAssembly.BalancedVbalSuccessorRhoEvaluation
