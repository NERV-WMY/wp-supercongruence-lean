import WPFieldAssembly.BalancedVbalSuccessorOriginSeriesMap
import WPFieldAssembly.BalancedVbalSuccessorWneedBridge

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource

namespace WPFieldAssembly.BalancedVbalSuccessorOriginSeriesTransport

open ActualBpairContraction ActualBpairLowHLocalPole ActualGreenResidue
  SourceClosureTraceOrigin SourceClosureHFNativeTransport
  BalancedVbalSuccessorWneedBridge ActualSimplePoleResidue
  NativeJointSuccessorJSeries NativeJointSuccessorWneedCore

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000
private theorem actual_HFOrigin_coefficientMap (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    coefficientMap (ActualThreePhase.φ (K:=K) p)
        (nativeHFOriginNumerator (K:=ZMod p) p hp)=
      nativeHFOriginNumerator (K:=K) p hp := by
  have hid : ActualThreePhase.φ (K:=ZMod p) p=RingHom.id (ZMod p) :=
    Subsingleton.elim _ _
  have hself (F : (ZMod p)[T;T⁻¹]) :
      coefficientMap (RingHom.id (ZMod p)) F=F := by
    ext j
    rw [coefficientMap_coeff]
    rfl
  have hH : coefficientMap (ActualThreePhase.φ (K:=K) p)
      (HpullK (K:=ZMod p) p).toLaurent=(HpullK (K:=K) p).toLaurent := by
    rw [coefficientMap_toLaurent]
    simp only [HpullK,hid,Polynomial.map_id]
  unfold nativeHFOriginNumerator
  simp only [map_mul,map_sub,map_pow,map_neg,map_ofNat,coefficientMap_T,
    coefficientMap_invert,hH,hid,hself]

/-- The exact original HF originTrace transports to the SAME full p+1 local-series pole. -/
theorem actual_HF_originTrace_series_map (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    ActualThreePhase.φ (K:=K) p
      (originTrace p (p+1) (nativeHFOriginNumerator (K:=ZMod p) p hp))=
      (localFiniteSeriesHom (nativeHFOriginNumerator (K:=K) p hp)/
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^(p+1)).coeff (-1) := by
  rw [actual_originTrace_series_map p hp (p+1) (ActualThreePhase.φ (K:=K) p),
    actual_HFOrigin_coefficientMap p hp]

/-- The original HF trace, both period rows and ORIGINAL Jcoupled attach to the full literal Wneed.
The existing native carrier and complete weighted HF are retained and are not evaluated here. -/
theorem actual_originTrace_HF_period_J_Wneed_bridge (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    ActualThreePhase.φ (K:=K) p
      (originTrace p (p+1) (nativeHFOriginNumerator (K:=ZMod p) p hp))+
      originPole
        ((33-12*T 1)*
          ((ActualThreePhase.fK (K:=K) p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : K)))+
            (ActualThreePhase.CBK (K:=K) p).toLaurent*
              (LaurentPolynomial.C (-10/9 : K)*
                (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : K)))))+
      (2/3 : K)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : K)*
                (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
              (ActualThreePhase.CBK (K:=K) p).toLaurent)*
            actualJSeries p*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1))=
      originPole
        (actualWneedCoreCarrier p+
          (HpullK (K:=K) p).toLaurent*
            (nativeHFSigmaNumerator p+
              WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                (4*T (-(p : ℤ))-11)*nativeHFBracket p u)) := by
  rw [actual_HF_originTrace_series_map p hp]
  exact actual_original_HF_period_J_Wneed_Laurent_bridge (K:=K) p hp u hu

end WPFieldAssembly.BalancedVbalSuccessorOriginSeriesTransport
