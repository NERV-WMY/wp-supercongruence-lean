import WPFieldAssembly.BalancedVbalSuccessorSeriesMap
import WPFieldAssembly.NativeJointSuccessorJSeries

open scoped Polynomial LaurentPolynomial LaurentSeries BigOperators
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource

namespace WPFieldAssembly.BalancedVbalSuccessorJSeriesTransport

open ActualBpairContraction ActualBpairLowHLocalPole NativeClosureMixedSource
  NativeJointSuccessorJSeries BalancedVbalSuccessorSeriesMap

variable {K L : Type*} [Field K] [Field L]
set_option maxHeartbeats 1600000

private theorem squaredCoordinate_natural (f : K →+* L) :
    (WPFiniteWSource.squaredCoordinate : K[X]).map f=
      (WPFiniteWSource.squaredCoordinate : L[X]) := by
  simp only [WPFiniteWSource.squaredCoordinate,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,
    map_inv₀,map_ofNat]

/-- The complete finite primitive commutes with coefficient mapping. -/
theorem Dstar_natural (f : K →+* L) (p : ℕ) :
    (Dstar p : K[X]).map f=(Dstar p : L[X]) := by
  simp only [Dstar,Polynomial.map_neg,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_comp,squaredCoordinate_natural,WPFiniteWSource.deltaE,
    Polynomial.map_sum,Polynomial.map_pow,Polynomial.map_X,map_div₀,
    map_pow,map_sub,map_one,map_mul,map_natCast,map_ofNat]

theorem Dsym_natural (f : K →+* L) (p : ℕ) :
    coefficientMap f (Dsym p : K[T;T⁻¹])=(Dsym p : L[T;T⁻¹]) := by
  simp only [Dsym,map_add,coefficientMap_invert,coefficientMap_toLaurent,
    Dstar_natural]

/-- The full odd cutoff and every reciprocal/Frobenius phase commute with mapping. -/
theorem mixedResidual_natural (f : K →+* L) (p : ℕ)
    (A : K[T;T⁻¹]) (h : K) :
    coefficientMap f (mixedResidual p A h)=
      mixedResidual p (coefficientMap f A) (f h) := by
  simp only [mixedResidual,oddReciprocalS,oddReciprocalKernel,
    mixedEvenSource,frobeniusPhi,map_add,map_mul,map_sub,map_pow,map_sum,
    coefficientMap_C,coefficientMap_T,coefficientMap_invert,
    coefficientMap_toLaurent,squaredCoordinate_natural,
    WPFiniteNC122.q,map_intCast,map_inv₀,map_natCast,map_ofNat,map_div₀,map_one]

/-- The existing original j series is mapped as a whole, before any residue. -/
theorem actual_J_series_natural (p : ℕ) [Fact p.Prime] [CharP K p] :
    seriesCoefficientHom (ActualThreePhase.φ (K:=K) p)
        (actualJSeries p : LaurentSeries (ZMod p))=
      (actualJSeries p : LaurentSeries K) := by
  have hA : coefficientMap (ActualThreePhase.φ (K:=K) p)
      (actualAK p : (ZMod p)[X]).toLaurent=(actualAK p : K[X]).toLaurent := by
    have hid : ActualThreePhase.φ (K:=ZMod p) p=RingHom.id (ZMod p) :=
      Subsingleton.elim _ _
    rw [coefficientMap_toLaurent]
    simp only [actualAK,hid,Polynomial.map_id]
  have hh : ActualThreePhase.φ (K:=K) p (WPFiniteNC122.h p : ZMod p)=
      (WPFiniteNC122.h p : K) := by
    simp only [WPFiniteNC122.h,WPFiniteNC122.q,map_sub,map_mul,
      map_neg,map_div₀,map_intCast,map_ofNat]
  unfold actualJSeries
  rw [map_div₀,map_pow,localFiniteSeriesHom_natural,localFiniteSeriesHom_natural,
    mixedResidual_natural,hA,hh,coefficientMap_toLaurent,squaredCoordinate_natural]

/-- The ORIGINAL metric/dlog Jcoupled residue maps to the SAME native consumer.
The series quotient, both metric terms and every Laurent coefficient are retained. -/
theorem actual_original_Jcoupled_base_change (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) :
    ActualThreePhase.φ (K:=K) p
      ((2/3 : ZMod p)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1)))=
      (2/3 : K)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : K)*
                (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
              (ActualThreePhase.CBK (K:=K) p).toLaurent)*
            (actualJSeries p : LaurentSeries K)*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1)) := by
  have hA : coefficientMap (ActualThreePhase.φ (K:=K) p)
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent=
        (WPFiniteZSource.Abar : K[X]).toLaurent := by
    rw [coefficientMap_toLaurent]
    simp only [WPFiniteZSource.Abar,Polynomial.map_mul,Polynomial.map_sub,
      Polynomial.map_ofNat,Polynomial.map_X,Polynomial.map_one]
  have hB : coefficientMap (ActualThreePhase.φ (K:=K) p)
      (4*T 1-11 : (ZMod p)[T;T⁻¹])=(4*T 1-11 : K[T;T⁻¹]) := by
    simp only [map_sub,map_mul,map_ofNat,coefficientMap_T]
  have hmetric : coefficientMap (ActualThreePhase.φ (K:=K) p)
      (LaurentPolynomial.C (3/5 : ZMod p)*
          (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
        (ActualFirstGreen.CB p).toLaurent)=
      LaurentPolynomial.C (3/5 : K)*
          (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
        (ActualThreePhase.CBK (K:=K) p).toLaurent := by
    simp only [map_sub,map_mul,coefficientMap_C,map_div₀,map_ofNat,
      coefficientMap_toLaurent,Dsym_natural,ActualThreePhase.fK,ActualThreePhase.CBK]
  rw [map_mul]
  simp only [map_div₀,map_ofNat]
  congr 1
  rw [←seriesCoefficientHom_coeff (ActualThreePhase.φ (K:=K) p)]
  congr 1
  simp only [map_mul,map_div₀,map_neg,map_ofNat,localFiniteSeriesHom_natural,
    actual_J_series_natural,hA,hB,hmetric]

end WPFieldAssembly.BalancedVbalSuccessorJSeriesTransport
