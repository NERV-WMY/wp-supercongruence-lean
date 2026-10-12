import WPFieldAssembly.NativeJointSuccessorHCollector
import WPFieldAssembly.NativeJointSuccessorLowHBracketCollection
import WPFieldAssembly.NativeJointSuccessorMixedGreenOddTransport

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorWneedCore NativeJointSuccessorRroot
  NativeJointSuccessorScalarSource SourceClosureHFNativeTransport NativeClosureLowH
  NativeJointSuccessorHCollector

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000
private theorem small_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : n ∈ Finset.Ico 1 p) : (n : LaurentSeries K) ≠ 0 := by
  simpa only [map_natCast, map_zero] using
    (algebraMap K (LaurentSeries K)).injective.ne
      (WPFiniteField.denominator_ne_zero (K := K) p n hn)

/-- IR64d and IR66h collect the complete Delta, NC83 bracket and non-Sigma HF source.
The undifferentiated odd source cancels against the SAME finite NC83 quotient. -/
theorem actual_mixed_H_completion_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    localFiniteSeriesHom (HpullK (K := K) p).toLaurent *
        ((3 / 2 : LaurentSeries K) *
            localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) *
              actualDeltaBSeries (K := K) p -
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
            localFiniteSeriesHom (D (actualDeltaCarrier p)) -
          localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
            localFiniteSeriesHom (D (actualBracketQK p)) +
          localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
            frobeniusPhi p * nativeHFBracket p u)) -
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (originalHCompletion p u) =
    -(2 / 5 : LaurentSeries K) * localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
      localFiniteSeriesHom (HpullK (K := K) p).toLaurent * localFiniteSeriesHom (Dsym p) *
        LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) +
      localFiniteSeriesHom (actualHCorrection p) := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  let A := f (WPFiniteZSource.Abar : K[X]).toLaurent
  let H := f (HpullK (K := K) p).toLaurent
  let U := f (actualAK p : K[X]).toLaurent
  let V := f (invert (actualAK p : K[X]).toLaurent)
  let q := f (LaurentPolynomial.C (WPFiniteNC122.q (K := K) p))
  let h := f (LaurentPolynomial.C (WPFiniteNC122.h (K := K) p))
  let e := V - (q - h)
  let S := f (WPFiniteWSource.squaredCoordinate.toLaurent) ^ ((p - 1) / 2)
  let Xn := f (T (((p - 1) / 2 : ℕ) : ℤ))
  let Y := f (T (-(((p - 1) / 2 : ℕ) : ℤ)))
  let ph := 4 * f (T (-(p : ℤ))) - 11
  let Q := f (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent
  let Qlog := f (lowHLinearYQLog (nativeH (K := K) p))
  let Pv := f (invert (WPFiniteZSource.P p u))
  let Vd := f (D (invert (actualAK p : K[X]).toLaurent))
  let B := q - 2 * h / 3 - 2 * V / 3 - U / 3 - Pv - Xn * (U + h) / 3
  have h2 : (2 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 5 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 6 (Finset.mem_Ico.mpr (by omega))
  have h9 : (9 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 9 (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 10 (Finset.mem_Ico.mpr (by omega))
  have hHQ : A * Q = H := by
    have he := congrArg f (congrArg (fun P : K[X] => P.toLaurent)
      (lowHBranchYQuotient_source (nativeH (K := K) p) (nativeH_origin p)))
    simpa only [map_mul, nativeH_original_Hpull p hp, A, Q, H, f] using he.symm
  have hXY : Xn * Y = 1 := by
    dsimp only [Xn, Y]
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hDs := congrArg f (Dsym_cleared_source (K := K) p hp)
  have hDd := congrArg f (native_dstar_density (K := K) p hp (nativeH p) (nativeH_origin p))
  have hJ := actual_J_value_source (K := K) p hp
  have hE := congrArg f (native_actual_Euler_bracket_collection (K := K) p hp)
  rw [actual_EulerBracket_source p] at hE
  rw [ActualGreenResidue.hK, ActualCubicNativeSource.actual_harmonic_map p hp] at hE
  have hq : ActualThreePhase.φ (K := K) p (WPFiniteNC122.q (K := ZMod p) p) =
      WPFiniteNC122.q (K := K) p := by
    simp only [WPFiniteNC122.q, map_intCast]
  rw [hq] at hE
  have hO := congrArg f (actual_odd_quotient_weighted_source (K := K) p hp)
  have hv0 := congrArg f (native_v_shifted_density (K := K) p hp (nativeH p) (nativeH_origin p))
  simp only [f, map_mul, map_add, map_sub, map_pow, map_neg, map_one, map_ofNat,
    localFiniteSeries_C, map_div₀, nativeH_original_Hpull p hp] at hDs hDd hJ hE hO hv0
  have hv : 2 * H * Vd + Qlog = 3 * ph * S * Y * Q := by
    change Xn * (2 * (H * Vd) + Qlog) = 3 * ph * S * Q at hv0
    linear_combination Y * hv0 - (2 * H * Vd + Qlog) * hXY
  have hδ := actual_delta_series_product_derivative (K := K) p hp
  simp only [map_sub, localFiniteSeries_C] at hδ
  dsimp only [actualDeltaBSeries, nativeHFBracket, originalHCompletion, actualHCorrection,
    ActualGreenResidue.hK]
  rw [ActualCubicNativeSource.actual_harmonic_map p hp]
  simp only [mixedEvenSource, map_mul, map_add, map_sub, map_neg, map_pow, map_ofNat, map_one,
    localFiniteSeries_C, map_div₀, nativeH_original_Hpull p hp, lowHLinearYOverX,
    Dsym, frobeniusPhi] at hDs hDd hJ hE hO hδ ⊢
  dsimp only [A, H, U, V, q, h, e, S, Xn, Y, ph, Q, Qlog, Pv, Vd, B] at hv hHQ hXY ⊢
  linear_combination (norm :=
    (dsimp only [A, H, U, V, q, h, e, S, Xn, Y, ph, Q, Qlog, Pv, Vd, B, f]
     simp only [localFiniteSeries_C]
     field_simp [h2, h3, h5, h6, h9, h10]
     ring))
    -A * H * hδ - (2 / 5 : LaurentSeries K) * H * actualJSeries (K := K) p * hDs -
      (2 / 3 : LaurentSeries K) * A * e * hDd - A * hE +
      (1 / 3 : LaurentSeries K) * A * hO - H * Y * hJ -
      (A / 3) * B * hv + (1 / 3 : LaurentSeries K) * H * S * ph * (U + h) * hXY +
      (Y * f (oddReciprocalS p) + (5 / 3 : LaurentSeries K) * S * e - ph * S * Y * B) * hHQ

end WPFieldAssembly.NativeJointSuccessorMixedGreenCore
