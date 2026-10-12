import WPFieldAssembly.NativeJointSuccessorScalarSource
import WPFieldAssembly.NativeJointSuccessorLowHRootCollection
import WPFieldAssembly.NativeJointSuccessorConicSeries
import WPFieldAssembly.NativeJointSuccessorCMPrimitive
import WPFieldAssembly.NativeClosureMetricDerivative
import WPFieldAssembly.NativeJointSuccessorHFJointSeries

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorWneedCore NativeJointSuccessorRroot
  NativeJointSuccessorScalarSource NativeClosureLowH SourceClosureHFNativeTransport

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

private theorem small_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : n ∈ Finset.Ico 1 p) : (n : LaurentSeries K) ≠ 0 := by
  simpa only [map_natCast, map_zero] using
    (algebraMap K (LaurentSeries K)).injective.ne
      (WPFiniteField.denominator_ne_zero (K := K) p n hn)

/-- The original B0 derivative is collected with the whole R52 differential. -/
theorem actual_B0_derivative_source (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (actualIR63B0 (K := K) p) =
      -2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) * D (literalKB p) +
        LaurentPolynomial.C (5 / 12 : K) * T (p : ℤ) * D (actualR52 p) := by
  change D (nativeActualCBMultiplier (K := K) p) = _
  rw [native_actual_CB_multiplier_derivative,
    actual_R52_derivative]
  ring

/-- This is precisely the non-odd metric row of IR65b, with CMhand=2*CMK. -/
theorem actual_B0_metric_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (CMK (K := K) p).toLaurent *
        (localFiniteSeriesHom (D (actualIR63B0 p)) -
          (10 / 9 : LaurentSeries K) * localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent))) -
      (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (CMK (K := K) p).toLaurent *
        localFiniteSeriesHom (frobeniusPhi p) *
          ((1 / 2 : LaurentSeries K) * localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) +
            (1 / 3 : LaurentSeries K) * localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent)) =
    localFiniteSeriesHom (coefficientMap (ActualThreePhase.φ (K := K) p) (actualMetricDensity p)) := by
  have h := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_metric_green_source (K := K) p hp)
  have h2 := small_series_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 := small_series_ne_zero (K := K) p 3 (Finset.mem_Ico.mpr (by omega))
  have h9 := small_series_ne_zero (K := K) p 9 (Finset.mem_Ico.mpr (by omega))
  have h12 : (12 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h2) h3 using 1; norm_num
  have h24 : (24 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) h3 using 1; norm_num
  rw [actual_B0_derivative_source]
  simp only [frobeniusPhi, map_mul, map_add, map_sub, map_neg, map_ofNat,
    map_one, localFiniteSeries_C, map_div₀] at h ⊢
  linear_combination (norm := (field_simp [h2, h3, h9, h12, h24]; ring)) h

/-- The complete DeltaB derivative retains j' and the original reciprocal even derivative. -/
theorem actual_DeltaB_series_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    LaurentSeries.derivative K (actualDeltaBSeries (K := K) p : LaurentSeries K) =
      -(2 / 3 : LaurentSeries K) *
        LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) -
        (10 / 9 : LaurentSeries K) * localFiniteSeriesHom (D (invert (actualAK p : K[X]).toLaurent)) := by
  have he : (actualDeltaBSeries (K := K) p : LaurentSeries K) =
      localFiniteSeriesHom (LaurentPolynomial.C (-2 / 3 : K)) * actualJSeries (K := K) p +
        localFiniteSeriesHom (-LaurentPolynomial.C (10 / 9 : K) *
          (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) := by
    simp only [actualDeltaBSeries, map_mul, map_sub, map_neg, localFiniteSeries_C,
      map_div₀, map_ofNat]
    ring
  have hdFinite : localFiniteSeriesHom
      (D (-LaurentPolynomial.C (10 / 9 : K) *
        (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)))) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (-LaurentPolynomial.C (10 / 9 : K) *
          (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (-LaurentPolynomial.C (10 / 9 : K) *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)))
  rw [he, map_add, finite_series_derivative_product, ← hdFinite]
  simp only [D_C, map_zero, zero_mul, zero_add, neg_mul, map_neg, D_C_mul, map_sub, sub_zero,
    map_mul, localFiniteSeries_C, map_div₀, map_ofNat]
  ring

/-- Coefficient transport attaches the entire joint density, rather than its scalar alone. -/
theorem actual_joint_metric_series_attachment (p : ℕ) [Fact p.Prime] [CharP K p] :
    localFiniteSeriesHom (originalJointMetricDensity (K := K) p) =
      localFiniteSeriesHom (threePhaseConicDensity p (actualPC p)) +
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
          localFiniteSeriesHom (coefficientMap (ActualThreePhase.φ (K := K) p) (actualMetricDensity p)) := by
  simp only [originalJointMetricDensity, threePhaseConicDensity, actualPC,
    map_add, map_mul, map_sub, coefficientMap_C, coefficientMap_T,
    coefficientMap_toLaurent, map_div₀, map_ofNat, WPFiniteZSource.Abar,
    Polynomial.map_X, Polynomial.map_one]

/-- The whole j/Sigma/proper metric and Bnew differential are the SAME conic/metric source.
Its H correction is retained until the original H completion is added. -/
theorem actual_Bnew_joint_metric_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (CMK (K := K) p).toLaurent *
          (localFiniteSeriesHom (D (actualIR63B0 p)) +
            LaurentSeries.derivative K (actualDeltaBSeries (K := K) p : LaurentSeries K)) -
      (1 / 3 : LaurentSeries K) * localFiniteSeriesHom
        ((WPFiniteZSource.Abar : K[X]).toLaurent *
          coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)) +
      localFiniteSeriesHom ((HpullK (K := K) p).toLaurent * nativeHFSigmaNumerator p) -
      (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (HpullK (K := K) p).toLaurent * localFiniteSeriesHom (Dsym p) *
          LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) =
    localFiniteSeriesHom (originalJointMetricDensity p) - localFiniteSeriesHom (actualHCorrection p) := by
  have hj := actual_joint_j_Sigma_proper_source (K := K) p hp
  have hm := actual_B0_metric_series_source (K := K) p hp
  rw [actual_DeltaB_series_derivative, actual_joint_metric_series_attachment]
  simp only [actualCgreen, actualHCorrection, map_mul, map_add, localFiniteSeries_C,
    map_div₀, map_ofNat, map_one] at hj ⊢
  linear_combination hj + localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent * hm

/-- Actual CB/CM integration by parts keeps the full harmonic branch and half metric scale. -/
theorem actual_CB_DeltaB_metric_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (actualCBDeltaBLCarrier (K := K) p) =
      (3 / 2 : LaurentSeries K) * localFiniteSeriesHom (HpullK (K := K) p).toLaurent *
        localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
          actualDeltaBSeries (K := K) p +
      3 * localFiniteSeriesHom (LaurentPolynomial.C (WPFiniteNC122.h (K := K) p)) *
        localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
          actualDeltaBSeries (K := K) p -
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (D (CMK (K := K) p).toLaurent) * actualDeltaBSeries (K := K) p := by
  have h := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (native_actual_CB_H_cleared (K := K) p hp)
  rw [ActualGreenResidue.hK, ActualCubicNativeSource.actual_harmonic_map p hp] at h
  rw [← actual_CB_DeltaB_L_Laurent p hp]
  simp only [map_mul, map_add, map_sub, map_ofNat, localFiniteSeries_C, map_div₀] at h ⊢
  have h2 : (2 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  linear_combination (norm := (field_simp [h2]; ring)) actualDeltaBSeries (K := K) p * h

/-- Nj remains the full original pole detector for this SAME j and symmetric factor. -/
theorem actual_Nj_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (33 - 12 * T 1 : K[T;T⁻¹]) *
        localFiniteSeriesHom (Dsym p) * actualJSeries (K := K) p -
      2 * localFiniteSeriesHom (LaurentPolynomial.C (WPFiniteNC122.h p)) *
        localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
          actualJSeries (K := K) p := by
  have hR : localFiniteSeriesHom
      (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) *
        actualJSeries (K := K) p := by
    unfold actualJSeries
    rw [map_pow]
    field_simp [pow_ne_zero ((p - 1) / 2) (conicSeries_squared_ne_zero p hp)]
  have hJ : localFiniteSeriesHom
      (mixedProduct p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      localFiniteSeriesHom (Dsym p) * actualJSeries (K := K) p := by
    have h := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
      (mixedProduct_consistency (K := K) p hp (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
    simp only [map_mul, hR] at h
    apply mul_left_cancel₀
      (show localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) ≠ 0 by
        rw [map_pow]
        exact pow_ne_zero _ (conicSeries_squared_ne_zero p hp))
    linear_combination h
  unfold mixedJNumerator
  simp only [map_sub, map_mul, hR, hJ, localFiniteSeries_C, map_div₀, map_ofNat]
  ring

end WPFieldAssembly.NativeJointSuccessorMixedGreenCore
