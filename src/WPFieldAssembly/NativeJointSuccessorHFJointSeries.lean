import WPFieldAssembly.NativeJointSuccessorConicSeries
import WPFieldAssembly.SourceClosureHFBranchFactor

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  SourceClosureHFNativeTransport

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

/-- Reflection supplies the SAME full weighted Sigma logarithm used in actual HF. -/
theorem actual_HF_sigma_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (nativeHFSigmaNumerator p : K[T;T⁻¹]) =
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (nativeKSigma p) * actualZlogSeries (K := K) := by
  have h := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_HF_sigma_Laurent_clearing (K := K) p hp)
  simp only [map_mul] at h
  unfold actualZlogSeries
  calc
    _ = (localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (nativeKSigma p) * localFiniteSeriesHom nativeZlogNumerator) /
          localFiniteSeriesHom nativeZlogDenominator := by
      apply (eq_div_iff (conicSeries_zlog_denominator_ne_zero p hp)).mpr
      linear_combination h
    _ = _ := by ring

/-- The last odd source survives in the joint derivative; no cutoff is replaced by an infinite log. -/
theorem actual_J_joint_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) +
      localFiniteSeriesHom (frobeniusPhi p) * actualZlogSeries (K := K) =
    actualOddSeries (K := K) p + localFiniteSeriesHom (frobeniusPhi p) *
      ((1 / 2 : LaurentSeries K) * localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) +
        (1 / 3 : LaurentSeries K) *
          localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent)) := by
  have hdA : localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (actualAK p : K[X]).toLaurent : LaurentSeries K) :=
    lowHFiniteSeries_derivative (actualAK p : K[X]).toLaurent
  rw [actual_J_series_odd_log_split p hp, actual_Zlog_series p hp,
    ← hdA]
  simp only [localFiniteSeries_C, map_div₀, map_one, map_ofNat]
  ring

/-- IR65b--g is a complete source equality: conic plus the literal nonunit correction. -/
theorem actual_joint_j_Sigma_proper_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (actualCgreen p) *
          LaurentSeries.derivative K (actualJSeries (K := K) p : LaurentSeries K) +
      localFiniteSeriesHom ((HpullK (K := K) p).toLaurent * nativeHFSigmaNumerator p) -
      (1 / 3 : LaurentSeries K) * localFiniteSeriesHom
        ((WPFiniteZSource.Abar : K[X]).toLaurent *
          coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)) =
    localFiniteSeriesHom (threePhaseConicDensity p (actualPC (K := K) p)) -
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (frobeniusPhi p) * localFiniteSeriesHom (actualCgreen p) *
        ((1 / 2 : LaurentSeries K) * localFiniteSeriesHom (T (-1) : K[T;T⁻¹]) +
          (1 / 3 : LaurentSeries K) * localFiniteSeriesHom (D (actualAK p : K[X]).toLaurent)) := by
  have hj := actual_J_joint_source (K := K) p hp
  have hc := actual_joint_conic_series_source (K := K) p hp
  have hκ : (nativeKSigma p : K[T;T⁻¹]) =
      -LaurentPolynomial.C (2 / 5 : K) * frobeniusPhi p * Dsym p := by rfl
  rw [map_mul, actual_HF_sigma_series_source p hp, map_mul,
    actual_properMetric_series_source p hp]
  rw [hκ]
  simp only [actualCgreen, map_mul, map_add, map_neg,
    localFiniteSeries_C, map_div₀, map_ofNat] at hj hc ⊢
  linear_combination
    -localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
      ((2 / 3 : LaurentSeries K) * localFiniteSeriesHom (CMK (K := K) p).toLaurent +
        (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (HpullK (K := K) p).toLaurent *
          localFiniteSeriesHom (Dsym p)) * hj + hc

end WPFieldAssembly.NativeJointSuccessorMixedGreenCore

