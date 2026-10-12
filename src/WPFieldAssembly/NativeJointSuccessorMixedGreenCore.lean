import WPFieldAssembly.NativeJointSuccessorScalarSource
import WPFieldAssembly.NativeJointSuccessorConicSeries
import WPFieldAssembly.NativeJointSuccessorHFJointSeries
import WPFieldAssembly.NativeJointSuccessorMixedGreenOddTransport
import WPFieldAssembly.NativeJointSuccessorGreenMetricSeries
import WPFieldAssembly.NativeJointSuccessorGreenHCompletion
import WPFieldAssembly.NativeJointSuccessorEndCollector
import WPFieldAssembly.NativeJointSuccessorCMPrimitive
import WPFieldAssembly.ScalarFinalSuccessorGreenCancellation

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open ActualBpairContraction ActualGreenResidue ActualBpairLowHLocalPole
  NativeClosureMixedSource NativeJointSuccessorOddSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorWneedCore NativeJointSuccessorRroot
  NativeJointSuccessorScalarSource SourceClosureHFNativeTransport NativeClosureLowH
  NativeJointSuccessorHCollector NativeJointSuccessorEndCollector

variable {K : Type*} [Field K]
set_option maxHeartbeats 2800000

private theorem small_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : n ∈ Finset.Ico 1 p) : (n : LaurentSeries K) ≠ 0 := by
  simpa only [map_natCast, map_zero] using
    (algebraMap K (LaurentSeries K)).injective.ne
      (WPFiniteField.denominator_ne_zero (K := K) p n hn)

/-- The complete remaining mixed collector is the negative derivative of the original CMK*Bnew.
No source, scalar, residue or numerical endpoint premise is used. -/
theorem actual_remaining_original_Green_series_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    localFiniteSeriesHom (remainingOriginalCollector p hp u : K[T;T⁻¹]) =
      -localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
        localFiniteSeriesHom (D (NativeJointSuccessorCMPrimitive.actualCMBnewCarrier p)) := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  let A := f (WPFiniteZSource.Abar : K[X]).toLaurent
  let S := f (WPFiniteWSource.squaredCoordinate.toLaurent) ^ ((p - 1) / 2)
  let h := f (LaurentPolynomial.C (WPFiniteNC122.h (K := K) p))
  let L := f (33 - 12 * T 1)
  have hH := actual_mixed_H_completion_series_source (K := K) p hp u
  have hCB := actual_CB_DeltaB_metric_series_source (K := K) p hp
  have hm := actual_Bnew_joint_metric_series_source (K := K) p hp
  have hprim := NativeJointSuccessorCMPrimitive.actual_CM_Bnew_derivative_source (K := K) p hp
  have hdelta := (actual_delta_Laurent (K := K) p hp).symm
  have hNj := actual_Nj_series_source (K := K) p hp
  have hB : (actualDeltaBSeries (K := K) p : LaurentSeries K) =
      -(2 / 3 : LaurentSeries K) * actualJSeries (K := K) p - (10 / 9 : LaurentSeries K) *
        f (invert (actualAK p : K[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) := rfl
  have h3 : (3 : LaurentSeries K) ≠ 0 :=
    small_series_ne_zero (K := K) p 3 (Finset.mem_Ico.mpr (by omega))
  have hcertificate :=
    ScalarFinalSuccessorGreenCancellation.whole_collector_cofactor_identity h3 A
      (f (CMK (K := K) p).toLaurent) (f (D (CMK (K := K) p).toLaurent))
      (f (HpullK (K := K) p).toLaurent) S L h
      (f (Dsym p)) (f (Dstar p).toLaurent)
      (actualJSeries (K := K) p) (LaurentSeries.derivative K (actualJSeries (K := K) p))
      (f (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)))
      (f (actualDeltaCarrier p)) (f (D (actualDeltaCarrier p)))
      (f (D (actualBracketQK p))) (f (actualCBDeltaBLCarrier p))
      (f (nativeHFSigmaNumerator p)) (f (frobeniusPhi p) * f (nativeHFBracket p u))
      (f (originalHCompletion p u)) (f (actualHCorrection p))
      (f (coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)))
      (f (originalJointMetricDensity p))
      (f (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)))
      (actualDeltaBSeries (K := K) p) (f (actualIR63B0 p))
      (LaurentSeries.derivative K (actualDeltaBSeries (K := K) p))
      (f (D (actualIR63B0 p)))
      (f (D (NativeJointSuccessorCMPrimitive.actualCMBnewCarrier p)))
  dsimp only at hcertificate
  rw [actual_remaining_original_end_reduction p hp u]
  dsimp only [mixedHCompletionDensity, actualEndComplementSource]
  simp only [f, actualDeltaSeries, frobeniusPhi, map_add, map_sub, map_mul, map_neg, map_pow,
    localFiniteSeries_C, map_div₀, map_ofNat, map_one] at hdelta hH hCB hm hNj hprim hB hcertificate ⊢
  linear_combination (norm :=
    (dsimp only [A, S, h, L, f]
     simp only [map_sub, map_mul, map_ofNat, localFiniteSeries_C]
     ring))
    hcertificate + hH + hCB + hm + A * hprim + L * hdelta - hNj + 3 * h * S * hB

/-- The complete original collector is the actual finite Green derivative, with all phases retained. -/
theorem actual_remaining_original_Green_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (remainingOriginalCollector p hp u : K[T;T⁻¹]) =
      -(WPFiniteZSource.Abar : K[X]).toLaurent *
        D (NativeJointSuccessorCMPrimitive.actualCMBnewCarrier p) := by
  apply conicSeries_finite_injective
  simpa only [map_mul, map_neg] using actual_remaining_original_Green_series_source (K := K) p hp u

/-- Zero origin follows from the proved whole Green derivative, rather than a collector assignment. -/
theorem actual_remaining_original_Green_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ActualSimplePoleResidue.originPole (remainingOriginalCollector p hp u : K[T;T⁻¹]) = 0 := by
  rw [actual_remaining_original_Green_source p hp u,
    show -(WPFiniteZSource.Abar : K[X]).toLaurent *
        D (NativeJointSuccessorCMPrimitive.actualCMBnewCarrier (K := K) p) =
      LaurentPolynomial.C (-1 : K) * ((WPFiniteZSource.Abar : K[X]).toLaurent *
        D (NativeJointSuccessorCMPrimitive.actualCMBnewCarrier p)) by
      simp only [map_neg, map_one]; ring,
    ActualSimplePoleResidue.originPole_C_mul,
    NativeJointSuccessorCMPrimitive.actual_CM_Bnew_total_derivative_origin p hp, mul_zero]

end WPFieldAssembly.NativeJointSuccessorMixedGreenCore
