import WPFieldAssembly.NativeJointSuccessorRmix
import WPFieldAssembly.ScalarFinalSuccessorWholeOriginRhoDefinitions
import WPFieldAssembly.ScalarFinalSuccessorWholeOriginRhoTransport
import WPFieldAssembly.NativeClosureLowHContraction
import WPFieldAssembly.NativeClosureMetricDerivative
import WPFieldAssembly.NativeClosureEndProductActual
import WPFieldAssembly.ActualBpairQuadraticTransport

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorScalarSource

open ActualBpairContraction ActualGreenResidue ActualThreePhase ActualSimplePoleResidue
  NativeJointSuccessorRmix NativeJointSuccessorRroot NativeJointSuccessorWneedCore
  NativeJointSuccessorCBMixed NativeJointSuccessorRhoReduction NativeClosureMixedSource
  NativeClosureLowH SourceClosureHFNativeTransport SourceClosureCommonWholeSource

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: this attaches the original NC77 scalar to its whole
Rroot/Rmix source and the original actual GB, G2, LowH and joint metric
densities. The last mixed Green collection is retained as an explicit
Laurent carrier. Its residue is not assigned a value. P-A/3 and chi0
remain distinct, and their Hpull origin conversion occurs exactly once.
No rho, Jraw, finite B2 or final scalar evaluation is repeated. -/

private theorem four_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (4 : K) ≠ 0 :=
  WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))

/-- The root Vmix value has its bracket value separated, while its adjoint
derivative retains the complete bracket, original Rroot and weighted HF. -/
noncomputable def rootMixedDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  (actualRootUniversalV p u + actualDeltaCarrier p) * (33 - 12 * T 1) -
    (WPFiniteZSource.Abar : K[X]).toLaurent * (HpullK (K := K) p).toLaurent *
      D (actualRootUniversalV p u + actualBracketQK p + actualDeltaCarrier p) +
    actualRroot p u (four_ne_zero p hp) + actualCBDeltaBLCarrier p +
    (HpullK (K := K) p).toLaurent *
      (nativeHFSigmaNumerator p +
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (-(p : ℤ)) - 11) * nativeHFBracket p u)

/-- Whole Rmix/Rroot cancellation separates only the original mapped GKQ and actual rho source. -/
theorem actual_full_native_root_rho_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    actualFullNativeDensity (K := K) p hp u (four_ne_zero p hp) =
      actualBracketQK p * (33 - 12 * T 1) +
        (coefficientMap (φ (K := K) p) (wholeTraceProperNativeDensity p hp) -
          fullWneedCarrier p u) + rootMixedDensity p hp u := by
  rw [actual_full_native_mixed_density p hp u (four_ne_zero p hp),
    actual_Rmix_Rroot_source p hp u (four_ne_zero p hp)]
  dsimp only [actualVmix, actualUniversalV, fullWneedCarrier, rootMixedDensity,
    actualWneedCoreCarrier]
  simp only [map_add]
  ring

/-- This is the exact actual NC77 source before the remaining mixed Green collection. -/
theorem actual_NC77_root_rho_unreduced (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u +
        φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) +
        originPole (rootMixedDensity p hp u) := by
  rw [actualNC77Scalar_full_native_origin p hp u hu (four_ne_zero p hp),
    actual_full_native_root_rho_source p hp u, originPole_add, originPole_add,
    ← actual_GKQ_bracket_origin p hp]
  dsimp only [originalRhoSourceValue]
  ring

/-- The original root chi uses P-A/3 before any origin conversion. -/
noncomputable def originalRootChi (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) * (actualAK p : K[X]).toLaurent

noncomputable def originalChi0 (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
    ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p))

/-- The only origin conversion from the root chi to the original chi0 is literal. -/
theorem actual_root_chi0_conversion (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    originalRootChi p u = originalChi0 p u + LaurentPolynomial.C (WPFiniteNC122.h p / 3) := by
  dsimp only [originalRootChi, originalChi0]
  have hc : LaurentPolynomial.C (1 / 3 : K) * LaurentPolynomial.C (WPFiniteNC122.h p) =
      LaurentPolynomial.C (WPFiniteNC122.h p / 3) := by
    rw [← map_mul]
    congr 1
    ring
  rw [mul_add, hc]
  ring

/-- The complete original GB carrier keeps chi0, Lambda_end and its original derivative. -/
noncomputable def originalGBDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (-1 : K) *
      ((33 - 12 * T 1) * (literalKB p * originalChi0 p u)) +
    (LaurentPolynomial.C (31 * WPFiniteNC122.q p) -
      LaurentPolynomial.C (4 * WPFiniteNC122.q p) * T 1) * literalKB p -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        (literalKB p * D (originalChi0 p u)))

/-- GB is the same whole density used by the original end-product attachment. -/
theorem actual_GB_density_attachment (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    originPole (originalGBDensity p u) = endProductActualGB p u := by
  rw [originalGBDensity, originPole_sub, originPole_add, originPole_C_mul,
    originPole_cleared p hp, GreenLaurentOperators.C_mul_coeff]
  dsimp only [endProductActualGB, originalChi0]
  simp only [map_ofNat]
  ring

/-- Both full original quadratic residues, including their complete metric, remain together. -/
noncomputable def originalG2Density (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  (33 - 12 * T 1) *
      (LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) * actualZ52 p u +
        LaurentPolynomial.C (2 / 3 : K) * (Dstar p : K[X]).toLaurent *
          (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) +
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (LaurentPolynomial.C (5 * WPFiniteNC122.h p / 4 : K) * T (p : ℤ) * actualR52 p -
        LaurentPolynomial.C (10 * WPFiniteNC122.h p / 3 : K) *
          (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)))

/-- The original NC123 whole quadratic block is the same actual G2, without a tail cutoff. -/
theorem actual_G2_density_attachment (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (originalG2Density p u) = actualNativeG2Residue (K := K) p := by
  rw [originalG2Density, originPole_add]
  simpa only [map_ofNat] using
    (actual_NC123_quadratic_block (K := K) p hp u hu
      (WPFiniteNC122.q p - WPFiniteNC122.h p))

/-- The original LowH source keeps the root P-A/3 slot. -/
noncomputable def originalLowHDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  (WPFiniteZSource.Abar : K[X]).toLaurent *
    nativeOriginalHSource p u (nativeH p) (literalKB p) (D (literalKB p))
      (WPFiniteNC122.h p) (WPFiniteNC122.q p)

/-- This density is precisely the single chi0 conversion of the LowH slot. -/
noncomputable def chi0OriginDensity (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  (WPFiniteZSource.Abar : K[X]).toLaurent *
    (LaurentPolynomial.C (WPFiniteNC122.h p / 3) *
      (HpullK (K := K) p).toLaurent * D (literalKB p))

noncomputable def originalChi0LowHDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] := originalLowHDensity p u - chi0OriginDensity p

/-- The conversion retains Hpull(0); the origin of H in its own variable is not substituted. -/
theorem actual_chi0_origin_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (chi0OriginDensity (K := K) p) =
      (WPFiniteNC122.h p / 3) * (HpullK (K := K) p).coeff 0 := by
  rw [chi0OriginDensity, originPole_cleared p hp,
    ← nativeH_original_Hpull p hp]
  exact native_H_chi0_kernel_origin p hp (WPFiniteNC122.h p)

private theorem root_coordinate (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) : (5 : K) * u ^ 2 = 1 := by
  rw [hu]
  exact mul_one_div_cancel (WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega)))

/-- The unchanged actual original LowH contraction is consumed at its original simple pole. -/
theorem actual_original_LowH_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (originalLowHDensity p u) = (97 / 375 : K) * (WPFiniteNC122.h p) ^ 2 := by
  rw [originalLowHDensity, originPole_cleared p hp]
  exact native_original_H_contraction p hp u (root_coordinate p hp u hu)
    (WPFiniteNC122.h p)

/-- The actual chi0 LowH contraction retains its exact origin correction once. -/
theorem actual_chi0_LowH_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (originalChi0LowHDensity p u) =
      (97 / 375 : K) * (WPFiniteNC122.h p) ^ 2 -
        (WPFiniteNC122.h p / 3) * (HpullK (K := K) p).coeff 0 := by
  rw [originalChi0LowHDensity, originPole_sub,
    actual_original_LowH_density p hp u hu, actual_chi0_origin_density p hp]

/-- The actual three conic phases and the whole Gauss metric collector share this mapped carrier. -/
noncomputable def originalJointMetricDensity (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  coefficientMap (φ (K := K) p)
    (threePhaseConicDensity p (actualGreenPC p) +
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * actualMetricDensity p)

/-- The SAME joint metric/conic source is consumed without splitting any of its pole slots. -/
theorem actual_joint_metric_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    originPole (originalJointMetricDensity (K := K) p) =
      -(1213 / 750 : K) * (WPFiniteNC122.h p) ^ 2 := by
  rw [originalJointMetricDensity,
    actual_joint_metric_coefficientMap_value p hp (φ (K := K) p),
    ActualCubicNativeSource.actual_harmonic_map p hp]

private theorem harmonic_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (97 / 375 : K) - 1213 / 750 = -(1019 / 750 : K) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h375 : (375 : K) ≠ 0 := by
    rw [show (375 : K) = 3 * 5 ^ 3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 3 h5)
  have h750 : (750 : K) ≠ 0 := by
    rw [show (750 : K) = 2 * 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero 3 h5)
  field_simp [h375, h750]
  ring

/-- The original LowH and complete conic/metric carriers have the retained -1019 normalization. -/
theorem actual_original_H_metric_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (originalLowHDensity p u + originalJointMetricDensity p) =
      -(1019 / 750 : K) * (WPFiniteNC122.h p) ^ 2 := by
  rw [originPole_add, actual_original_LowH_density p hp u hu, actual_joint_metric_density p hp]
  linear_combination (WPFiniteNC122.h p : K) ^ 2 * harmonic_collection (K := K) p hp

/-- The chi0 form retains its Hpull origin beside the same -1019 normalization. -/
theorem actual_chi0_H_metric_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originPole (originalChi0LowHDensity p u + originalJointMetricDensity p) =
      -(1019 / 750 : K) * (WPFiniteNC122.h p) ^ 2 -
        (WPFiniteNC122.h p / 3) * (HpullK (K := K) p).coeff 0 := by
  rw [originPole_add, actual_chi0_LowH_density p hp u hu, actual_joint_metric_density p hp]
  linear_combination (WPFiniteNC122.h p : K) ^ 2 * harmonic_collection (K := K) p hp

/-- The exact uncollected original mixed Green source. No component residue is presumed zero. -/
noncomputable def remainingOriginalCollector (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  rootMixedDensity p hp u -
    (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) +
      originalGBDensity p u + originalG2Density p u +
      (originalLowHDensity p u + originalJointMetricDensity p))

/-- This is the chi0 form of the same remaining whole collector, with its one conversion carrier. -/
noncomputable def remainingChi0Collector (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  rootMixedDensity p hp u -
    (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) +
      originalGBDensity p u + originalG2Density p u +
      (originalChi0LowHDensity p u + originalJointMetricDensity p))

/-- The two open collectors differ by exactly the original chi0 H conversion, as whole sources. -/
theorem actual_remaining_chi0_conversion (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    remainingChi0Collector p hp u = remainingOriginalCollector p hp u + chi0OriginDensity p := by
  dsimp only [remainingChi0Collector, remainingOriginalCollector, originalChi0LowHDensity]
  ring

/-- The corresponding origin difference is exactly h*Hpull(0)/3 and is never set to zero. -/
theorem actual_remaining_chi0_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    originPole (remainingChi0Collector p hp u) =
      originPole (remainingOriginalCollector p hp u) +
        (WPFiniteNC122.h p / 3) * (HpullK (K := K) p).coeff 0 := by
  rw [actual_remaining_chi0_conversion p hp u, originPole_add, actual_chi0_origin_density p hp]

/-- Every evaluated original source attaches to actual NC77; only the explicit mixed collector remains. -/
theorem actual_NC77_original_sources_unreduced (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u +
        φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
        endProductActualGB p u + actualNativeG2Residue p -
        (1019 / 750 : K) * (WPFiniteNC122.h p) ^ 2 +
        originPole (remainingOriginalCollector p hp u) := by
  have hs := actual_NC77_root_rho_unreduced (K := K) p hp u hu
  have hr : rootMixedDensity p hp u =
      mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) +
        originalGBDensity p u + originalG2Density p u +
        (originalLowHDensity p u + originalJointMetricDensity p) +
        remainingOriginalCollector p hp u := by
    dsimp only [remainingOriginalCollector]
    ring
  rw [hr, originPole_add, originPole_add, originPole_add, originPole_add,
    actual_GB_density_attachment p hp u, actual_G2_density_attachment p hp u hu,
    actual_original_H_metric_collection p hp u hu] at hs
  linear_combination hs

/-- The same actual scalar in chi0 form retains its explicit origin correction exactly once. -/
theorem actual_NC77_chi0_sources_unreduced (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u +
        φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
        endProductActualGB p u + actualNativeG2Residue p -
        (1019 / 750 : K) * (WPFiniteNC122.h p) ^ 2 -
        (WPFiniteNC122.h p / 3) * (HpullK (K := K) p).coeff 0 +
        originPole (remainingChi0Collector p hp u) := by
  rw [actual_remaining_chi0_origin p hp u]
  linear_combination actual_NC77_original_sources_unreduced (K := K) p hp u hu

/- Exact missing source attachment: the original IR63e/IR64d/IR66h mixed
Green collection must identify rootMixedDensity with the sum printed in
remainingOriginalCollector up to a source with proved zero origin residue.
This requires the SAME full j derivative, the reflected HF Sigma carrier,
the CM proper metric and the joint conic source to be collected together.
NativeClosureLowHActualCollection supplies the root H/Xi and original CB
rows, but does not identify this whole corrected mixed source. The chi0
version must retain chi0OriginDensity and its proved h*Hpull(0)/3 residue.
No assertion about either remaining collector's residue is made here. -/

/- Retained rejected step: the first source-only rootMixedDensity omitted
the term -Abar*Hpull*D(actualBracketQK). Expanding actualVmix showed that
actual_full_native_root_rho_source could not follow by ring. The definition
now retains this term; it supplies the original positive Ksrc(Q) derivative
in the mixed H collection. The separated GKQ value remains the same. -/

end WPFieldAssembly.NativeJointSuccessorScalarSource
