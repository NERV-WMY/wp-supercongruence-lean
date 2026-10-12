import WPFieldAssembly.NativeJointSuccessorScalarSource
import WPFieldAssembly.NativeJointSuccessorLowHRootCollection

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource

namespace WPFieldAssembly.NativeJointSuccessorHCollector

open ActualBpairContraction ActualGreenResidue ActualThreePhase
  NativeClosureLowH ActualBpairLowHLocalPole
  NativeJointSuccessorRroot NativeJointSuccessorCBMixed
  NativeJointSuccessorWneedCore NativeJointSuccessorScalarSource

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: the root H/Xi and CB sources are collected before
any pole evaluation. The original P-A/3 slot is kept. The literal six
IR64d--IR66h completion terms retain both reciprocal phases and the full
-(2/5)*phi*Dsym*(dx/(2x)+dA/3) row. The resulting non-H density and
remaining mixed H/HF completion are separate actual Laurent sources;
neither is assigned a scalar value. -/

private theorem four_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (4 : K) ≠ 0 :=
  WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))

/-- The original B0 is the same complete CB multiplier used by the actual LowH proof. -/
theorem actual_IR63B0_native_CB_multiplier (p : ℕ) [Fact p.Prime] [CharP K p] :
    actualIR63B0 (K := K) p = nativeActualCBMultiplier p := by
  rfl

/-- These are precisely the six additional original IR64d--IR66h H rows after Xi. -/
noncomputable def originalHCompletion (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  let A := (actualAK (K := K) p).toLaurent
  let v := invert A
  let P := WPFiniteZSource.P p u
  let Ds := (Dstar p : K[X]).toLaurent
  let Xn := T (((p - 1) / 2 : ℕ) : ℤ)
  let ph := 4 * T (-(p : ℤ)) - 11
  let y := (lowHCubicY (nativeH (K := K) p)).toLaurent
  let yq := lowHLinearYQLog (nativeH (K := K) p)
  let z := lowHLinearYOverX (nativeH (K := K) p)
  let Q := (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent
  let h := WPFiniteNC122.h (K := K) p;
  -LaurentPolynomial.C (5 / 3 : K) * (v - LaurentPolynomial.C (WPFiniteNC122.q p - h)) * Q -
    LaurentPolynomial.C (2 / 3 : K) * (Ds + invert P) * (y * D v) +
    LaurentPolynomial.C (2 / 9 : K) *
      ((v + LaurentPolynomial.C h) - (1 + Xn) * (A + LaurentPolynomial.C h)) * (y * D v) -
    LaurentPolynomial.C (1 / 9 : K) * (A + Xn * (A + LaurentPolynomial.C h)) * yq -
    LaurentPolynomial.C (1 / 3 : K) * invert P * yq -
    LaurentPolynomial.C (2 / 5 : K) * ph * (Ds + invert Ds) *
      (LaurentPolynomial.C (1 / 2 : K) * z + LaurentPolynomial.C (1 / 3 : K) * (y * D A))

/-- The complete original H source is its literal kernel/Xi plus those six full rows. -/
theorem actual_H_completion_source (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    nativeOriginalHSource p u (nativeH (K := K) p) (literalKB p) (D (literalKB p))
        (WPFiniteNC122.h p) (WPFiniteNC122.q p) =
      nativeRootHKernelXi p u (nativeH p) + originalHCompletion p u := by
  dsimp only [nativeOriginalHSource, nativeRootHKernelXi, originalHCompletion]
  ring

/-- The actual H adjoint and the original two elementary H rows share the complete CB partner. -/
noncomputable def rootHCBSource (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  -(WPFiniteZSource.Abar : K[X]).toLaurent * (HpullK (K := K) p).toLaurent *
      D (actualRootUniversalV p u) +
    (HpullK (K := K) p).toLaurent *
      (-literalKB p * (33 - 12 * T 1) +
        (WPFiniteZSource.Abar : K[X]).toLaurent * literalKB p *
          LaurentPolynomial.C (1 / 2 : K) * T (-1)) +
    (CBK (K := K) p).toLaurent * actualIR63B0 p * (33 - 12 * T 1)

/-- The original CB/CM branch is retained before its finite integration by parts. -/
noncomputable def originalCBMetricBranch (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  -(WPFiniteZSource.Abar : K[X]).toLaurent * actualIR63B0 p * D (CMK (K := K) p).toLaurent +
    LaurentPolynomial.C (3 * WPFiniteNC122.h p) *
      (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * actualIR63B0 p)

/-- The existing complete LowH proof collects the root H/Xi and actual CB branch as whole sources. -/
theorem actual_root_H_CB_kernel_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    rootHCBSource p u =
      (WPFiniteZSource.Abar : K[X]).toLaurent * nativeRootHKernelXi p u (nativeH p) +
        originalCBMetricBranch p := by
  have hRoot := native_actual_root_H_kernel_collection (K := K) p hp u
    (nativeH p) (nativeH_origin p)
  have hCB := native_actual_CB_H_quotient_collection (K := K) p hp (actualIR63B0 p)
  have hyL : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (lowHqCubicDensity (nativeH (K := K) p)).toLaurent =
      (lowHCubicY (nativeH (K := K) p)).toLaurent * (33 - 12 * T 1) := by
    rw [lowH_linear_ylog_polynomial,
      lowHBranchYQuotient_source _ (nativeH_origin p), map_mul]
    simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
    ring
  rw [ActualGreenResidue.hK, ActualCubicNativeSource.actual_harmonic_map p hp] at hCB
  dsimp only [rootHCBSource, originalCBMetricBranch]
  rw [← nativeH_original_Hpull p hp]
  dsimp only [nativeRootHKernelXi, actualIR63B0, lowHLinearYOverX] at hRoot hCB ⊢
  linear_combination (WPFiniteZSource.Abar : K[X]).toLaurent * hRoot + hCB + literalKB p * hyL

/-- Replacing Xi by the complete original LowH source leaves its exact completion density visible. -/
theorem actual_root_H_CB_original_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    rootHCBSource p u = originalLowHDensity p u + originalCBMetricBranch p -
      (WPFiniteZSource.Abar : K[X]).toLaurent * originalHCompletion p u := by
  rw [actual_root_H_CB_kernel_source p hp u, originalLowHDensity, actual_H_completion_source p u]
  ring

/-- The whole CB branch has exactly one total derivative and its retained 3h phase. -/
theorem actual_CB_metric_branch_IBP_source (p : ℕ) [Fact p.Prime] [CharP K p] :
    originalCBMetricBranch (K := K) p =
      (WPFiniteZSource.Abar : K[X]).toLaurent *
          ((CMK (K := K) p).toLaurent * D (actualIR63B0 p)) +
        LaurentPolynomial.C (3 * WPFiniteNC122.h p) *
          (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * actualIR63B0 p) -
        (WPFiniteZSource.Abar : K[X]).toLaurent *
          D (actualIR63B0 p * (CMK (K := K) p).toLaurent) := by
  rw [originalCBMetricBranch, D_mul]
  ring

/-- The exact remaining root density contains no explicit H multiplier; its full CM branch remains. -/
noncomputable def rootNonHDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  actualRootUniversalV p u * (33 - 12 * T 1) + originalCBMetricBranch p +
    LaurentPolynomial.C (WPFiniteNC122.h p) *
      (WPFiniteZSource.Abar : K[X]).toLaurent * literalKB p * T (-1) -
    literalKB p * actualMarkedEndpointSource p u (four_ne_zero p hp) -
    LaurentPolynomial.C (1 / 3 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (φ (K := K) p) (properMetricDensity p)

/-- This single source still couples the original Delta, CB correction, full HF and six H completion rows. -/
noncomputable def mixedHCompletionDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  actualDeltaCarrier p * (33 - 12 * T 1) -
    (WPFiniteZSource.Abar : K[X]).toLaurent * (HpullK (K := K) p).toLaurent * D (actualDeltaCarrier p) +
    -(WPFiniteZSource.Abar : K[X]).toLaurent * (HpullK (K := K) p).toLaurent * D (actualBracketQK p) +
    actualCBDeltaBLCarrier p +
    (HpullK (K := K) p).toLaurent *
      (SourceClosureHFNativeTransport.nativeHFSigmaNumerator p +
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (-(p : ℤ)) - 11) * SourceClosureHFNativeTransport.nativeHFBracket p u) -
    (WPFiniteZSource.Abar : K[X]).toLaurent * originalHCompletion p u

/-- The same complete root mixed source has the original LowH density and these two explicit complements. -/
theorem actual_root_mixed_H_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    rootMixedDensity p hp u =
      originalLowHDensity p u + rootNonHDensity p hp u + mixedHCompletionDensity p u := by
  have hs := actual_root_H_CB_original_source (K := K) p hp u
  dsimp only [rootMixedDensity, rootNonHDensity, mixedHCompletionDensity, actualRroot]
  simp only [map_add]
  dsimp only [rootHCBSource, originalCBMetricBranch] at hs ⊢
  linear_combination hs

/-- The same whole collection in chi0 form keeps its one literal H origin conversion. -/
theorem actual_root_mixed_H_chi0_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    rootMixedDensity p hp u =
      originalChi0LowHDensity p u + chi0OriginDensity p +
        rootNonHDensity p hp u + mixedHCompletionDensity p u := by
  rw [actual_root_mixed_H_collection p hp u]
  dsimp only [originalChi0LowHDensity]
  ring

/-- The previous open collector now has its actual H contraction removed by a whole-source identity. -/
theorem actual_remaining_original_H_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    remainingOriginalCollector p hp u =
      rootNonHDensity p hp u + mixedHCompletionDensity p u -
        (NativeClosureMixedSource.mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) +
          originalGBDensity p u + originalG2Density p u + originalJointMetricDensity p) := by
  rw [remainingOriginalCollector, actual_root_mixed_H_collection p hp u]
  ring

/- The remaining central equality is the joint source collection of
rootNonHDensity + mixedHCompletionDensity with the SAME Nj, GB, G2 and
joint metric/conic densities. In particular the six original completion
rows cannot be deleted before matching the full mixed j/HF/metric source.
No origin-pole premise or value is introduced by this H reduction. -/

end WPFieldAssembly.NativeJointSuccessorHCollector
