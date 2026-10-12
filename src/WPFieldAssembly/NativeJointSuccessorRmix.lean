import WPFieldAssembly.NativeClosureWholeSource
import WPFieldAssembly.NativeJointSuccessorWneedCore
import WPFieldAssembly.NativeJointSuccessorRroot

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorRmix

open ActualBpairContraction ActualBpairLowHLocalPole ActualSimplePoleResidue
open NativeClosureMixedSource NativeJointSuccessorJSeries
open NativeJointSuccessorWneedCore WPFiniteLaurentDifferential
open NativeJointSuccessorRroot

variable {K : Type*} [Field K]

private theorem four_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 : K) ≠ 0 :=
  WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))

/-- The actual IR63b coefficient adds the entire Laurent correction to the same universal source. -/
noncomputable def actualVmix (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[T;T⁻¹] :=
  actualUniversalV (K := K) p u + actualDeltaCarrier p

/-- All original residual and mapped proper sources stay inside the corrected whole remainder. -/
noncomputable def actualRmix (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  actualMarkedResidualDensity (K := K) p u (four_ne_zero p hp) +
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
      (SourceClosureCommonWholeSource.wholeTraceProperNativeDensity p hp) -
    actualDeltaCarrier p * (33 - 12 * T 1) +
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualDeltaCarrier p)

/-- The correction is the complete Dsym*j and reciprocal-even IR63b source, before differentiation. -/
theorem actual_delta_IR63b_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (actualDeltaCarrier p : K[T;T⁻¹]) =
      (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (Dsym p : K[T;T⁻¹]) *
          actualJSeries p +
        (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (Dstar p : K[X]).toLaurent *
          localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)) := by
  simpa only [actualDeltaSeries] using (actual_delta_Laurent (K := K) p hp).symm

/-- The same universal coefficient acquires the original whole j and E(Q) source. -/
theorem actual_Vmix_IR63b_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    localFiniteSeriesHom (actualVmix (K := K) p u) =
      localFiniteSeriesHom (actualUniversalV (K := K) p u) +
        ((2 / 5 : LaurentSeries K) * localFiniteSeriesHom (Dsym p : K[T;T⁻¹]) *
            actualJSeries p +
          (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (Dstar p : K[X]).toLaurent *
            localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
              LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) := by
  rw [actualVmix, map_add, actual_delta_IR63b_source p hp]

/-- This prints the original whole Rmix, with the mapped common and proper density retained. -/
theorem actual_Rmix_whole_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualRmix (K := K) p hp u =
      actualMarkedResidualDensity (K := K) p u h4 +
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (SourceClosureCommonWholeSource.wholeTraceProperNativeDensity p hp) -
        actualDeltaCarrier p * (33 - 12 * T 1) +
        (WPFiniteZSource.Abar : K[X]).toLaurent *
          (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualDeltaCarrier p) := by
  rfl

/-- The root residual cancellation preserves its original endpoints and whole proper metric in Rmix. -/
theorem actual_Rmix_Rroot_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualRmix (K := K) p hp u =
      actualRroot (K := K) p u h4 +
        WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
          (SourceClosureCommonWholeSource.wholeTraceProperNativeDensity p hp) -
        actualDeltaCarrier p * (33 - 12 * T 1) +
        (WPFiniteZSource.Abar : K[X]).toLaurent *
          (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualDeltaCarrier p) := by
  rw [actual_Rmix_whole_source p hp u h4, actual_marked_residual_Rroot p hp u h4]

/-- The IR63b replacement preserves the entire original native density, including invisible slots. -/
theorem actual_full_native_mixed_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualFullNativeDensity (K := K) p hp u h4 =
      actualVmix p u * (33 - 12 * T 1) -
        (WPFiniteZSource.Abar : K[X]).toLaurent *
          (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualVmix p u) +
        actualRmix p hp u := by
  unfold actualFullNativeDensity actualUniversalDensity actualVmix actualRmix
  rw [map_add]
  ring

/-- The same actual NC77 scalar and divided Vbal now use the original corrected mixed origin. -/
theorem actual_NC77_mixed_native_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p (actualDividedVbalScalar p hp) +
        originPole (actualVmix p u * (33 - 12 * T 1) -
          (WPFiniteZSource.Abar : K[X]).toLaurent *
            (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualVmix p u) +
          actualRmix p hp u) := by
  rw [actualNC77Scalar_full_native_origin p hp u hu (four_ne_zero p hp),
    actual_full_native_mixed_density p hp u (four_ne_zero p hp)]

/-- Splitting the same mixed origin exposes an actual residual residue without assigning its value. -/
theorem actual_NC77_mixed_split_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p (actualDividedVbalScalar p hp) +
        originPole (actualVmix p u * (33 - 12 * T 1) -
          (WPFiniteZSource.Abar : K[X]).toLaurent *
            (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualVmix p u)) +
        originPole (actualRmix p hp u) := by
  rw [actual_NC77_mixed_native_origin p hp u hu, originPole_add]
  ring

end WPFieldAssembly.NativeJointSuccessorRmix
