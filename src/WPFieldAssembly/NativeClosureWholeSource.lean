import WPFieldAssembly.NativeClosureUniversalSource
import WPFieldAssembly.SourceClosureCommonWholeSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction
open WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- The whole actual Vbal remains a rational divided source outside the collected native origin. -/
noncomputable def actualDividedVbalScalar (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  (2 / 3 : ZMod p) * residueHom p (vBalancedDividedIntegral p hp) -
    103 * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 / 1000

/-- This is the complete original common, balanced, period and proper source collection. -/
theorem actualRetainedTrace_common_origin {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (g : ZMod p →+* K) :
    g (actualRetainedTraceScalar p hp) = g (actualDividedVbalScalar p hp) +
      originPole (WPActualChiSource.coefficientMap g
        (SourceClosureCommonWholeSource.wholeTraceProperNativeDensity p hp)) := by
  have ht := SourceClosureCommonWholeSource.actual_whole_trace_proper_native_origin_transport
    p hp g
  have he : actualRetainedTraceScalar p hp = actualDividedVbalScalar p hp +
      ((2 / 3 : ZMod p) *
        (residueHom p (commonSourceTraceIntegral p hp) +
          residueHom p (balancedTraceIntegral p hp) -
          residueHom p (periodCarryIntegral p hp)) +
        (2 / 3 : ZMod p) * ActualDeltaUNextSource.QO p
          (SourceClosureCommonWholeSource.properSource p)) := by
    unfold actualRetainedTraceScalar actualDividedVbalScalar
      SourceClosureCommonWholeSource.properSource
    ring
  rw [he, map_add, ht]

variable {K : Type*} [Field K]

/-- No actual common or proper term remains outside this whole original native density. -/
noncomputable def actualFullNativeDensity (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  actualUniversalDensity (K := K) p u h4 +
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
      (SourceClosureCommonWholeSource.wholeTraceProperNativeDensity p hp)

/-- The SAME NC77 scalar retains its actual divided Vbal and one complete native origin source. -/
theorem actualNC77Scalar_full_native_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (h4 : (4 : K) ≠ 0) :
    ActualThreePhase.φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      ActualThreePhase.φ (K := K) p (actualDividedVbalScalar p hp) +
        originPole (actualFullNativeDensity (K := K) p hp u h4) := by
  rw [actualNC77Scalar_universal_origin p hp u hu h4,
    actualRetainedTrace_common_origin p hp (ActualThreePhase.φ p),
    actualFullNativeDensity, originPole_add]
  ring

end WPFieldAssembly.ActualBpairContraction
