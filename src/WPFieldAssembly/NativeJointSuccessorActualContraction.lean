import WPFieldAssembly.NativeJointSuccessorNC77Collected
import WPFieldAssembly.NativeJointSuccessorB2FiniteValue
import WPFieldAssembly.BalancedVbalSuccessorDividedVbalConsumer
import WPFieldAssembly.NativeJointSuccessorFiniteNormalizer

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorActualContraction

open ActualBpairContraction ActualThreePhase ActualSimplePoleResidue
  NativeClosureMixedSource NativeJointSuccessorScalarSource
  NativeJointSuccessorMixedGreenCore NativeJointSuccessorRhoReduction
  NativeJointSuccessorB2Finite NativeJointSuccessorFiniteNormalizer

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: the scalar here is the original actualNC77Scalar,
and the subtracted arithmetic digit is the original actualP. The remaining
whole source is consumed by its actual finite Green derivative. The full
divided Vbal/rho, mapped GKQ, Nj, GB and G2 are then collected at scale one.
The original chi0 conversion remains inside the source proofs and is not
applied again. No final consumer evaluation is imported or presumed. -/

/-- Actual divided Vbal and the entire rho combine with the same GKQ and Nj to finite B2. -/
theorem actual_vbal_rho_B2_collected (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u +
        φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      finiteB2Alphabet p u + (287 / 600 : K) * (WPFiniteNC122.h p) ^ 2 := by
  have hv : φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u =
      ActualVbalFieldClosure.vbalMomentConsumer p u w +
        SourceClosureWholeTraceCollection.originalUVFiniteRemainder p u +
        SourceClosureNormalizedZFinite.normalizedZFiniteValue p u +
        (287 / 600 : K) * (WPFiniteNC122.h p) ^ 2 := by
    simpa only [originalRhoSourceValue, fullWneedCarrier] using
      (BalancedVbalSuccessorRhoEvaluation.actual_divided_Vbal_rho_joint_consumer
        (K := K) p hp u w hu hw)
  have hb := actual_finite_B2_value (K := K) p hp u w hu hw
  rw [actual_GKQ_coefficient_transport p hp]
  dsimp only [actualFiniteB2] at hv hb ⊢
  linear_combination hv + hb

/-- The original actual NC77 scalar minus its actual P is the full corrected consumer at scale one. -/
theorem actual_NC77_corrected_finite_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) -
        φ (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) =
      correctedFiniteConsumer p u := by
  have hs := actual_NC77_sources_collected (K := K) p hp u hu
  have hb := actual_vbal_rho_B2_collected (K := K) p hp u w hu hw
  have hn := actual_finite_B2_normalization (K := K) p hp u hu
  linear_combination hs + hb + hn

/-- Mapping the SAME original scalar difference preserves the full scale-one contraction. -/
theorem actual_NC77_difference_corrected_finite_consumer
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    φ (K := K) p
        (WPMomentPrecision.MomentToField.actualNC77Scalar p hp -
          (WPMomentPrecision.MomentPrecision.actualP p : ZMod p)) =
      correctedFiniteConsumer p u := by
  rw [map_sub]
  exact actual_NC77_corrected_finite_consumer p hp u w hu hw

end WPFieldAssembly.NativeJointSuccessorActualContraction
