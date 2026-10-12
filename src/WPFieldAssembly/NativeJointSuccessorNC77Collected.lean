import WPFieldAssembly.NativeJointSuccessorScalarSource
import WPFieldAssembly.NativeJointSuccessorMixedGreenCore

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorActualContraction

open ActualBpairContraction ActualThreePhase ActualSimplePoleResidue
  NativeClosureMixedSource NativeJointSuccessorScalarSource
  NativeJointSuccessorMixedGreenCore NativeJointSuccessorRhoReduction

variable {K : Type*} [Field K]

/-- The same actual NC77 source closes its remaining whole Green density. -/
theorem actual_NC77_sources_collected (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    φ (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      φ (K := K) p (actualDividedVbalScalar p hp) + originalRhoSourceValue p hp u +
        φ (K := K) p (NativeScalarRows.actualGKQ (K := ZMod p) p) +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
        endProductActualGB p u + actualNativeG2Residue p -
        (1019 / 750 : K) * (WPFiniteNC122.h p) ^ 2 := by
  rw [actual_NC77_original_sources_unreduced p hp u hu,
    actual_remaining_original_Green_origin p hp u, add_zero]

end WPFieldAssembly.NativeJointSuccessorActualContraction
