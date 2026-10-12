import WPFieldAssembly.NativeClosureWholeSource
import WPFieldAssembly.NativeJointSuccessorWneedCore
import WPFieldAssembly.SourceClosureHFBranchFactor
import WPFieldAssembly.BalancedVbalSuccessorHFBracketDefinition

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource

namespace WPFieldAssembly.NativeJointSuccessorRhoReduction

open ActualGreenResidue ActualSimplePoleResidue ActualThreePhase
  SourceClosureCommonWholeSource SourceClosureHFNativeTransport
  NativeJointSuccessorWneedCore

variable {K : Type*} [Field K]

/-- The entire Laurent Wneed; its original negative Frobenius phase remains explicit. -/
noncomputable def fullWneedCarrier (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  actualWneedCoreCarrier p + (HpullK (K := K) p).toLaurent *
    (nativeHFSigmaNumerator p +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (4 * T (-(p : ℤ)) - 11) * nativeHFBracket p u)

/-- This is rho at its actual whole mapped proper/common Laurent source. -/
noncomputable def originalRhoSourceValue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K :=
  originPole
    (coefficientMap (φ (K := K) p) (wholeTraceProperNativeDensity p hp) -
      fullWneedCarrier p u)

end WPFieldAssembly.NativeJointSuccessorRhoReduction
