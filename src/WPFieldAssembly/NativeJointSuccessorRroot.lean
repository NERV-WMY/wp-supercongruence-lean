import WPFieldAssembly.NativeClosureUniversalSource
import WPFieldAssembly.ActualCubicNativeSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource

namespace WPFieldAssembly.NativeJointSuccessorRroot

open ActualBpairContraction WPFiniteLaurentDifferential ActualCubicNativeSource

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- The original CB partner before the corrected mixed DeltaB is added. -/
noncomputable def actualIR63B0 (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  -2 * (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) * literalKB p +
    LaurentPolynomial.C (5 / 12 : K) * T (p : ℤ) * actualR52 p

/-- The whole native residual retains its endpoint and original proper metric. -/
noncomputable def actualRroot (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (h4 : (4 : K) ≠ 0) : K[T;T⁻¹] :=
  (ActualThreePhase.CBK (K := K) p).toLaurent * actualIR63B0 p * (33 - 12 * T 1) +
    (ActualGreenResidue.HpullK (K := K) p).toLaurent *
      (-literalKB p * (33 - 12 * T 1) +
        (WPFiniteZSource.Abar : K[X]).toLaurent * literalKB p *
          LaurentPolynomial.C (1 / 2 : K) * T (-1)) +
    LaurentPolynomial.C (WPFiniteNC122.h p) *
      (WPFiniteZSource.Abar : K[X]).toLaurent * literalKB p * T (-1) -
    literalKB p * actualMarkedEndpointSource p u h4 -
    LaurentPolynomial.C (1 / 3 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (ActualThreePhase.φ (K := K) p) (properMetricDensity p)

/-- Opposite Euler-bracket sources cancel before any origin value is assigned. -/
theorem actual_marked_residual_Rroot (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualMarkedResidualDensity (K := K) p u h4 = actualRroot p u h4 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hh : ActualGreenResidue.hK (K := K) p = WPFiniteNC122.h p :=
    actual_harmonic_map p hp
  have hhalf : 2 * LaurentPolynomial.C (1 / 2 : K) = (1 : K[T;T⁻¹]) := by
    change LaurentPolynomial.C (2 : K) * LaurentPolynomial.C (1 / 2 : K) = 1
    rw [← map_mul, mul_one_div_cancel h2, map_one]
  unfold actualMarkedResidualDensity actualMarkedNonfDensity actualRroot actualIR63B0
  rw [hh]
  linear_combination
    ((WPFiniteZSource.Abar : K[X]).toLaurent * literalKB (K := K) p * T (-1) *
      LaurentPolynomial.C (WPFiniteNC122.h p)) * hhalf

end WPFieldAssembly.NativeJointSuccessorRroot
