import WPFieldAssembly.LiteralAssembly
import WPMomentPrecision.MomentToField
import WPScalarMarkedBridge.RationalLaw

open scoped BigOperators

namespace WPFieldAssembly.LiteralMomentBridge

/-- Both producers use the complete range-p sum with the same literal terms. -/
theorem fullActualMoment_eq_native_sum (p : ℕ) :
    WPLiteralAdapter.fullActualMoment p =
      ∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
        WPNativeMomentIntegrality.actualMonomialMoment p n := rfl

/-- The actual scalar decision is exactly the three-digit full moment target. -/
theorem actual_NC77_scalar_iff_full_moment
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) ↔
      WPReview.RationalCongruent p 3 (WPLiteralAdapter.fullActualMoment p)
        ((1728 : ℚ)^p / 45000) := by
  rw [fullActualMoment_eq_native_sum]
  exact (WPMomentPrecision.MomentToField.actual_full_native_value_NC77_iff p hp).symm

/-- The original literal target decides the same actual NC77 scalar, including p=19. -/
theorem actual_NC77_scalar_iff_literal
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) ↔
      WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) :=
  (actual_NC77_scalar_iff_full_moment p hp).trans
    (WPFieldAssembly.LiteralAssembly.literal_iff_full_actual_moment p hp).symm

/-- The older integral marked chart keeps its own exclusion of p=19. -/
theorem marked_scalar_residual_iff_actual_NC77_scalar
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (hp19 : p ≠ 19) :
    WPScalarMarkedBridge.actualScalarResidual p (by omega) (by omega) hp19 ∈
        Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p]) ↔
      WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) :=
  (WPScalarMarkedBridge.actual_scalar_residual_iff_literal
    p (by omega) (by omega) hp19).trans
      (actual_NC77_scalar_iff_literal p hp).symm

/-- The actual field scalar at nineteen follows from its retained literal endpoint. -/
theorem actual_NC77_scalar_nineteen [Fact (Nat.Prime 19)] :
    WPMomentPrecision.MomentToField.actualNC77Scalar 19 (by norm_num) =
      (WPMomentPrecision.MomentPrecision.actualP 19 : ZMod 19) :=
  (actual_NC77_scalar_iff_literal 19 (by norm_num)).mpr WPReview.literal_nineteen

/-- Only the honest actual scalar equality remains in the large-prime consumer. -/
theorem literal_of_actual_NC77_scalar
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hscalar : WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
      (WPMomentPrecision.MomentPrecision.actualP p : ZMod p)) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  exact WPFieldAssembly.LiteralAssembly.literal_of_full_actual_moment p hp
    ((actual_NC77_scalar_iff_full_moment p hp).mp hscalar)

/-- The retained small primes reduce the all-prime target to actual scalar closure. -/
theorem all_primes_literal_of_actual_large_prime_scalar
    (hscalar : ∀ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p),
      WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p))
    (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  apply WPFieldAssembly.LiteralAssembly.literal_of_large_prime_endpoint p hp
  intro hp19
  exact literal_of_actual_NC77_scalar p hp19 (hscalar p hp19)

end WPFieldAssembly.LiteralMomentBridge
