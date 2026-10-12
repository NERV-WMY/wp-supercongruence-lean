import WPFieldAssembly.NativeJointSuccessorActualContraction
import WPFieldAssembly.AllPrimesLiteral
import WPFieldAssembly.LiteralMomentBridge

namespace WPFieldAssembly.ScalarFinalSuccessorAllPrime

/-
STATEMENT_FIDELITY: this is the terminal assembly of the literal
NativeJointSuccessorActualContraction.actual_NC77_corrected_finite_consumer
with WPActualFinalConsumer.actual_corrected_consumer. Both use scale one and
the corrected term -2233q^2/125. The first is the complete actual source
identity; the second evaluates its exact finite alphabet. ActualThreePhase.φ
and ActualScalarClosure.scalarMap are the same prime-field embedding.

Both conic coordinates u^2=1/5 and w^2=3/11 are obtained in one faithful
algebraic closure. The source theorem retains both prime classes and either
quadratic branch. Injective descent proves the SAME actualNC77Scalar=actualP;
the checked full-moment and literal bridges retain the original range-p sum
and its weight 532n^2+126n+9, including the retained 7/11/13/17 endpoints.

The source, compiler and review boundaries are recorded in
SCALAR_ALL_PRIME_RECOVERY_2026-10-12.md. Completion requires the genuine native
producer, this module's affected FIVE and the applicable final major-result
review. No native source equation or scalar value is a theorem premise here.
-/

variable {K : Type*} [Field K]

/-- Either pair of actual conic roots closes the complete mapped scalar difference. -/
theorem actual_NC77_mapped_difference_zero
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    ActualScalarClosure.scalarMap (K := K) p
        (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) -
      ActualScalarClosure.scalarMap (K := K) p
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) = 0 := by
  have hnative :=
    NativeJointSuccessorActualContraction.actual_NC77_corrected_finite_consumer
      (K := K) p hp u w hu hw
  have hfinite : NativeJointSuccessorFiniteNormalizer.correctedFiniteConsumer p u = 0 := by
    simpa only [NativeJointSuccessorFiniteNormalizer.correctedFiniteConsumer] using
      (WPActualFinalConsumer.actual_corrected_consumer (K := K) p hp u hu)
  change ActualThreePhase.φ (K := K) p
      (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) -
    ActualThreePhase.φ (K := K) p
      (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) = 0
  exact hnative.trans hfinite

/-- Faithful algebraic-closure descent identifies the SAME original scalar for every prime at least 19. -/
theorem actual_NC77_scalar_eq_actualP
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
      (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) := by
  obtain ⟨u, w, hu, hw⟩ := AllPrimesLiteral.exists_joint_faithful_coordinates p
  exact
    (ActualScalarClosure.actual_scalar_iff_mapped_difference_zero
      (K := AlgebraicClosure (ZMod p)) p hp).mpr
      (actual_NC77_mapped_difference_zero
        (K := AlgebraicClosure (ZMod p)) p hp u w hu hw)

/-- The complete original actual moment has its required three-digit value. -/
theorem actual_full_moment_congruence
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPLiteralAdapter.fullActualMoment p)
      ((1728 : ℚ)^p / 45000) :=
  (LiteralMomentBridge.actual_NC77_scalar_iff_full_moment p hp).mp
    (actual_NC77_scalar_eq_actualP p hp)

/-- The original sum with weight 532n^2+126n+9 satisfies the full all-prime target. -/
theorem all_primes_literal_congruence
    (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  apply LiteralAssembly.literal_of_large_prime_endpoint p hp
  intro hp19
  exact LiteralAssembly.literal_of_full_actual_moment p hp19
    (actual_full_moment_congruence p hp19)

end WPFieldAssembly.ScalarFinalSuccessorAllPrime
