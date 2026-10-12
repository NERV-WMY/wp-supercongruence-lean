import WPActualCentralResidueSource
import WPActualPartialHarmonic

open scoped LaurentPolynomial
open WPActualPullbackSource WPActualEtaPole WPActualEtaIntegrality WPActualEtaPrimitive
  WPActualGaussBottom
  WPPIntegralReduction WPActualPartialHarmonic

namespace WPFirstResidue.LiteralNormalization

/-- The NC69 rational lift uses the three exact integer Fermat quotients. -/
noncomputable def literalR0 (p : ℕ) : ℚ :=
  -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
    (3 / 2 : ℚ) * ((WPFiniteInversion.integerFermatQuotient p 3 : ℚ) +
      (WPFiniteInversion.integerFermatQuotient p 5 : ℚ))

noncomputable def integralHalf (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by norm_num) (by omega)⟩

noncomputable def integralLiteralR0 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  -2 * (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
    3 * integralHalf p hp *
      ((WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p) +
        (WPFiniteInversion.integerFermatQuotient p 5 : integralRationals p))

theorem integralLiteralR0_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralLiteralR0 p hp).val = literalR0 p := by
  change (integralRationals p).subtype (integralLiteralR0 p hp) = _
  simp only [integralLiteralR0, map_sub, map_mul, map_neg, map_ofNat, map_intCast]
  change -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
    3 * (1 / 2 : ℚ) * ((WPFiniteInversion.integerFermatQuotient p 3 : ℚ) +
      (WPFiniteInversion.integerFermatQuotient p 5 : ℚ)) = _
  unfold literalR0
  ring

theorem literalR0_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (literalR0 p) := by
  rw [← integralLiteralR0_value p hp]
  exact (integralLiteralR0 p hp).property

theorem integralHalf_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (integralHalf p hp) = (1 / 2 : ZMod p) := by
  change ((1 / 2 : ℚ) : ZMod p) = _
  norm_num [Rat.cast_def]

theorem literalR0_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (literalR0 p : ZMod p) =
      -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        (3 / 2 : ZMod p) *
          ((WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) +
            (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)) := by
  rw [← integralLiteralR0_value p hp]
  change residueHom p (integralLiteralR0 p hp) = _
  simp only [integralLiteralR0, map_sub, map_mul, map_neg, map_ofNat, map_intCast,
    integralHalf_residue]
  rw [map_add, map_intCast, map_intCast]
  ring

/-- This is a field equality only; it does not replace the rational lift before division. -/
theorem harmonic_literalR0 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fieldHarmonic p (p / 6) -
      (3 / 2 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) =
        (literalR0 p : ZMod p) := by
  rw [actual_harmonic_sixth p (by omega), literalR0_residue p hp]
  ring

/-- The actual full-cutoff rational central residue, with neither endpoint truncated. -/
noncomputable def actualFirstResidue (p : ℕ) : ℚ :=
  actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0

theorem actualFirstResidue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualFirstResidue p) := by
  have hP := actual_Peta_integral p (p - 1 - p / 6) (by omega) (by omega) (by omega)
  have hv : 0 ≤ padicValRat p
      ((Peta p ((p - 1) / 2) (p - 1 - p / 6)).coeff (-1)) := hP (-1)
  simpa only [actualFirstResidue, actualResidue, zero_mul, zero_sub] using hv

end WPFirstResidue.LiteralNormalization
