import WPGammaNumeratorBounds

noncomputable section

namespace WPReview.ResidueNumeratorNormalization

open scoped BigOperators
open WPResidueQuotient WPReview.ResidueNumeratorOperators

def normalizedExponent (a : Fin 6 → ℕ) : Fin 6 → ℕ :=
  canonicalAsNat (latticeQ (fun i => (a i : ℤ)))

theorem normalizedExponent_sum_le (a : Fin 6 → ℕ) :
    (∑ i, normalizedExponent a i) ≤ ∑ i, a i := by
  rw [normalizedExponent, canonicalAsNat_sum]
  exact latticeQ_nonnegative_degree_le a

theorem normalizedExponent_has_zero (a : Fin 6 → ℕ) :
    ∃ i, normalizedExponent a i = 0 := by
  obtain ⟨i, hi⟩ := (canonicalRepresentative_isCanonical
    (latticeQ (fun i => (a i : ℤ)))).2
  exact ⟨i, by simp [normalizedExponent, canonicalAsNat, hi]⟩

theorem numeratorGenerator_normalized {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) :
    numeratorGenerator u a n = numeratorGenerator u (normalizedExponent a) n := by
  rw [numeratorGenerator_eq_canonical, canonicalNumeratorGenerator_as_nonnegative]
  rfl

variable (K : Type*) [CommRing K]

theorem qNumerator_normalized (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) :
    qNumerator K a n ha = qNumerator K (normalizedExponent a) n
      ((normalizedExponent_sum_le a).trans ha) := by
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact numeratorGenerator_normalized (parameter K) a n

section Integral

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

include hp7 in
theorem strict_classes_canonical_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) : ∃ w : WPGammaIntegralLift.Space p,
    qNumerator ℤ_[p] a n (by omega) =
      (p : ℤ)^(((n/p)-5)/5) • WPGammaIntegralLift.gammaSection p w := by
  rw [qNumerator_normalized]
  exact WPGammaNumeratorBounds.strict_classes_zero_exponent_bound p hp7
    (normalizedExponent a) n ((normalizedExponent_sum_le a).trans ha)
    (normalizedExponent_has_zero a)

theorem strict_coordinates_normalized (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) :
    strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) a n =
      strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7)
        (normalizedExponent a) n := by
  apply (ResidueConnection.integral_gammaSection_injective p)
  rw [actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp7) a n ha,
    actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp7) (normalizedExponent a) n
      ((normalizedExponent_sum_le a).trans ha)]
  exact qNumerator_normalized ℤ_[p] a n (by omega)

theorem strict_coordinates_canonical_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) : ∃ w : WPGammaIntegralLift.Space p,
    strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) a n =
      (p : ℤ)^(((n/p)-5)/5) • w := by
  rw [strict_coordinates_normalized p hp7 a n ha]
  exact WPGammaNumeratorBounds.strict_coordinates_zero_exponent_bound p hp7
    (normalizedExponent a) n ((normalizedExponent_sum_le a).trans ha)
    (normalizedExponent_has_zero a)

end Integral

end WPReview.ResidueNumeratorNormalization
