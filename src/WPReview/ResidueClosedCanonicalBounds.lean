import WPGammaClosedNumeratorBounds
import WPReview.ResidueNumeratorNormalization

noncomputable section

namespace WPReview.ResidueClosedCanonicalBounds

open scoped BigOperators
open WPResidueQuotient WPReview.ResidueNumeratorOperators

/-!
The actual closed numerator domain includes both strict and boundary
numerators. The strict canonical bound and the six-list boundary bound
together supply the uniform loss five on this entire domain. A stronger
boundary loss four remains subject to its proved zero-exponent hypothesis.
-/

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

theorem actual_closed_classes_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) : ∃ w : WPGammaClosedNumeratorBounds.Space p,
    qNumerator ℤ_[p] a n ha =
      (p : ℤ)^(((n/p)-5)/5) • WPGammaClosedNumeratorBounds.fullSection p hp7 w := by
  by_cases hs : (∑ i, a i) ≤ n
  · obtain ⟨v, hv⟩ := ResidueNumeratorNormalization.strict_classes_canonical_bound p hp7 a n hs
    refine ⟨(v, 0), ?_⟩
    simpa only [WPGammaClosedNumeratorBounds.fullSection,
      ResidueClosedConnection.fullSection_apply, map_zero, add_zero,
      WPGammaIntegralLift.gammaSection] using hv
  · exact WPGammaClosedNumeratorBounds.closed_classes_bound p hp7 a n (by omega)

theorem actual_closed_coordinates_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n + 1) (v : WPGammaClosedNumeratorBounds.Space p)
    (hv : WPGammaClosedNumeratorBounds.fullSection p hp7 v = qNumerator ℤ_[p] a n ha) :
    ∃ w : WPGammaClosedNumeratorBounds.Space p, v = (p : ℤ)^(((n/p)-5)/5) • w := by
  obtain ⟨w, hw⟩ := actual_closed_classes_bound p hp7 a n ha
  refine ⟨w, ?_⟩
  apply ResidueClosedConnection.integral_fullSection_injective p hp7
  change WPGammaClosedNumeratorBounds.fullSection p hp7 v =
    WPGammaClosedNumeratorBounds.fullSection p hp7 ((p : ℤ)^(((n/p)-5)/5) • w)
  rw [map_zsmul, hv, hw]

end WPReview.ResidueClosedCanonicalBounds
