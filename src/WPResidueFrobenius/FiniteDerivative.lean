import WPResidueFrobenius.Binomial

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators

/-- An algebraic helper for the finite pullback. Its hypotheses are instantiated
by the actual localized derivation below; the retained tail is part of the identity. -/
theorem finite_binomial_derivative {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p r N : ℕ) (hr : 1 ≤ r)
    (P dP A e X df phiDf dG : R)
    (hP : D P = (p : R)*dP)
    (hA : D A = -(p : R)*(r : R)*A*e*df)
    (hX : D X = (p : R)*phiDf*e^p - (p : R)*df*e*(1+X))
    (hG : phiDf*e^p-df*e = e^p*dG) :
    D (P*A*binomialPartial r (N+1) X) - (p : R)*
      (dP*A*binomialPartial r (N+1) X -
        (r : R)*P*phiDf*A*e^p*binomialPartial (r+1) (N+1) X) =
      (p : R)*(r : R)*P*A*e^p*algebraMap ℚ R (binomialWeight (r+1) N)*X^N*dG := by
  rw [Derivation.leibniz, Derivation.leibniz, derivation_binomialPartial,
    binomialPartial_derivative r N hr X]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  rw [hP, hA, hX, binomialPartial_succ (r+1) N]
  have hs := binomialPartial_raise r N X
  rw [binomialPartial_succ (r+1) N, pow_succ] at hs
  have hg := hG
  linear_combination
    (p : R)*(r : R)*P*A*df*e*hs +
      (p : R)*(r : R)*P*A*algebraMap ℚ R (binomialWeight (r+1) N)*X^N*hg

end WPResidueFrobenius
