import WPResidueFrobenius.Linearity

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem plainPullbackCoordinates_congr {r s : ℕ} {hr : 1 ≤ r} {hs : 1 ≤ s}
    {P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p]}
    {hP : P ∈ numeratorFiltration ℤ_[p] r} {hQ : Q ∈ numeratorFiltration ℤ_[p] s}
    (hrs : r = s) (hPQ : P = Q) :
    plainPullbackCoordinates p hp r hr P hP = plainPullbackCoordinates p hp s hs Q hQ := by
  subst s
  subst Q
  rfl

include hp7 hp19 in
theorem plainPullbackCoordinates_raise_pow (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp (r+k) (by omega)
      (P*torusPolynomial (Parameter.integralTenth p hp)^k)
      (numeratorFiltration_mul_f_pow _ r k hP) = plainPullbackCoordinates p hp r hr P hP := by
  induction k with
  | zero =>
      apply plainPullbackCoordinates_congr p hp <;> simp only [Nat.add_zero, pow_zero, mul_one]
  | succ k ih =>
      have hs := plainPullbackCoordinates_raise p hp hp7 hp19 (r+k) (by omega)
        (P*torusPolynomial (Parameter.integralTenth p hp)^k)
        (numeratorFiltration_mul_f_pow _ r k hP)
      calc
        _ = plainPullbackCoordinates p hp (r+k+1) (by omega)
            ((P*torusPolynomial (Parameter.integralTenth p hp)^k)*
              torusPolynomial (Parameter.integralTenth p hp))
            (numeratorFiltration_mul_f _ (r+k) (numeratorFiltration_mul_f_pow _ r k hP)) := by
          apply plainPullbackCoordinates_congr p hp <;>
            simp only [Nat.add_assoc, pow_succ, mul_assoc]
        _ = _ := hs.trans ih

include hp7 hp19 in
theorem plainPullbackCoordinates_presentation (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (hQ : Q ∈ numeratorFiltration ℤ_[p] s)
    (he : poleLinearMap (Parameter.integralTenth p hp) r P =
      poleLinearMap (Parameter.integralTenth p hp) s Q) :
    plainPullbackCoordinates p hp r hr P hP = plainPullbackCoordinates p hp s hs Q hQ := by
  have hc := (poleLinearMap_eq_iff_cross_multiply _ r s P Q).mp he
  rw [← plainPullbackCoordinates_raise_pow p hp hp7 hp19 r s hr P hP,
    ← plainPullbackCoordinates_raise_pow p hp hp7 hp19 s r hs Q hQ]
  exact plainPullbackCoordinates_congr p hp (Nat.add_comm r s) hc

include hp7 hp19 in
theorem plainPullbackCoordinates_add (r : ℕ) (hr : 1 ≤ r)
    (P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (hQ : Q ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp r hr (P+Q) ((numeratorFiltration ℤ_[p] r).add_mem hP hQ) =
      plainPullbackCoordinates p hp r hr P hP + plainPullbackCoordinates p hp r hr Q hQ := by
  rw [plainPullbackCoordinates, rawPullbackCoordinates_add p hp hp7 hp19, smul_add]
  rfl

theorem plainPullbackCoordinates_smul (r : ℕ) (hr : 1 ≤ r)
    (c : ℤ_[p]) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp r hr (c • P) ((numeratorFiltration ℤ_[p] r).smul_mem c hP) =
      IntegralTransport.padicCoefficientMap p c • plainPullbackCoordinates p hp r hr P hP := by
  rw [plainPullbackCoordinates, rawPullbackCoordinates_smul, smul_comm]
  rfl

theorem integral_presentation_exists (g : FClosed (Parameter.integralTenth p hp)) :
    ∃ r : ℕ, ∃ P : WPResidueQuotient.LaurentPolynomial ℤ_[p], 1 ≤ r ∧
      P ∈ numeratorFiltration ℤ_[p] r ∧ (g : ActualRing (Parameter.integralTenth p hp)) =
        poleLinearMap (Parameter.integralTenth p hp) r P := by
  obtain ⟨r, P, hr, _, hP, hg⟩ := FClosed_common_pole _ g.property
  exact ⟨r, P, hr, by simpa only [Nat.sub_zero] using hP, hg⟩

def presentationPole (g : FClosed (Parameter.integralTenth p hp)) : ℕ :=
  Classical.choose (integral_presentation_exists p hp g)

def presentationNumerator (g : FClosed (Parameter.integralTenth p hp)) :
    WPResidueQuotient.LaurentPolynomial ℤ_[p] :=
  Classical.choose (Classical.choose_spec (integral_presentation_exists p hp g))

theorem presentation_spec (g : FClosed (Parameter.integralTenth p hp)) :
    1 ≤ presentationPole p hp g ∧
      presentationNumerator p hp g ∈ numeratorFiltration ℤ_[p] (presentationPole p hp g) ∧
        (g : ActualRing (Parameter.integralTenth p hp)) =
          poleLinearMap (Parameter.integralTenth p hp) (presentationPole p hp g)
            (presentationNumerator p hp g) :=
  Classical.choose_spec (Classical.choose_spec (integral_presentation_exists p hp g))

def presentedPullback (g : FClosed (Parameter.integralTenth p hp)) : Fin 11 → ℚ_[p] :=
  plainPullbackCoordinates p hp (presentationPole p hp g) (presentation_spec p hp g).1
    (presentationNumerator p hp g) (presentation_spec p hp g).2.1

include hp7 hp19 in
theorem presentedPullback_eq (g : FClosed (Parameter.integralTenth p hp))
    (r : ℕ) (hr : 1 ≤ r) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r)
    (he : (g : ActualRing (Parameter.integralTenth p hp)) = poleLinearMap _ r P) :
    presentedPullback p hp g = plainPullbackCoordinates p hp r hr P hP :=
  plainPullbackCoordinates_presentation p hp hp7 hp19 _ r (presentation_spec p hp g).1 hr _ P
    (presentation_spec p hp g).2.1 hP ((presentation_spec p hp g).2.2.symm.trans he)

end WPResidueFrobenius
