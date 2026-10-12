import WPResidueFrobenius.Presentation

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

include hp7 hp19 in
theorem presentedPullback_add (g h : FClosed (Parameter.integralTenth p hp)) :
    presentedPullback p hp (g+h) = presentedPullback p hp g + presentedPullback p hp h := by
  obtain ⟨r, P, hr, hP, hg⟩ := integral_presentation_exists p hp g
  obtain ⟨s, Q, hs, hQ, hh⟩ := integral_presentation_exists p hp h
  let f := torusPolynomial (Parameter.integralTenth p hp)
  have hPr := numeratorFiltration_mul_f_pow (Parameter.integralTenth p hp) r s hP
  have hQr : Q*f^r ∈ numeratorFiltration ℤ_[p] (r+s) := by
    simpa only [Nat.add_comm s r] using
      numeratorFiltration_mul_f_pow (Parameter.integralTenth p hp) s r hQ
  have he : ((g+h : FClosed (Parameter.integralTenth p hp)) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) (r+s) (P*f^s+Q*f^r) := by
    simp only [Submodule.coe_add, map_add, hg, hh]
    rw [poleLinearMap_raise, show r+s = s+r by omega, poleLinearMap_raise]
  rw [presentedPullback_eq p hp hp7 hp19 (g+h) (r+s) (by omega) _
    ((numeratorFiltration ℤ_[p] (r+s)).add_mem hPr hQr) he,
    plainPullbackCoordinates_add p hp hp7 hp19 (r+s) (by omega) _ _ hPr hQr,
    plainPullbackCoordinates_raise_pow p hp hp7 hp19 r s hr P hP,
    presentedPullback_eq p hp hp7 hp19 g r hr P hP hg,
    presentedPullback_eq p hp hp7 hp19 h s hs Q hQ hh]
  congr 1
  exact (plainPullbackCoordinates_congr p hp (Nat.add_comm r s) rfl).trans
    (plainPullbackCoordinates_raise_pow p hp hp7 hp19 s r hs Q hQ)

include hp7 hp19 in
theorem presentedPullback_smul (c : ℤ_[p]) (g : FClosed (Parameter.integralTenth p hp)) :
    presentedPullback p hp (c • g) = IntegralTransport.padicCoefficientMap p c •
      presentedPullback p hp g := by
  obtain ⟨r, P, hr, hP, hg⟩ := integral_presentation_exists p hp g
  have he : ((c • g : FClosed (Parameter.integralTenth p hp)) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) r (c • P) := by
    simp only [Submodule.coe_smul, map_smul, hg]
  rw [presentedPullback_eq p hp hp7 hp19 _ r hr _
    ((numeratorFiltration ℤ_[p] r).smul_mem c hP) he,
    plainPullbackCoordinates_smul, presentedPullback_eq p hp hp7 hp19 g r hr P hP hg]

def presentedPullbackLinear : FClosed (Parameter.integralTenth p hp) →ₗ[ℤ_[p]]
    (Fin 11 → ℚ_[p]) where
  toFun := presentedPullback p hp
  map_add' := presentedPullback_add p hp hp7 hp19
  map_smul' := by
    intro c g
    exact presentedPullback_smul p hp hp7 hp19 c g

@[simp] theorem presentedPullbackLinear_apply (g : FClosed (Parameter.integralTenth p hp)) :
    presentedPullbackLinear p hp hp7 hp19 g = presentedPullback p hp g := rfl

include hp7 hp19 in
theorem plainPullbackCoordinates_sub (r : ℕ) (hr : 1 ≤ r)
    (P Q : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) (hQ : Q ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp r hr (P-Q) ((numeratorFiltration ℤ_[p] r).sub_mem hP hQ) =
      plainPullbackCoordinates p hp r hr P hP - plainPullbackCoordinates p hp r hr Q hQ := by
  calc
    _ = plainPullbackCoordinates p hp r hr (P+(-1:ℤ_[p]) • Q)
      ((numeratorFiltration ℤ_[p] r).add_mem hP
        ((numeratorFiltration ℤ_[p] r).smul_mem (-1) hQ)) :=
      plainPullbackCoordinates_congr p hp rfl (by simp [sub_eq_add_neg])
    _ = _ := by
      rw [plainPullbackCoordinates_add p hp hp7 hp19 r hr _ _ hP
        ((numeratorFiltration ℤ_[p] r).smul_mem (-1) hQ),
        plainPullbackCoordinates_smul p hp r hr (-1) Q hQ]
      simp [sub_eq_add_neg]

theorem logarithmicPoleNumerator_actual (r : ℕ)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5) :
    logarithmicPoleNumerator (Parameter.integralTenth p hp) i r P =
      derivativeNumerator p P i * torusPolynomial (Parameter.integralTenth p hp) -
        (r : ℤ_[p]) • derivativePoleNumerator p hp P i := by
  unfold logarithmicPoleNumerator derivativeNumerator derivativePoleNumerator
  rw [logarithmicDerivation_f]
  change _ = _ - (r : ℤ_[p]) •
    (P * (-algebraMap ℤ_[p] (WPResidueQuotient.LaurentPolynomial ℤ_[p])
      (Parameter.integralTenth p hp) * (laurentVertex i.castSucc-laurentVertex (Fin.last 5))))
  simp only [Algebra.smul_def]
  ring

include hp7 hp19 in
theorem plainPullbackCoordinates_derivative_zero (r : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (i : Fin 5)
    (hP : P ∈ numeratorFiltration ℤ_[p] r) :
    plainPullbackCoordinates p hp (r+1) (by omega)
      (logarithmicPoleNumerator (Parameter.integralTenth p hp) i r P)
      (logarithmicPoleNumerator_supported _ i r hP) = 0 := by
  have hDP := derivativeNumerator_supported p P i r hP
  have hPD := derivativePoleNumerator_supported p hp P i r hP
  have hDPf := numeratorFiltration_mul_f (Parameter.integralTenth p hp) r hDP
  have hsm := (numeratorFiltration ℤ_[p] (r+1)).smul_mem (r : ℤ_[p]) hPD
  calc
    _ = plainPullbackCoordinates p hp (r+1) (by omega)
        (derivativeNumerator p P i*torusPolynomial (Parameter.integralTenth p hp) -
          (r : ℤ_[p]) • derivativePoleNumerator p hp P i)
        ((numeratorFiltration ℤ_[p] (r+1)).sub_mem hDPf hsm) :=
      plainPullbackCoordinates_congr p hp rfl (logarithmicPoleNumerator_actual p hp r P i)
    _ = _ := by
      rw [plainPullbackCoordinates_sub p hp hp7 hp19 (r+1) (by omega) _ _ hDPf hsm,
        plainPullbackCoordinates_raise p hp hp7 hp19 r hr _ hDP,
        plainPullbackCoordinates_smul p hp (r+1) (by omega) (r : ℤ_[p]) _ hPD]
      simp only [map_natCast, plainPullbackCoordinates, Nat.add_sub_cancel]
      have hf : (r.factorial : ℚ_[p]) = (r : ℚ_[p])*((r-1).factorial : ℚ_[p]) := by
        have he := Nat.factorial_succ (r-1)
        rw [show r-1+1=r by omega] at he
        rw [he, Nat.cast_mul]
      have hrne : (r : ℚ_[p]) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
      have hc : (r : ℚ_[p])*(r.factorial : ℚ_[p])⁻¹ =
          ((r-1).factorial : ℚ_[p])⁻¹ := by
        rw [hf, mul_inv_rev]
        field_simp
      rw [smul_smul, hc, ← smul_sub,
        raw_coordinates_annihilate_presented_derivative p hp hp7 hp19 P i r hr hP,
        smul_zero]

set_option maxHeartbeats 800000 in
include hp7 hp19 in
theorem presentedPullback_derivative_zero (i : Fin 5)
    (g : FClosed (Parameter.integralTenth p hp)) :
    presentedPullback p hp (DClosed (Parameter.integralTenth p hp) i g) = 0 := by
  obtain ⟨r, P, hr, hP, hg⟩ := integral_presentation_exists p hp g
  obtain ⟨n, hn⟩ : ∃ n, r=n+1 := ⟨r-1, by omega⟩
  have he : ((DClosed (Parameter.integralTenth p hp) i g : FClosed _) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) (r+1)
        (logarithmicPoleNumerator (Parameter.integralTenth p hp) i r P) := by
    change actualD (Parameter.integralTenth p hp) i
      (g : ActualRing (Parameter.integralTenth p hp)) = _
    rw [hg]
    simpa only [hn, Nat.add_assoc] using
      actualD_poleLinearMap_succ (Parameter.integralTenth p hp) i n P
  rw [presentedPullback_eq p hp hp7 hp19 _ (r+1) (by omega) _
    (logarithmicPoleNumerator_supported _ i r hP) he]
  exact plainPullbackCoordinates_derivative_zero p hp hp7 hp19 r hr P i hP

theorem presentedPullbackLinear_kills_exact : exactSubmodule (Parameter.integralTenth p hp) ≤
    (presentedPullbackLinear p hp hp7 hp19).ker := by
  unfold exactSubmodule
  apply iSup_le
  intro i g hg
  obtain ⟨h, rfl⟩ := hg
  exact presentedPullback_derivative_zero p hp hp7 hp19 i h

def quotientPullback : ClosedResidueQuotient (Parameter.integralTenth p hp) →ₗ[ℤ_[p]]
    (Fin 11 → ℚ_[p]) :=
  (exactSubmodule (Parameter.integralTenth p hp)).liftQ (presentedPullbackLinear p hp hp7 hp19)
    (presentedPullbackLinear_kills_exact p hp hp7 hp19)

@[simp] theorem quotientPullback_mk (g : FClosed (Parameter.integralTenth p hp)) :
    quotientPullback p hp hp7 hp19 (Submodule.Quotient.mk g) = presentedPullback p hp g := rfl

end WPResidueFrobenius
