import WPGamma
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section
set_option maxHeartbeats 1000000

namespace WPGammaU

open Polynomial WPPsi

variable (p : ℕ) [Fact p.Prime]

def parameterPolynomial : Polynomial (ZMod p) := (C 6 * X)^6
def polynomialSubstitution : Polynomial (ZMod p) →+* Polynomial (ZMod p) :=
  Polynomial.eval₂RingHom C (parameterPolynomial p)

theorem polynomialSubstitution_apply (P : Polynomial (ZMod p)) :
    polynomialSubstitution p P=P.comp (parameterPolynomial p) := rfl

theorem parameterPolynomial_degree (hp7 : 7 ≤ p) :
    (parameterPolynomial p).natDegree=6 := by
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro h
    apply (WPDual.six_field_unit p hp7).ne_zero
    simpa only [map_ofNat, map_zero] using congrArg (algebraMap (ZMod p) (K p)) h
  simp [parameterPolynomial, natDegree_pow, natDegree_C_mul h6]

theorem polynomialSubstitution_ne_zero (hp7 : 7 ≤ p)
    (P : Polynomial (ZMod p)) (hP : P ≠ 0) : polynomialSubstitution p P ≠ 0 := by
  rw [polynomialSubstitution_apply]
  intro h
  rcases comp_eq_zero_iff.mp h with h | h
  · exact hP h
  · have hn := congrArg natDegree h.2
    rw [parameterPolynomial_degree p hp7, natDegree_C] at hn
    omega

theorem substitution_nzd (hp7 : 7 ≤ p)
    (s : nonZeroDivisors (Polynomial (ZMod p))) :
    IsUnit (polyMap p (polynomialSubstitution p s)) := by
  apply isUnit_iff_ne_zero.mpr
  simpa only [polyMap, map_zero] using
    (IsFractionRing.injective (Polynomial (ZMod p)) (K p)).ne
      (polynomialSubstitution_ne_zero p hp7 s
        (mem_nonZeroDivisors_iff_ne_zero.mp s.property))

def substitute (hp7 : 7 ≤ p) : K p →+* K p :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial (ZMod p)))
    (S := K p) (g := (polyMap p).comp (polynomialSubstitution p))
    (substitution_nzd p hp7)

theorem substitute_poly (hp7 : 7 ≤ p) (P : Polynomial (ZMod p)) :
    substitute p hp7 (polyMap p P)=polyMap p (polynomialSubstitution p P) :=
  IsLocalization.lift_eq (substitution_nzd p hp7) P

theorem substitute_injective (hp7 : 7 ≤ p) : Function.Injective (substitute p hp7) :=
  (substitute p hp7).injective

theorem substitute_base (hp7 : 7 ≤ p) (a : ZMod p) :
    substitute p hp7 (algebraMap (ZMod p) (K p) a)=algebraMap (ZMod p) (K p) a := by
  have he : algebraMap (ZMod p) (K p) a=polyMap p (C a) := by
    simp [polyMap, IsScalarTower.algebraMap_apply (ZMod p) (Polynomial (ZMod p)) (K p)]
  rw [he, substitute_poly]
  simp [polynomialSubstitution]

theorem substitute_X (hp7 : 7 ≤ p) :
    substitute p hp7 (polyMap p X)=(6*polyMap p X)^6 := by
  rw [substitute_poly]
  simp [polynomialSubstitution, parameterPolynomial, map_pow, map_mul, map_ofNat]

theorem substitute_delta (hp7 : 7 ≤ p) :
    substitute p hp7 (oneMinus p)=1-(6*polyMap p X)^6 := by
  rw [oneMinus_literal, map_sub, map_one, substitute_X]

theorem parameter_theta : WPRho.theta (parameterPolynomial p)=6*parameterPolynomial p := by
  simp [WPRho.theta, parameterPolynomial, derivative_pow, map_ofNat]
  ring

theorem theta_substitution_polynomial (P : Polynomial (ZMod p)) :
    WPRho.theta (polynomialSubstitution p P)=6*polynomialSubstitution p (WPRho.theta P) := by
  rw [polynomialSubstitution_apply, polynomialSubstitution_apply]
  change X*(P.comp (parameterPolynomial p)).derivative=
    6*((X*P.derivative).comp (parameterPolynomial p))
  rw [derivative_comp, mul_comp, X_comp]
  calc
    X*((parameterPolynomial p).derivative*P.derivative.comp (parameterPolynomial p)) =
        (P.derivative.comp (parameterPolynomial p))*WPRho.theta (parameterPolynomial p) := by
      rw [WPRho.theta]
      ring
    _ = _ := by rw [parameter_theta]; ring

theorem theta_substitute_poly (hp7 : 7 ≤ p) (P : Polynomial (ZMod p)) :
    theta p (substitute p hp7 (polyMap p P))=
      6*substitute p hp7 (theta p (polyMap p P)) := by
  rw [substitute_poly, theta_poly, theta_substitution_polynomial,
    theta_poly, substitute_poly, map_mul, map_ofNat]

theorem theta_substitute (hp7 : 7 ≤ p) (a : K p) :
    theta p (substitute p hp7 a)=6*substitute p hp7 (theta p a) := by
  obtain ⟨P,Q,_,rfl⟩ := IsFractionRing.div_surjective (Polynomial (ZMod p)) a
  change theta p (substitute p hp7 (polyMap p P/polyMap p Q))=
    6*substitute p hp7 (theta p (polyMap p P/polyMap p Q))
  rw [map_div₀, (theta p).leibniz_div, (theta p).leibniz_div,
    theta_substitute_poly, theta_substitute_poly]
  simp only [smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀]
  ring

end WPGammaU
