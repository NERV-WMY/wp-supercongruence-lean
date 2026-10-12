import WPResidueQuotient.ActualSplit
import WPResidueQuotient.FiniteSpecialization
import WPResidueQuotient.ParameterSpecialization

/-!
The proved actual eleven coordinates are specialized through the actual
finite-presentation kernel. Rational and p-adic constant families therefore
receive actual coordinate equivalences. Integral constant-family independence
is proved by its actual map into the p-adic field family; integral finite
generation supplies surjectivity without inverting factorials.
-/

namespace WPResidueQuotient.ActualSpecialization

noncomputable section

open scoped BigOperators
open Parameter

section Coefficients

variable {R S : Type*} [CommRing R] [CommRing S]

theorem closedMap_elevenElement (φ : R →+* S) (u : R) (i : Fin 11) :
    Specialization.closedMap φ u (Actual.elevenClosedElement u i) =
      Actual.elevenClosedElement (φ u) i := by
  refine Fin.addCases (m := 5) (n := 6) (fun j => ?_) (fun j => ?_) i
  · rw [Actual.elevenClosedElement_left, Actual.elevenClosedElement_left]
    apply Subtype.ext
    exact Specialization.actualMap_factorialPole φ u j.val
  · rw [Actual.elevenClosedElement_right, Actual.elevenClosedElement_right]
    apply Subtype.ext
    exact Specialization.actualMap_b φ u j

theorem closedMap_elevenSection (φ : R →+* S) (u : R) (a : Fin 11 → R) :
    Specialization.closedMap φ u (Actual.elevenSection u a) =
      Actual.elevenSection (φ u) (fun i => φ (a i)) := by
  rw [Actual.elevenSection_apply, Actual.elevenSection_apply]
  simp only [map_sum, map_smulₛₗ, closedMap_elevenElement]

theorem quotientMap_elevenSection (φ : R →+* S) (u : R) (a : Fin 11 → R) :
    Specialization.quotientMap φ u (Actual.elevenQuotientSection u a) =
      Actual.elevenQuotientSection (φ u) (fun i => φ (a i)) := by
  change Specialization.quotientMap φ u ((exactSubmodule u).mkQ (Actual.elevenSection u a)) =
    (exactSubmodule (φ u)).mkQ (Actual.elevenSection (φ u) (fun i => φ (a i)))
  rw [Specialization.quotientMap_mkQ, closedMap_elevenSection]

theorem transportedClosedMap_elevenElement (φ : R →+* S) (u : R) (v : S)
    (hu : φ u = v) (i : Fin 11) :
    IntegralTransport.closedMap φ u v hu (Actual.elevenClosedElement u i) =
      Actual.elevenClosedElement v i := by
  refine Fin.addCases (m := 5) (n := 6) (fun j => ?_) (fun j => ?_) i
  · rw [Actual.elevenClosedElement_left, Actual.elevenClosedElement_left]
    apply Subtype.ext
    exact IntegralTransport.actualMap_factorialPole φ u v hu j.val
  · rw [Actual.elevenClosedElement_right, Actual.elevenClosedElement_right]
    apply Subtype.ext
    exact IntegralTransport.actualMap_b φ u v hu j

theorem transportedClosedMap_elevenSection (φ : R →+* S) (u : R) (v : S)
    (hu : φ u = v) (a : Fin 11 → R) :
    IntegralTransport.closedMap φ u v hu (Actual.elevenSection u a) =
      Actual.elevenSection v (fun i => φ (a i)) := by
  rw [Actual.elevenSection_apply, Actual.elevenSection_apply]
  simp only [map_sum, map_smulₛₗ, transportedClosedMap_elevenElement]

theorem transportedQuotientMap_elevenSection (φ : R →+* S) (u : R) (v : S)
    (hu : φ u = v) (a : Fin 11 → R) :
    IntegralTransport.quotientMap φ u v hu (Actual.elevenQuotientSection u a) =
      Actual.elevenQuotientSection v (fun i => φ (a i)) := by
  change IntegralTransport.quotientMap φ u v hu
    (Submodule.Quotient.mk (Actual.elevenSection u a)) =
      Submodule.Quotient.mk (Actual.elevenSection v (fun i => φ (a i)))
  rw [IntegralTransport.quotientMap_mk, transportedClosedMap_elevenSection]

end Coefficients

section Field

variable (K : Type*) [Field K] [CharZero K]

/-- Constructed generic coordinates on the actual parameter family. -/
def parameterQuotientEquiv : (Fin 11 → ParameterRing K) ≃ₗ[ParameterRing K]
    ClosedResidueQuotient (Parameter.u : ParameterRing K) :=
  Actual.parameterQuotientEquiv K

@[simp] theorem parameterQuotientEquiv_apply (a : Fin 11 → ParameterRing K) :
    parameterQuotientEquiv K a = Actual.elevenQuotientSection Parameter.u a := rfl

def evaluatedQuotientEquiv (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    (Fin 11 → K) ≃ₗ[K]
      ClosedResidueQuotient (Specialization.fieldSpecialization K c hc
        (Parameter.u : ParameterRing K)) :=
  Specialization.fieldSpecializedSectionEquiv K c hc 11 (parameterQuotientEquiv K)
    (Actual.elevenQuotientSection _) (by
      intro a
      rw [parameterQuotientEquiv_apply]
      exact quotientMap_elevenSection (Specialization.fieldSpecialization K c hc) Parameter.u a)

@[simp] theorem evaluatedQuotientEquiv_apply (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) (a : Fin 11 → K) :
    evaluatedQuotientEquiv K c hc a = Actual.elevenQuotientSection _ a := rfl

/-- Independence and spanning in the literal constant family follow through the proved fiber. -/
def constantQuotientEquiv (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    (Fin 11 → K) ≃ₗ[K] ClosedResidueQuotient c := by
  refine LinearEquiv.ofBijective (Actual.elevenQuotientSection c) ?_
  have hb : Function.Bijective
      (Actual.elevenQuotientSection (Specialization.fieldSpecialization K c hc
        (Parameter.u : ParameterRing K))) :=
    (evaluatedQuotientEquiv K c hc).bijective
  exact (Specialization.fieldSpecialization_u K c hc) ▸ hb

@[simp] theorem constantQuotientEquiv_apply (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) (a : Fin 11 → K) :
      constantQuotientEquiv K c hc a = Actual.elevenQuotientSection c a := rfl

def tenthQuotientEquiv : (Fin 11 → K) ≃ₗ[K] ClosedResidueQuotient (1 / 10 : K) :=
  constantQuotientEquiv K (1 / 10) (Specialization.tenth_denominator_nonzero K)

@[simp] theorem tenthQuotientEquiv_apply (a : Fin 11 → K) :
    tenthQuotientEquiv K a = Actual.elevenQuotientSection (1 / 10 : K) a :=
  constantQuotientEquiv_apply K (1 / 10) (Specialization.tenth_denominator_nonzero K) a

theorem tenthSection_injective : Function.Injective (Actual.elevenQuotientSection (1 / 10 : K)) := by
  intro a b h
  apply (tenthQuotientEquiv K).injective
  simpa only [tenthQuotientEquiv_apply] using h

end Field

def rationalConstantQuotientEquiv :
    (Fin 11 → ℚ) ≃ₗ[ℚ] ClosedResidueQuotient (1 / 10 : ℚ) := tenthQuotientEquiv ℚ

section Padic

variable (p : ℕ) [Fact p.Prime]

def padicConstantQuotientEquiv :
    (Fin 11 → ℚ_[p]) ≃ₗ[ℚ_[p]] ClosedResidueQuotient (1 / 10 : ℚ_[p]) :=
  tenthQuotientEquiv ℚ_[p]

def integralConstantQuotientMap (hp : 7 ≤ p) :
    ClosedResidueQuotient (integralTenth p hp)
      →ₛₗ[IntegralTransport.padicCoefficientMap p] ClosedResidueQuotient (1 / 10 : ℚ_[p]) :=
  IntegralTransport.quotientMap (IntegralTransport.padicCoefficientMap p)
    (integralTenth p hp) (1 / 10) (ParameterSpecialization.integralTenth_in_field p hp)

theorem integralConstantQuotientMap_section (hp : 7 ≤ p) (a : Fin 11 → ℤ_[p]) :
    integralConstantQuotientMap p hp (Actual.elevenQuotientSection (integralTenth p hp) a) =
      Actual.elevenQuotientSection (1 / 10 : ℚ_[p])
        (fun i => IntegralTransport.padicCoefficientMap p (a i)) :=
  transportedQuotientMap_elevenSection _ _ _ _ a

/-- Integral independence is proved in the literal constant family through its actual field map. -/
theorem integralConstantSection_injective (hp : 7 ≤ p) :
    Function.Injective (Actual.elevenQuotientSection (integralTenth p hp)) := by
  intro a b hab
  have h := congrArg (integralConstantQuotientMap p hp) hab
  rw [integralConstantQuotientMap_section, integralConstantQuotientMap_section] at h
  have he := tenthSection_injective ℚ_[p] h
  ext i
  exact IntegralTransport.padicCoefficientMap_injective p (congrFun he i)

def integralConstantInverseSix (hp : 7 ≤ p) : ℤ_[p] :=
  ↑((padic_six_unit p hp).mul (integralTenth_unit p hp)).unit⁻¹

theorem integralConstantInverseSix_identity (hp : 7 ≤ p) :
    integralConstantInverseSix p hp * (6 * integralTenth p hp) = 1 :=
  ((padic_six_unit p hp).mul (integralTenth_unit p hp)).val_inv_mul

def integralConstantInverseDiscriminant (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) : ℤ_[p] :=
  ↑(specialized_discriminant_unit p hp hp7 hp19).unit⁻¹

theorem integralConstantInverseDiscriminant_identity
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    integralConstantInverseDiscriminant p hp hp7 hp19 *
      (1 - (6 * integralTenth p hp) ^ 6) = 1 :=
  (specialized_discriminant_unit p hp hp7 hp19).val_inv_mul

/-- Surjectivity uses the integral numerator reduction and exact primitives, with no factorial inverse. -/
theorem integralConstantSection_surjective (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    Function.Surjective (Actual.elevenQuotientSection (integralTenth p hp)) :=
  Actual.elevenQuotientSection_surjective (integralTenth p hp)
    (integralConstantInverseSix p hp) (integralConstantInverseDiscriminant p hp hp7 hp19)
    (integralConstantInverseSix_identity p hp)
    (integralConstantInverseDiscriminant_identity p hp hp7 hp19)

/-- The actual integral constant family has the eleven displayed coordinates at every good prime. -/
def integralConstantQuotientEquiv (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    (Fin 11 → ℤ_[p]) ≃ₗ[ℤ_[p]] ClosedResidueQuotient (integralTenth p hp) :=
  LinearEquiv.ofBijective (Actual.elevenQuotientSection (integralTenth p hp))
    ⟨integralConstantSection_injective p hp, integralConstantSection_surjective p hp hp7 hp19⟩

@[simp] theorem integralConstantQuotientEquiv_apply
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) (a : Fin 11 → ℤ_[p]) :
    integralConstantQuotientEquiv p hp hp7 hp19 a =
      Actual.elevenQuotientSection (integralTenth p hp) a := rfl

theorem integralConstantQuotientMap_injective
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    Function.Injective (integralConstantQuotientMap p hp) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := (integralConstantQuotientEquiv p hp hp7 hp19).surjective a
  obtain ⟨b', rfl⟩ := (integralConstantQuotientEquiv p hp hp7 hp19).surjective b
  rw [integralConstantQuotientEquiv_apply, integralConstantQuotientEquiv_apply] at hab ⊢
  rw [integralConstantQuotientMap_section, integralConstantQuotientMap_section] at hab
  have hcoeff := tenthSection_injective ℚ_[p] hab
  have he : a' = b' := funext (fun i =>
    IntegralTransport.padicCoefficientMap_injective p (congrFun hcoeff i))
  rw [he]

end Padic

end

end WPResidueQuotient.ActualSpecialization
