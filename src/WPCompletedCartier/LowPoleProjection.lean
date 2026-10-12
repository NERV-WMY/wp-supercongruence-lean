import WPCompletedCartier.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace WPCompletedCartier.LowPoleProjection

noncomputable section
open scoped BigOperators
open Polynomial WPResidueQuotient WPCartierFinite
open WPReview.ResidueNumeratorOperators

abbrev FamilyCoeff := Parameter.ParameterRing ℚ
abbrev FamilyResidue := ClosedResidueQuotient (ActualConnection.parameter ℚ)
def theta : Module.End ℚ FamilyResidue := ActualConnection.quotientTheta ℚ

theorem summedDegree (a : SixExponent) : (∑ i, a i) = exponentDegree a := rfl

theorem admissibleBound (a : SixExponent) (k : ℕ) (ha : exponentDegree a ≤ k) :
    (∑ i, a i) ≤ k + 1 := by
  rw [summedDegree]
  omega

def vertexPolynomial (a : SixExponent) : ℚ[X] :=
  ∏ i, ∏ j ∈ Finset.range (a i), (X - C (6 * (j : ℚ)))

def polePolynomial (n : ℕ) : ℚ[X] :=
  ∏ t ∈ Finset.range n, (X + C ((t : ℚ) + 1))

theorem vertexPolynomial_zero : vertexPolynomial 0 = 1 := by
  simp [vertexPolynomial]

theorem vertexPolynomial_add (a : SixExponent) (i : Fin 6) :
    vertexPolynomial (addNumeratorExponent a i) =
      (X - C (6 * (a i : ℚ))) * vertexPolynomial a := by
  have h (j : Fin 6) :
      (∏ t ∈ Finset.range (addNumeratorExponent a i j), (X - C (6 * (t : ℚ)))) =
        (if j = i then X - C (6 * (a i : ℚ)) else 1) *
          ∏ t ∈ Finset.range (a j), (X - C (6 * (t : ℚ))) := by
    by_cases hj : j = i
    · subst j
      simp only [addNumeratorExponent, Pi.add_apply, Pi.single_apply, if_true]
      rw [Finset.prod_range_succ]
      exact mul_comm _ _
    · simp [addNumeratorExponent, hj]
  simp only [vertexPolynomial, h, Finset.prod_mul_distrib]
  simp

theorem scalar_action (c : ℚ) (x : FamilyResidue) :
    (algebraMap ℚ FamilyCoeff c) • x = c • x :=
  IsScalarTower.algebraMap_smul FamilyCoeff c x

set_option maxHeartbeats 1600000 in
theorem classOperators_polynomial (x : FamilyResidue) (w : List (Fin 6)) :
    classOperators ℚ x w = (aeval theta (vertexPolynomial (wordExponent w))) x := by
  induction w with
  | nil =>
      change x = (aeval theta (vertexPolynomial 0)) x
      rw [vertexPolynomial_zero, map_one, Module.End.one_apply]
  | cons i w ih =>
      change theta (classOperators ℚ x w) -
        (6 * (wordExponent w i : FamilyCoeff)) • classOperators ℚ x w = _
      rw [ih, wordExponent, vertexPolynomial_add,
        map_mul, map_sub, aeval_X, aeval_C, Module.End.mul_apply,
        LinearMap.sub_apply]
      congr 1
      change (6 * (wordExponent w i : FamilyCoeff)) •
          (((aeval theta (vertexPolynomial (wordExponent w))) x) : FamilyResidue) =
        (6 * (wordExponent w i : ℚ)) •
          (((aeval theta (vertexPolynomial (wordExponent w))) x) : FamilyResidue)
      simpa only [map_mul, map_ofNat, map_natCast] using
        scalar_action (6 * (wordExponent w i : ℚ))
          ((aeval theta (vertexPolynomial (wordExponent w))) x)

set_option maxHeartbeats 1600000 in
theorem poleOperators_polynomial (n : ℕ) :
    poleOperators ℚ n = (aeval theta (polePolynomial n)) (ActualConnection.qGamma ℚ 0) := by
  induction n with
  | zero => simp [poleOperators, polePolynomial]
  | succ n ih =>
      have hp : polePolynomial (n + 1) =
          (X + C ((n : ℚ) + 1)) * polePolynomial n := by
        simp only [polePolynomial, Finset.prod_range_succ]
        exact mul_comm _ _
      change theta (poleOperators ℚ n) + (n + 1 : FamilyCoeff) • poleOperators ℚ n = _
      rw [ih, hp,
        map_mul, map_add, aeval_X, aeval_C, Module.End.mul_apply,
        LinearMap.add_apply]
      congr 1
      change (n + 1 : FamilyCoeff) •
          (((aeval theta (polePolynomial n)) (ActualConnection.qGamma ℚ 0)) : FamilyResidue) =
        ((n : ℚ) + 1) •
          (((aeval theta (polePolynomial n)) (ActualConnection.qGamma ℚ 0)) : FamilyResidue)
      simpa only [map_add, map_natCast, map_one] using
        scalar_action ((n : ℚ) + 1)
          ((aeval theta (polePolynomial n)) (ActualConnection.qGamma ℚ 0))

set_option maxHeartbeats 1600000 in
/-- This equality uses the genuine family numerator raising theorem. -/
theorem actual_scaled_numerator_polynomial (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) :
    scaledNumerator ℚ a k (admissibleBound a k ha) =
      (aeval theta (lowPolePolynomial a k)) (ActualConnection.qGamma ℚ 0) := by
  have hpole : k - exponentDegree a + (canonicalWord a).length = k := by
    rw [canonicalWord_length, summedDegree, Nat.sub_add_cancel ha]
  have hword : Eq (α := FamilyResidue)
      (scaledNumerator ℚ (wordExponent (canonicalWord a))
        (k - exponentDegree a + (canonicalWord a).length)
        (by rw [wordExponent_sum]; omega))
      (classOperators ℚ (poleOperators ℚ (k - exponentDegree a)) (canonicalWord a)) :=
    @WPReview.ResidueNumeratorOperators.word_numerator_from_first_pole ℚ
      (inferInstance : CommRing ℚ) (k - exponentDegree a) (canonicalWord a)
  have h : Eq (α := FamilyResidue)
      (scaledNumerator ℚ a k (admissibleBound a k ha))
      (classOperators ℚ (poleOperators ℚ (k - exponentDegree a)) (canonicalWord a)) := by
    simpa only [canonicalWord_exponent, hpole] using hword
  let E : ℚ[X] →ₐ[ℚ] Module.End ℚ FamilyResidue := aeval theta
  let q : FamilyResidue := ActualConnection.qGamma ℚ 0
  have hclass : Eq (α := FamilyResidue)
      (classOperators ℚ (poleOperators ℚ (k - exponentDegree a)) (canonicalWord a))
      (E (vertexPolynomial (wordExponent (canonicalWord a)))
        (poleOperators ℚ (k - exponentDegree a))) :=
    classOperators_polynomial (poleOperators ℚ (k - exponentDegree a)) (canonicalWord a)
  have hvertex : Eq (α := FamilyResidue)
      (E (vertexPolynomial (wordExponent (canonicalWord a)))
        (poleOperators ℚ (k - exponentDegree a)))
      (E (vertexPolynomial a) (poleOperators ℚ (k - exponentDegree a))) :=
    congrArg (fun P : ℚ[X] => E P (poleOperators ℚ (k - exponentDegree a)))
      (congrArg vertexPolynomial (canonicalWord_exponent a))
  have hpoles : Eq (α := FamilyResidue)
      (poleOperators ℚ (k - exponentDegree a))
      (E (polePolynomial (k - exponentDegree a)) q) :=
    poleOperators_polynomial (k - exponentDegree a)
  have hsubstitute : Eq (α := FamilyResidue)
      (E (vertexPolynomial a) (poleOperators ℚ (k - exponentDegree a)))
      (E (vertexPolynomial a) (E (polePolynomial (k - exponentDegree a)) q)) :=
    congrArg (fun x : FamilyResidue => E (vertexPolynomial a) x) hpoles
  have hproduct : Eq (α := Module.End ℚ FamilyResidue)
      (E (vertexPolynomial a) * E (polePolynomial (k - exponentDegree a)))
      (E (vertexPolynomial a * polePolynomial (k - exponentDegree a))) :=
    (E.map_mul (vertexPolynomial a) (polePolynomial (k - exponentDegree a))).symm
  have hproductValue : Eq (α := FamilyResidue)
      (E (vertexPolynomial a) (E (polePolynomial (k - exponentDegree a)) q))
      (E (vertexPolynomial a * polePolynomial (k - exponentDegree a)) q) :=
    congrArg (fun L : Module.End ℚ FamilyResidue => L q) hproduct
  have hpolynomial : vertexPolynomial a * polePolynomial (k - exponentDegree a) =
      lowPolePolynomial a k := (lowPolePolynomial_formula a k).symm
  have hfinal : Eq (α := FamilyResidue)
      (E (vertexPolynomial a * polePolynomial (k - exponentDegree a)) q)
      (E (lowPolePolynomial a k) q) :=
    congrArg (fun P : ℚ[X] => E P q) hpolynomial
  exact h.trans (hclass.trans (hvertex.trans (hsubstitute.trans (hproductValue.trans hfinal))))

def familyGammaSection (v : LowVector) : FamilyResidue :=
  WPReview.ResidueConnection.gammaSection ℚ (fun i => algebraMap ℚ FamilyCoeff (v i))

theorem familyGammaSection_formula (v : LowVector) :
    familyGammaSection v = ∑ i : Fin 5, v i • ActualConnection.qGamma ℚ i.val := by
  rw [familyGammaSection, WPReview.ResidueConnection.gammaSection_apply]
  simp only [scalar_action]

/-- These powers are formed before specialization; no Euler map on the fiber is used. -/
theorem family_connection_powers (d : ℕ) (hd : d ≤ 4) :
    (theta ^ d) (ActualConnection.qGamma ℚ 0) = familyGammaSection (gammaB d) := by
  interval_cases d <;>
    norm_num [familyGammaSection_formula, gammaB, gammaBInteger, Fin.sum_univ_succ,
      theta, pow_succ, Module.End.mul_apply, ActualConnection.quotientTheta_Gamma,
      map_add, map_sub, map_smul] <;> module

theorem family_polynomial_coordinates (P : ℚ[X]) (k : ℕ)
    (hP : P.natDegree ≤ k) (hk : k ≤ 4) :
    (aeval theta P) (ActualConnection.qGamma ℚ 0) =
      familyGammaSection (fun i =>
        ∑ d ∈ Finset.range (k + 1), P.coeff d * gammaB d i) := by
  rw [aeval_endomorphism, Polynomial.sum_over_range' _ _ (k + 1) (by omega)]
  · simp only [familyGammaSection_formula]
    have hpowers : ∀ d ∈ Finset.range (k + 1),
        (theta ^ d) (ActualConnection.qGamma ℚ 0) =
          ∑ i : Fin 5, gammaB d i • ActualConnection.qGamma ℚ i.val := by
      intro d hd
      rw [family_connection_powers d (by have := Finset.mem_range.mp hd; omega),
        familyGammaSection_formula]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hpowers d hd, Finset.smul_sum]
    simp only [smul_smul]
  · simp

abbrev NumericalResidue := ClosedResidueQuotient (1 / 10 : ℚ)

def numericalNumerator (a : SixExponent) (k : ℕ) (ha : exponentDegree a ≤ k + 1) :
    NumericalResidue :=
  Submodule.Quotient.mk
    (⟨numeratorGenerator (1 / 10 : ℚ) a k,
      numeratorGenerator_mem_closed _ a k
        (by simpa only [summedDegree] using ha)⟩ : FClosed (1 / 10 : ℚ))

def appendInterior : LowVector →ₗ[ℚ] (Fin 11 → ℚ) where
  toFun v := Fin.append v (fun _ : Fin 6 => 0)
  map_add' v w := by ext i; exact Fin.addCases (by simp) (by simp) i
  map_smul' c v := by ext i; exact Fin.addCases (by simp) (by simp) i

def numericalGammaSection : LowVector →ₗ[ℚ] NumericalResidue :=
  (Actual.elevenQuotientSection (1 / 10 : ℚ)).comp appendInterior

def specialize : FamilyResidue →ₛₗ[Parameter.rationalSpecialization] NumericalResidue :=
  IntegralTransport.quotientMap Parameter.rationalSpecialization
    (ActualConnection.parameter ℚ) (1 / 10) Parameter.rationalSpecialization_u

theorem specialize_numerator (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k + 1) :
    specialize (qNumerator ℚ a k (by simpa only [summedDegree] using ha)) =
      numericalNumerator a k ha := by
  change IntegralTransport.quotientMap Parameter.rationalSpecialization
    (ActualConnection.parameter ℚ) (1 / 10) Parameter.rationalSpecialization_u
      (Submodule.Quotient.mk (numeratorClosed ℚ a k _)) = _
  rw [IntegralTransport.quotientMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact IntegralTransport.actualMap_numeratorGenerator _ _ _ _ a k

theorem numericalGammaSection_formula (v : LowVector) :
    numericalGammaSection v =
      ∑ i : Fin 5, v i •
        MellinFactors.gammaQuotientFamily (1 / 10 : ℚ) i := by
  change Actual.elevenQuotientSection _ (Fin.append v (fun _ : Fin 6 => 0)) = _
  rw [Actual.elevenQuotientSection_apply, Fin.sum_univ_add (a := 5) (b := 6)]
  simp only [Fin.append_left, Fin.append_right, Actual.elevenQuotientFamily_left,
    zero_smul, Finset.sum_const_zero, add_zero]

theorem specialize_familyGammaSection (v : LowVector) :
    specialize (familyGammaSection v) = numericalGammaSection v := by
  rw [familyGammaSection_formula, numericalGammaSection_formula]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← scalar_action (v i) (ActualConnection.qGamma ℚ i.val)]
  rw [map_smulₛₗ, Parameter.rationalSpecialization_scalar]
  congr 1
  rw [specialize, ActualConnection.qGamma, IntegralTransport.quotientMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simpa only [IntegralTransport.closedMap_coe, ActualConnection.gammaClosed,
    MellinFactors.gammaQuotientFamily,
    Actual.gammaClosedElement, Gamma_succ] using
    IntegralTransport.actualMap_Gamma Parameter.rationalSpecialization
      (ActualConnection.parameter ℚ) (1 / 10) Parameter.rationalSpecialization_u (i.val + 1)

theorem actual_numerical_scaled_coordinates (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) (hk : k ≤ 4) :
    ((3 : ℚ) / 5) ^ exponentDegree a • numericalNumerator a k (by omega) =
      numericalGammaSection (fun i =>
        ∑ d ∈ Finset.range (k + 1), (lowPolePolynomial a k).coeff d * gammaB d i) := by
  have h := actual_scaled_numerator_polynomial a k ha
  rw [family_polynomial_coordinates _ k (lowPolePolynomial_degree a k ha) hk] at h
  have hs := congrArg specialize h
  rw [scaledNumerator, map_smulₛₗ, specialize_numerator,
    specialize_familyGammaSection] at hs
  norm_num only [map_pow, map_mul, map_ofNat, Parameter.rationalSpecialization_u,
    ActualConnection.parameter, summedDegree] at hs
  exact hs

def rawNumeratorClass (a : SixExponent) (k : ℕ) (ha : exponentDegree a ≤ k) :
    NumericalResidue :=
  (k.factorial : ℚ)⁻¹ • numericalNumerator a k (by omega)

/-- The printed vector represents the literal unnormalized fraction in the actual quotient. -/
theorem actual_lowPoleVector (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) (hk : k ≤ 4) :
    numericalGammaSection (lowPoleVector a k) = rawNumeratorClass a k ha := by
  have h := actual_numerical_scaled_coordinates a k ha hk
  have hv : lowPoleVector a k =
      (((5 : ℚ) / 3) ^ exponentDegree a / (k.factorial : ℚ)) •
        (fun i => ∑ d ∈ Finset.range (k + 1),
          (lowPolePolynomial a k).coeff d * gammaB d i) := rfl
  rw [hv, map_smul, ← h, smul_smul, rawNumeratorClass]
  congr 1
  have hp : ((5 : ℚ) / 3) ^ exponentDegree a *
      ((3 : ℚ) / 5) ^ exponentDegree a = 1 := by
    rw [← mul_pow]
    norm_num
  rw [div_eq_mul_inv]
  calc
    _ = (((5 : ℚ) / 3) ^ exponentDegree a *
        ((3 : ℚ) / 5) ^ exponentDegree a) * (k.factorial : ℚ)⁻¹ := by ring
    _ = _ := by rw [hp, one_mul]

def numericalGammaProjection (q : NumericalResidue) : LowVector :=
  fun i => ActualSpecialization.rationalConstantQuotientEquiv.symm q (Fin.castAdd 6 i)

theorem numericalGammaProjection_section (v : LowVector) :
    numericalGammaProjection (numericalGammaSection v) = v := by
  have hs : numericalGammaSection v = ActualSpecialization.rationalConstantQuotientEquiv
      (Fin.append v (fun _ : Fin 6 => 0)) := rfl
  rw [hs]
  ext i
  simp [numericalGammaProjection]

/-- Actual numerical Gamma coordinates, obtained by the proved finite-specialization equivalence. -/
theorem actual_lowPole_projection (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) (hk : k ≤ 4) :
    numericalGammaProjection (rawNumeratorClass a k ha) = lowPoleVector a k := by
  rw [← actual_lowPoleVector a k ha hk, numericalGammaProjection_section]

def rawNumeratorClosed (a : SixExponent) (k : ℕ) (ha : exponentDegree a ≤ k) :
    FClosed (1 / 10 : ℚ) :=
  (k.factorial : ℚ)⁻¹ •
    (⟨numeratorGenerator (1 / 10 : ℚ) a k,
      numeratorGenerator_mem_closed _ a k (admissibleBound a k ha)⟩ :
        FClosed (1 / 10 : ℚ))

/-- The representative is the literal rational function, with the factorial fully cancelled. -/
theorem rawNumeratorClosed_value (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) :
    (rawNumeratorClosed a k ha : ActualRing (1 / 10 : ℚ)) =
      actualMonomial (1 / 10 : ℚ) (fun i => (a i : ℤ)) *
        inverseF (1 / 10 : ℚ) ^ (k + 1) := by
  have hunit : algebraMap ℚ (ActualRing (1 / 10 : ℚ)) (k.factorial : ℚ)⁻¹ *
      (k.factorial : ActualRing (1 / 10 : ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ (ActualRing (1 / 10 : ℚ))), ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), map_one]
  simp only [rawNumeratorClosed, Submodule.coe_smul, Algebra.smul_def,
    numeratorGenerator, factorialPole]
  calc
    _ = (algebraMap ℚ (ActualRing (1 / 10 : ℚ)) (k.factorial : ℚ)⁻¹ *
        (k.factorial : ActualRing (1 / 10 : ℚ))) *
        (actualMonomial (1 / 10 : ℚ) (fun i => (a i : ℤ)) *
          inverseF (1 / 10 : ℚ) ^ (k + 1)) := by ring
    _ = _ := by rw [hunit, one_mul]

theorem rawNumeratorClass_is_actual (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) :
    rawNumeratorClass a k ha = Submodule.Quotient.mk (rawNumeratorClosed a k ha) := rfl

def actualPolynomialClass (k : ℕ) (P : SixExponent →₀ ℚ)
    (hP : ∀ a ∈ P.support, exponentDegree a ≤ k) : NumericalResidue :=
  ∑ a ∈ P.support, if ha : a ∈ P.support then
    P a • rawNumeratorClass a k (hP a ha) else 0

theorem actual_lowPole_polynomial (k : ℕ) (hk : k ≤ 4) (P : SixExponent →₀ ℚ)
    (hP : ∀ a ∈ P.support, exponentDegree a ≤ k) :
    numericalGammaSection (WPCartierFinite.lowPoleProjection k P) =
      actualPolynomialClass k P hP := by
  have hv : WPCartierFinite.lowPoleProjection k P =
      ∑ a ∈ P.support, P a • lowPoleVector a k := by
    ext i
    simp [lowPoleProjection_support_formula]
  rw [hv, map_sum]
  unfold actualPolynomialClass
  apply Finset.sum_congr rfl
  intro a ha
  rw [dif_pos ha, map_smul, actual_lowPoleVector a k (hP a ha) hk]

theorem actual_lowPole_polynomial_projection (k : ℕ) (hk : k ≤ 4)
    (P : SixExponent →₀ ℚ) (hP : ∀ a ∈ P.support, exponentDegree a ≤ k) :
    numericalGammaProjection (actualPolynomialClass k P hP) =
      WPCartierFinite.lowPoleProjection k P := by
  rw [← actual_lowPole_polynomial k hk P hP, numericalGammaProjection_section]

theorem actual_finite_numerator_projection (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p)
    (k r : Fin 5) :
    numericalGammaProjection
      (actualPolynomialClass k.val (actualFiniteCoefficients p hp k r)
        (fun a ha => (actualFiniteCoefficients_support p hp hp7 k r a ha).1)) =
      WPCartierFinite.lowPoleProjection k.val (actualFiniteCoefficients p hp k r) := by
  apply actual_lowPole_polynomial_projection
  omega

/-- Field coordinates are transported by the actual localized rational coefficient map. -/
theorem actual_lowPole_field_coordinates (K : Type*) [Field K] [CharZero K]
    (a : SixExponent) (k : ℕ) (ha : exponentDegree a ≤ k) (hk : k ≤ 4) :
    (ActualSpecialization.tenthQuotientEquiv K).symm
        (ActualSpecialization.rationalConstantMap K (rawNumeratorClass a k ha)) =
      fun j => algebraMap ℚ K
        (Fin.append (lowPoleVector a k) (fun _ : Fin 6 => 0) j) := by
  apply (ActualSpecialization.tenthQuotientEquiv K).injective
  rw [LinearEquiv.apply_symm_apply, ActualSpecialization.tenthQuotientEquiv_apply]
  rw [← actual_lowPoleVector a k ha hk]
  exact ActualSpecialization.rationalConstantMap_elevenSection K _

def phiClosed (i : Fin 5) : FClosed (1 / 10 : ℚ) :=
  (i.val.factorial : ℚ)⁻¹ • Actual.gammaClosedElement (1 / 10 : ℚ) i

/-- These are actual representatives of the raw pole basis 1/f^(i+1). -/
theorem phiClosed_value (i : Fin 5) :
    (phiClosed i : ActualRing (1 / 10 : ℚ)) = inverseF (1 / 10 : ℚ) ^ (i.val + 1) := by
  have hunit : algebraMap ℚ (ActualRing (1 / 10 : ℚ)) (i.val.factorial : ℚ)⁻¹ *
      (i.val.factorial : ActualRing (1 / 10 : ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ (ActualRing (1 / 10 : ℚ))), ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i.val), map_one]
  simp only [phiClosed, Actual.gammaClosedElement, Submodule.coe_smul,
    Algebra.smul_def, factorialPole]
  rw [← mul_assoc, hunit, one_mul]

def numericalPhiSection : LowVector →ₗ[ℚ] NumericalResidue :=
  Fintype.linearCombination ℚ (fun i : Fin 5 => Submodule.Quotient.mk (phiClosed i))

/-- H is the change between the two literal actual pole bases. -/
theorem actual_factorial_change (v : LowVector) :
    numericalPhiSection (factorialDiagonal v) = numericalGammaSection v := by
  rw [numericalPhiSection, Fintype.linearCombination_apply, numericalGammaSection_formula]
  apply Finset.sum_congr rfl
  intro i hi
  change ((i.val.factorial : ℚ) * v i) •
      ((i.val.factorial : ℚ)⁻¹ • MellinFactors.gammaQuotientFamily (1 / 10 : ℚ) i) =
    v i • MellinFactors.gammaQuotientFamily (1 / 10 : ℚ) i
  rw [smul_smul]
  congr 1
  field_simp [show (i.val.factorial : ℚ) ≠ 0 from
    by exact_mod_cast Nat.factorial_ne_zero i.val]

/-- The finite selected sum is a sum of actual localized numerical residue classes. -/
def actualFiniteColumn (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p) (r : Fin 5) :
    NumericalResidue :=
  ∑ k : Fin 5, (p : ℚ) ^ k.val •
    actualPolynomialClass k.val (actualFiniteCoefficients p hp k r)
      (fun a ha => (actualFiniteCoefficients_support p hp hp7 k r a ha).1)

/-- The printed finite array is identified with the actual raw-coordinate finite projection.
The actual infinite Cartier operator and its tail estimate are separate obligations. -/
theorem finiteCartierArray_actual_column (p : ℕ) (hp : 0 < p) (hp7 : 7 ≤ p)
    (r : Fin 5) :
    numericalPhiSection (finiteCartierArray p hp r) = actualFiniteColumn p hp hp7 r := by
  rw [finiteCartierArray, finiteCoefficientArray_projection_formula, actual_factorial_change,
    map_sum]
  unfold actualFiniteColumn
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul, actual_lowPole_polynomial k.val (by omega)
    (actualFiniteCoefficients p hp k r)
    (fun a ha => (actualFiniteCoefficients_support p hp hp7 k r a ha).1)]

end
end WPCompletedCartier.LowPoleProjection
