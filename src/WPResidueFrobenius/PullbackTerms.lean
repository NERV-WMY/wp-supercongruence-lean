import WPResidueFrobenius.Valuation

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def integralPolynomialGenerator (n : ℕ) (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] (n+1)) : FClosed (Parameter.integralTenth p hp) :=
  ⟨factorialNumeratorMap (Parameter.integralTenth p hp) n P,
    factorialNumeratorMap_mem_closed _ n hP⟩

theorem integralPolynomialGenerator_coordinates_bound (n : ℕ)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] (n+1)) : ∃ w : Fin 11 → ℤ_[p],
    ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
      (integralPolynomialGenerator p hp n P hP) = (p : ℤ)^(((n/p)-5)/5) • w := by
  let property (Q : WPResidueQuotient.LaurentPolynomial ℤ_[p]) : Prop :=
    ∀ hQ : Q ∈ numeratorFiltration ℤ_[p] (n+1), ∃ w : Fin 11 → ℤ_[p],
      ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
        (integralPolynomialGenerator p hp n Q hQ) = (p : ℤ)^(((n/p)-5)/5) • w
  have haux : ∀ Q, Q ∈ Submodule.span ℤ_[p]
      {AddMonoidAlgebra.single x (1 : ℤ_[p]) | x ∈ {x | canonicalDegreeNat x ≤ n+1}} →
      property Q := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      intro hmem
      obtain ⟨x, hx, rfl⟩ := hQ
      have ha : (∑ i, canonicalAsNat x i) ≤ n+1 := by rwa [canonicalAsNat_sum]
      have he : integralPolynomialGenerator p hp n (AddMonoidAlgebra.single x 1) hmem =
          integralGenerator p hp (canonicalAsNat x) n ha := by
        apply Subtype.ext
        exact canonicalNumeratorGenerator_as_nonnegative _ x n
      rw [he]
      exact integralGenerator_coordinates_bound p hp hp7 hp19 _ n ha
    | zero =>
      intro hmem
      refine ⟨0, ?_⟩
      have he : integralPolynomialGenerator p hp n 0 hmem = 0 := by
        apply Subtype.ext; exact map_zero _
      rw [he, map_zero, smul_zero]
    | add P Q hsP hsQ hP hQ =>
      intro hmem
      have hmP : P ∈ numeratorFiltration ℤ_[p] (n+1) := by
        rwa [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single]
      have hmQ : Q ∈ numeratorFiltration ℤ_[p] (n+1) := by
        rwa [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single]
      obtain ⟨v, hv⟩ := hP hmP
      obtain ⟨w, hw⟩ := hQ hmQ
      refine ⟨v+w, ?_⟩
      have he : integralPolynomialGenerator p hp n (P+Q) hmem =
          integralPolynomialGenerator p hp n P hmP + integralPolynomialGenerator p hp n Q hmQ := by
        apply Subtype.ext; exact map_add _ _ _
      rw [he, map_add, hv, hw, smul_add]
    | smul c P hsP hP =>
      intro hmem
      have hmP : P ∈ numeratorFiltration ℤ_[p] (n+1) := by
        rwa [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single]
      obtain ⟨v, hv⟩ := hP hmP
      refine ⟨c • v, ?_⟩
      have he : integralPolynomialGenerator p hp n (c • P) hmem =
          c • integralPolynomialGenerator p hp n P hmP := by
        apply Subtype.ext; exact map_smul _ _ _
      rw [he, map_smul, hv, smul_comm]
  apply haux P _ hP
  rwa [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single] at hP

theorem numeratorFiltration_pow {R : Type*} [CommRing R]
    (P : WPResidueQuotient.LaurentPolynomial R) (m k : ℕ)
    (hP : P ∈ numeratorFiltration R m) : P^k ∈ numeratorFiltration R (m*k) := by
  induction k with
  | zero => simpa using one_mem_numeratorFiltration (R := R) 0
  | succ k ih =>
      simpa [pow_succ, Nat.mul_succ] using numeratorFiltration_mul ih hP

def pullbackNumerator (P : WPResidueQuotient.LaurentPolynomial ℤ_[p]) (k : ℕ) :=
  laurentPhi ℤ_[p] p P * G p hp ^ k

theorem pullbackNumerator_supported (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (m k : ℕ) (hP : P ∈ numeratorFiltration ℤ_[p] m) :
    pullbackNumerator p hp P k ∈ numeratorFiltration ℤ_[p] (p*(m+k)) := by
  simpa [pullbackNumerator, Nat.mul_add] using numeratorFiltration_mul
    (laurentPhi_supported ℤ_[p] p m P hP)
    (numeratorFiltration_pow (G p hp) p k (G_supported p hp))

def rawIntegralGenerator (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (Parameter.integralTenth p hp) :=
  integralPolynomialGenerator p hp (p*(r+k)-1) (pullbackNumerator p hp P k)
    (by
      have he : p*(r+k)-1+1 = p*(r+k) := by
        have hpos := Nat.mul_pos (Fact.out : p.Prime).pos (by omega : 0 < r+k)
        omega
      rw [he]
      exact pullbackNumerator_supported p hp P r k hP)

theorem rawIntegralGenerator_coordinates_bound (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : ∃ w : Fin 11 → ℤ_[p],
    ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
      (rawIntegralGenerator p hp r k hr P hP) = (p : ℤ)^(pullbackGain r k) • w := by
  obtain ⟨w, hw⟩ := integralPolynomialGenerator_coordinates_bound p hp hp7 hp19
    (p*(r+k)-1) (pullbackNumerator p hp P k) _
  refine ⟨w, ?_⟩
  rw [pullbackGain_is_closed_gain p r k (Fact.out : p.Prime).pos hr] at hw
  exact hw

def rawPullbackTerm (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : FClosed (1/10 : ℚ_[p]) :=
  (pullbackScalar p r k : ℚ_[p]) • integralToField p hp
    (rawIntegralGenerator p hp r k hr P hP)

include hp7 hp19 in
theorem rawPullbackTerm_coordinates_factor (r k : ℕ) (hr : 1 ≤ r)
    (P : WPResidueQuotient.LaurentPolynomial ℤ_[p])
    (hP : P ∈ numeratorFiltration ℤ_[p] r) : ∃ w : Fin 11 → ℤ_[p],
    ActualSpecialization.tenthClosedCoordinates ℚ_[p] (rawPullbackTerm p hp r k hr P hP) =
      fun i => (pullbackScalar p r k : ℚ_[p]) * (p : ℚ_[p])^(pullbackGain r k) *
        IntegralTransport.padicCoefficientMap p (w i) := by
  obtain ⟨w, hw⟩ := rawIntegralGenerator_coordinates_bound p hp hp7 hp19 r k hr P hP
  refine ⟨w, ?_⟩
  rw [rawPullbackTerm, map_smul, integralToField_coordinates p hp hp7 hp19, hw]
  funext i
  simp [Algebra.smul_def, mul_assoc]

end WPResidueFrobenius
