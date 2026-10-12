import WPActualEtaIntegrality

open scoped BigOperators LaurentPolynomial
open LaurentPolynomial WPActualChiSource WPActualEtaIntegrality WPActualEtaPole
  WPActualEtaPrimitive WPPIntegralReduction

namespace WPLaurentIntegralResidue

theorem coefficientMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : Function.Injective (coefficientMap f) := by
  intro P Q h
  ext j
  apply hf
  simpa only [coefficientMap_coeff] using congrArg (fun L => L.coeff j) h

/-- Actual coefficient lift; its finite support is the support of the original source. -/
noncomputable def integralLift (p : ℕ) [Fact p.Prime] (P : integralLaurent p) :
    (integralRationals p)[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset P.val.coeff.support
    (fun j => ⟨P.val.coeff j, P.property j⟩) (by
      intro j hj
      apply Finsupp.mem_support_iff.mpr
      intro hz
      apply hj
      exact Subtype.ext hz))

theorem integralLift_coeff (p : ℕ) [Fact p.Prime] (P : integralLaurent p) (j : ℤ) :
    (integralLift p P).coeff j = ⟨P.val.coeff j, P.property j⟩ := by
  simp only [integralLift, Finsupp.onFinset_apply]

theorem integralLift_rational (p : ℕ) [Fact p.Prime] (P : integralLaurent p) :
    coefficientMap (integralRationals p).subtype (integralLift p P) = P.val := by
  ext j
  rw [coefficientMap_coeff, integralLift_coeff]
  rfl

noncomputable def integralLiftHom (p : ℕ) [Fact p.Prime] :
    integralLaurent p →+* (integralRationals p)[T;T⁻¹] where
  toFun := integralLift p
  map_zero' := by
    apply coefficientMap_injective _ (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, map_zero]
    rfl
  map_one' := by
    apply coefficientMap_injective _ (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, map_one]
    rfl
  map_add' P Q := by
    apply coefficientMap_injective _ (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, map_add, integralLift_rational, integralLift_rational]
    rfl
  map_mul' P Q := by
    apply coefficientMap_injective _ (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, map_mul, integralLift_rational, integralLift_rational]
    rfl

noncomputable def residueLaurent (p : ℕ) [Fact p.Prime] :
    integralLaurent p →+* (ZMod p)[T;T⁻¹] :=
  (coefficientMap (residueHom p)).comp (integralLiftHom p)

theorem residueLaurent_coeff (p : ℕ) [Fact p.Prime] (P : integralLaurent p) (j : ℤ) :
    (residueLaurent p P).coeff j = (P.val.coeff j : ZMod p) := by
  change (coefficientMap (residueHom p) (integralLift p P)).coeff j = _
  rw [coefficientMap_coeff, integralLift_coeff]
  rfl

theorem residueLaurent_C (p : ℕ) [Fact p.Prime] (c : integralRationals p) :
    residueLaurent p ⟨C c.val, integral_C p c.val c.property⟩ = C (c.val : ZMod p) := by
  have h : integralLift p ⟨C c.val, integral_C p c.val c.property⟩ = C c := by
    apply coefficientMap_injective _ (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, coefficientMap_C]
    rfl
  change coefficientMap (residueHom p) (integralLift p _) = _
  rw [h, coefficientMap_C]
  rfl

/-- Membership in the actual residue kernel, retaining integrality as part of the statement. -/
def residueZero (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹]) : Prop :=
  ∃ hP : P ∈ integralLaurent p, residueLaurent p ⟨P, hP⟩ = 0

theorem residueZero_iff (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹]) :
    residueZero p P ↔ P ∈ integralLaurent p ∧ ∀ j, (P.coeff j : ZMod p) = 0 := by
  constructor
  · rintro ⟨hP, hzero⟩
    refine ⟨hP, fun j => ?_⟩
    have hj := congrArg (fun L => L.coeff j) hzero
    rw [residueLaurent_coeff] at hj
    exact hj
  · rintro ⟨hP, hzero⟩
    refine ⟨hP, ?_⟩
    ext j
    exact (residueLaurent_coeff p _ j).trans (hzero j)

theorem residueZero_zero (p : ℕ) [Fact p.Prime] : residueZero p 0 := by
  exact ⟨(integralLaurent p).zero_mem, (residueLaurent p).map_zero⟩

theorem residueZero_add (p : ℕ) [Fact p.Prime] {P Q : ℚ[T;T⁻¹]}
    (hP : residueZero p P) (hQ : residueZero p Q) : residueZero p (P + Q) := by
  rcases hP with ⟨hP, hPr⟩
  rcases hQ with ⟨hQ, hQr⟩
  refine ⟨(integralLaurent p).add_mem hP hQ, ?_⟩
  change residueLaurent p (⟨P, hP⟩ + ⟨Q, hQ⟩) = 0
  rw [map_add, hPr, hQr, add_zero]

theorem residueZero_neg (p : ℕ) [Fact p.Prime] {P : ℚ[T;T⁻¹]}
    (hP : residueZero p P) : residueZero p (-P) := by
  rcases hP with ⟨hP, hPr⟩
  refine ⟨(integralLaurent p).neg_mem hP, ?_⟩
  change residueLaurent p (-⟨P, hP⟩) = 0
  rw [map_neg, hPr, neg_zero]

theorem residueZero_sub (p : ℕ) [Fact p.Prime] {P Q : ℚ[T;T⁻¹]}
    (hP : residueZero p P) (hQ : residueZero p Q) : residueZero p (P - Q) := by
  simpa only [sub_eq_add_neg] using residueZero_add p hP (residueZero_neg p hQ)

theorem residueZero_mul_integral (p : ℕ) [Fact p.Prime] {P Q : ℚ[T;T⁻¹]}
    (hP : residueZero p P) (hQ : Q ∈ integralLaurent p) : residueZero p (P * Q) := by
  rcases hP with ⟨hP, hPr⟩
  refine ⟨(integralLaurent p).mul_mem hP hQ, ?_⟩
  change residueLaurent p (⟨P, hP⟩ * ⟨Q, hQ⟩) = 0
  rw [map_mul, hPr, zero_mul]

theorem residueZero_sum (p : ℕ) [Fact p.Prime] {I : Type*} (s : Finset I)
    (f : I → ℚ[T;T⁻¹]) (hf : ∀ i ∈ s, residueZero p (f i)) :
    residueZero p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using residueZero_zero p
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact residueZero_add p (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem residueZero_C (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : 0 ≤ padicValRat p c) (hr : (c : ZMod p) = 0) : residueZero p (C c) := by
  refine ⟨integral_C p c hc, ?_⟩
  rw [residueLaurent_C p ⟨c, hc⟩, hr, map_zero]

theorem residueZero_dividedDifference (p : ℕ) [Fact p.Prime] (a : ℚ)
    (ha : a ∈ integralRationals p) (hai : a⁻¹ ∈ integralRationals p)
    (P : ℚ[T;T⁻¹]) (hP : residueZero p P) : residueZero p (dividedDifference a P) := by
  classical
  have hi := (residueZero_iff p P).mp hP
  change residueZero p (Finsupp.linearCombination ℚ (monomialQuotient a) P.coeff)
  rw [Finsupp.linearCombination_apply]
  apply residueZero_sum
  intro j _
  change residueZero p (P.coeff j • monomialQuotient a j)
  rw [smul_eq_C_mul]
  exact residueZero_mul_integral p (residueZero_C p _ (hi.1 j) (hi.2 j))
    (monomialQuotient_integral p a ha hai j)

theorem canonicalPrimitive_sub (p : ℕ) (P Q : ℚ[T;T⁻¹]) :
    canonicalPrimitive p (P - Q) = canonicalPrimitive p P - canonicalPrimitive p Q := by
  ext k
  simp only [canonicalPrimitive_coeff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  split_ifs <;> ring

theorem residueZero_canonicalPrimitive (p : ℕ) [Fact p.Prime]
    (P : ℚ[T;T⁻¹]) (hP : residueZero p P) : residueZero p (canonicalPrimitive p P) := by
  have hi := (residueZero_iff p P).mp hP
  apply (residueZero_iff p _).mpr
  refine ⟨canonicalPrimitive_integral p P hi.1, fun k => ?_⟩
  rw [canonicalPrimitive_coeff]
  by_cases hd : (p : ℤ) ∣ k
  · simp only [if_pos hd, Rat.cast_zero]
  · rw [if_neg hd, div_eq_mul_inv]
    have hinv : 0 ≤ padicValRat p (k : ℚ)⁻¹ := by
      rw [padicValRat.inv, integer_denominator_unit p k hd]
      simp
    rw [Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ (hi.1 (k - 1)))
      (integral_denominator_cast_ne_zero p _ hinv), hi.2 (k - 1), zero_mul]

end WPLaurentIntegralResidue
