import WPResidueQuotient.SpecializationCore
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The rational constant-parameter fiber is proved from actual finite Laurent
numerators. Coefficient evaluation has the principal kernel `u - 1/10`;
division by that coefficient preserves finite numerator support. Actual
common-pole presentations and finite logarithmic-image lifts then identify
the specialization kernel on the residue quotient. No residue basis or
formal-series evaluation is assumed.
-/

namespace WPResidueQuotient.Specialization

noncomputable section

open scoped BigOperators

open Parameter

/-- The literal coefficient defining the rational constant-parameter fiber. -/
def rationalFiberParameter : ParameterRing ℚ :=
  Parameter.u - algebraMap ℚ (ParameterRing ℚ) (1 / 10)

@[simp] theorem rationalFiberParameter_specializes :
    rationalSpecialization rationalFiberParameter = 0 := by
  rw [rationalFiberParameter, map_sub, rationalSpecialization_u,
    rationalSpecialization_scalar, sub_self]

theorem rationalSpecialization_surjective : Function.Surjective rationalSpecialization := by
  intro q
  exact ⟨algebraMap ℚ (ParameterRing ℚ) q, rationalSpecialization_scalar q⟩

theorem rationalSpecialization_eq_zero_iff (r : ParameterRing ℚ) :
    rationalSpecialization r = 0 ↔ ∃ s, r = rationalFiberParameter * s := by
  constructor
  · intro hr
    let sec := IsLocalization.Away.sec (denominatorPolynomial ℚ) r
    have hs : r * algebraMap (Polynomial ℚ) (ParameterRing ℚ)
        ((denominatorPolynomial ℚ) ^ sec.2) =
        algebraMap (Polynomial ℚ) (ParameterRing ℚ) sec.1 :=
      IsLocalization.Away.sec_spec (denominatorPolynomial ℚ) r
    have he : Polynomial.eval (1 / 10 : ℚ) sec.1 = 0 := by
      have h := congrArg rationalSpecialization hs
      rw [map_mul, hr, zero_mul, rationalSpecialization_polynomial] at h
      exact h.symm
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.2 he
    have ht : algebraMap (Polynomial ℚ) (ParameterRing ℚ)
        (Polynomial.X - Polynomial.C (1 / 10 : ℚ)) = rationalFiberParameter := by
      rw [map_sub]
      change Parameter.u - algebraMap (Polynomial ℚ) (ParameterRing ℚ)
        (algebraMap ℚ (Polynomial ℚ) (1 / 10)) = _
      rw [← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (ParameterRing ℚ)]
      rfl
    let invD : ParameterRing ℚ := IsLocalization.Away.invSelf (denominatorPolynomial ℚ)
    have hc : algebraMap (Polynomial ℚ) (ParameterRing ℚ)
        ((denominatorPolynomial ℚ) ^ sec.2) * invD ^ sec.2 = 1 := by
      rw [map_pow, ← mul_pow]
      change (algebraMap (Polynomial ℚ) (ParameterRing ℚ) (denominatorPolynomial ℚ) *
        IsLocalization.Away.invSelf (denominatorPolynomial ℚ)) ^ sec.2 = 1
      rw [IsLocalization.Away.mul_invSelf, one_pow]
    refine ⟨algebraMap (Polynomial ℚ) (ParameterRing ℚ) Q * invD ^ sec.2, ?_⟩
    calc
      r = (r * algebraMap (Polynomial ℚ) (ParameterRing ℚ)
          ((denominatorPolynomial ℚ) ^ sec.2)) * invD ^ sec.2 := by
        rw [mul_assoc, hc, mul_one]
      _ = algebraMap (Polynomial ℚ) (ParameterRing ℚ) sec.1 * invD ^ sec.2 :=
        congrArg (fun z => z * invD ^ sec.2) hs
      _ = rationalFiberParameter *
          (algebraMap (Polynomial ℚ) (ParameterRing ℚ) Q * invD ^ sec.2) := by
        rw [hQ, map_mul, ht, mul_assoc]
  · rintro ⟨s, rfl⟩
    rw [map_mul, rationalFiberParameter_specializes, zero_mul]

section PrincipalKernel

variable {R S : Type*} [CommRing R] [CommRing S]
variable (φ : R →+* S) (t : R)
variable (hker : ∀ r : R, φ r = 0 ↔ ∃ s, r = t * s)

include hker in
theorem coefficientKernel_parameter_zero : φ t = 0 :=
  (hker t).2 ⟨1, (mul_one t).symm⟩

include hker in
/-- Coefficient division uses precisely the finite support of the original numerator. -/
theorem supportedNumerator_divide (m : ℕ) (P : LaurentPolynomial R)
    (hP : P ∈ numeratorFiltration R m) (hz : laurentMap φ P = 0) :
    ∃ Q : LaurentPolynomial R, Q ∈ numeratorFiltration R m ∧ P = t • Q := by
  classical
  have hcoeff : ∀ x : Exponents, ∃ r : R, P.coeff x = t * r := by
    intro x
    apply (hker (P.coeff x)).1
    have he := congrArg (fun Q : LaurentPolynomial S => Q.coeff x) hz
    simpa only [laurentMap_coefficient, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using he
  choose c hc using hcoeff
  let Q : LaurentPolynomial R := ∑ x ∈ P.coeff.support, AddMonoidAlgebra.single x (c x)
  have hQ : Q ∈ numeratorFiltration R m := by
    apply (numeratorFiltration R m).sum_mem
    intro x hx
    exact single_mem_numeratorFiltration x (c x) m
      ((mem_numeratorFiltration m P).1 hP x hx)
  refine ⟨Q, hQ, ?_⟩
  calc
    P = ∑ x ∈ P.coeff.support, AddMonoidAlgebra.single x (P.coeff x) := by
      simpa only [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single P).symm
    _ = ∑ x ∈ P.coeff.support, t • AddMonoidAlgebra.single x (c x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hc, AddMonoidAlgebra.smul_single']
    _ = t • Q := Finset.smul_sum.symm

variable [Algebra ℚ R] [IsDomain S]

include hker in
theorem closedMap_eq_zero_iff (u : R) (g : FClosed u) :
    closedMap φ u g = 0 ↔ ∃ h : FClosed u, g = t • h := by
  constructor
  · intro hg
    obtain ⟨m, P, hm, _, hP, he⟩ := FClosed_common_pole u g.property
    have hz : poleLinearMap (φ u) m (laurentMap φ P) = 0 := by
      have h := congrArg (fun z : FClosed (φ u) => (z : ActualRing (φ u))) hg
      change actualMap φ u (g : ActualRing u) = 0 at h
      rw [he, actualMap_poleLinearMap] at h
      exact h
    have hzero := (poleLinearMap_eq_zero_iff (φ u) m (laurentMap φ P)).1 hz
    obtain ⟨Q, hQ, hPQ⟩ := supportedNumerator_divide φ t hker m P hP hzero
    have hQc : poleLinearMap u m Q ∈ FClosed u := by
      apply commonPoleModule_le_FClosed u
      exact ⟨m, Q, hm, Nat.zero_le m, hQ, rfl⟩
    refine ⟨⟨poleLinearMap u m Q, hQc⟩, ?_⟩
    apply Subtype.ext
    change (g : ActualRing u) = t • poleLinearMap u m Q
    rw [he, hPQ, map_smul]
  · rintro ⟨h, rfl⟩
    rw [map_smulₛₗ, coefficientKernel_parameter_zero φ t hker, zero_smul]

variable (hφ : Function.Surjective φ)

omit [Algebra ℚ R] [IsDomain S] in
include hφ in
/-- Every actual target logarithmic image has an actual source logarithmic-image lift. -/
theorem exact_specialization_lift (u : R) (g : FClosed (φ u))
    (hg : g ∈ exactSubmodule (φ u)) :
    ∃ h : FClosed u, h ∈ exactSubmodule u ∧ closedMap φ u h = g := by
  classical
  rw [← exactAggregate_range] at hg
  obtain ⟨a, rfl⟩ := hg
  have hlift : ∀ i : Fin 5, ∃ b : FClosed u, closedMap φ u b = a i :=
    fun i => closedMap_surjective φ hφ u (a i)
  choose b hb using hlift
  refine ⟨exactAggregate u b, ?_, ?_⟩
  · rw [← exactAggregate_range]
    exact LinearMap.mem_range_self (exactAggregate u) b
  · simp only [exactAggregate_apply, map_sum, closedMap_commutes_DClosed, hb]

include hker hφ in
/-- Quotient specialization has exactly the principal scalar kernel. -/
theorem quotientMap_eq_zero_iff (u : R) (g : ClosedResidueQuotient u) :
    quotientMap φ u g = 0 ↔ ∃ h : ClosedResidueQuotient u, g = t • h := by
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := (exactSubmodule u).mkQ_surjective g
    have ha : closedMap φ u a ∈ exactSubmodule (φ u) := by
      rw [quotientMap_mkQ] at hg
      exact (Submodule.Quotient.mk_eq_zero (exactSubmodule (φ u))).1 hg
    obtain ⟨b, hb, hba⟩ := exact_specialization_lift φ hφ u (closedMap φ u a) ha
    have hz : closedMap φ u (a - b) = 0 := by rw [map_sub, hba, sub_self]
    obtain ⟨c, hc⟩ := (closedMap_eq_zero_iff φ t hker u (a - b)).1 hz
    refine ⟨(exactSubmodule u).mkQ c, ?_⟩
    have hbzero : (exactSubmodule u).mkQ b = 0 :=
      (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).2 hb
    have h := congrArg (exactSubmodule u).mkQ hc
    rw [map_sub, hbzero, sub_zero, map_smul] at h
    exact h
  · rintro ⟨h, rfl⟩
    rw [map_smulₛₗ, coefficientKernel_parameter_zero φ t hker, zero_smul]

end PrincipalKernel

section FieldFiber

variable (K : Type*) [Field K]

/-- Actual coefficient evaluation, extended only after its denominator is proved nonzero. -/
def fieldSpecialization (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) : ParameterRing K →+* K :=
  IsLocalization.Away.lift (denominatorPolynomial K)
    (g := Polynomial.evalRingHom c) (isUnit_iff_ne_zero.2 hc)

@[simp] theorem fieldSpecialization_polynomial (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) (P : Polynomial K) :
    fieldSpecialization K c hc (algebraMap (Polynomial K) (ParameterRing K) P) =
      Polynomial.eval c P := by
  simp [fieldSpecialization]

@[simp] theorem fieldSpecialization_scalar (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) (a : K) :
    fieldSpecialization K c hc (algebraMap K (ParameterRing K) a) = a := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (ParameterRing K)]
  change fieldSpecialization K c hc
    (algebraMap (Polynomial K) (ParameterRing K) (Polynomial.C a)) = a
  rw [fieldSpecialization_polynomial, Polynomial.eval_C]

@[simp] theorem fieldSpecialization_u (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    fieldSpecialization K c hc (Parameter.u : ParameterRing K) = c := by
  rw [Parameter.u, fieldSpecialization_polynomial, Polynomial.eval_X]

theorem fieldSpecialization_surjective (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    Function.Surjective (fieldSpecialization K c hc) := by
  intro a
  exact ⟨algebraMap K (ParameterRing K) a, fieldSpecialization_scalar K c hc a⟩

def fieldFiberParameter (c : K) : ParameterRing K :=
  Parameter.u - algebraMap K (ParameterRing K) c

@[simp] theorem fieldFiberParameter_specializes (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    fieldSpecialization K c hc (fieldFiberParameter K c) = 0 := by
  rw [fieldFiberParameter, map_sub, fieldSpecialization_u,
    fieldSpecialization_scalar, sub_self]

theorem fieldSpecialization_eq_zero_iff (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) (r : ParameterRing K) :
    fieldSpecialization K c hc r = 0 ↔ ∃ s, r = fieldFiberParameter K c * s := by
  constructor
  · intro hr
    let sec := IsLocalization.Away.sec (denominatorPolynomial K) r
    have hs : r * algebraMap (Polynomial K) (ParameterRing K)
        ((denominatorPolynomial K) ^ sec.2) =
        algebraMap (Polynomial K) (ParameterRing K) sec.1 :=
      IsLocalization.Away.sec_spec (denominatorPolynomial K) r
    have he : Polynomial.eval c sec.1 = 0 := by
      have h := congrArg (fieldSpecialization K c hc) hs
      rw [map_mul, hr, zero_mul, fieldSpecialization_polynomial] at h
      exact h.symm
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.2 he
    have ht : algebraMap (Polynomial K) (ParameterRing K)
        (Polynomial.X - Polynomial.C c) = fieldFiberParameter K c := by
      rw [map_sub]
      change Parameter.u - algebraMap (Polynomial K) (ParameterRing K)
        (algebraMap K (Polynomial K) c) = _
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (ParameterRing K)]
      rfl
    let invD : ParameterRing K := IsLocalization.Away.invSelf (denominatorPolynomial K)
    have hcancel : algebraMap (Polynomial K) (ParameterRing K)
        ((denominatorPolynomial K) ^ sec.2) * invD ^ sec.2 = 1 := by
      rw [map_pow, ← mul_pow]
      change (algebraMap (Polynomial K) (ParameterRing K) (denominatorPolynomial K) *
        IsLocalization.Away.invSelf (denominatorPolynomial K)) ^ sec.2 = 1
      rw [IsLocalization.Away.mul_invSelf, one_pow]
    refine ⟨algebraMap (Polynomial K) (ParameterRing K) Q * invD ^ sec.2, ?_⟩
    calc
      r = (r * algebraMap (Polynomial K) (ParameterRing K)
          ((denominatorPolynomial K) ^ sec.2)) * invD ^ sec.2 := by
        rw [mul_assoc, hcancel, mul_one]
      _ = algebraMap (Polynomial K) (ParameterRing K) sec.1 * invD ^ sec.2 :=
        congrArg (fun z => z * invD ^ sec.2) hs
      _ = fieldFiberParameter K c *
          (algebraMap (Polynomial K) (ParameterRing K) Q * invD ^ sec.2) := by
        rw [hQ, map_mul, ht, mul_assoc]
  · rintro ⟨s, rfl⟩
    rw [map_mul, fieldFiberParameter_specializes, zero_mul]

variable [CharZero K]

def fieldFiberSubmodule (c : K) :
    Submodule (ParameterRing K) (ClosedResidueQuotient (Parameter.u : ParameterRing K)) :=
  LinearMap.range (fieldFiberParameter K c • LinearMap.id)

omit [CharZero K] in
theorem mem_fieldFiberSubmodule (c : K)
    (g : ClosedResidueQuotient (Parameter.u : ParameterRing K)) :
    g ∈ fieldFiberSubmodule K c ↔ ∃ h, g = fieldFiberParameter K c • h := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, hh.symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

theorem field_quotient_specialization_kernel (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    LinearMap.ker (quotientMap (fieldSpecialization K c hc)
      (Parameter.u : ParameterRing K)) = fieldFiberSubmodule K c := by
  ext g
  rw [LinearMap.mem_ker, mem_fieldFiberSubmodule]
  exact quotientMap_eq_zero_iff (fieldSpecialization K c hc) (fieldFiberParameter K c)
    (fieldSpecialization_eq_zero_iff K c hc) (fieldSpecialization_surjective K c hc)
    Parameter.u g

def fieldQuotientMap (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    ClosedResidueQuotient (Parameter.u : ParameterRing K) →ₗ[K]
      ClosedResidueQuotient (fieldSpecialization K c hc (Parameter.u : ParameterRing K)) where
  toFun := quotientMap (fieldSpecialization K c hc) Parameter.u
  map_add' g h := map_add (quotientMap (fieldSpecialization K c hc) Parameter.u) g h
  map_smul' a g := by
    rw [← IsScalarTower.algebraMap_smul (ParameterRing K) a g, map_smulₛₗ,
      fieldSpecialization_scalar]
    rfl

omit [CharZero K] in
theorem fieldQuotientMap_surjective (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    Function.Surjective (fieldQuotientMap K c hc) :=
  quotientMap_surjective (fieldSpecialization K c hc)
    (fieldSpecialization_surjective K c hc) Parameter.u

theorem fieldQuotientMap_kernel (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    LinearMap.ker (fieldQuotientMap K c hc) = (fieldFiberSubmodule K c).restrictScalars K := by
  ext g
  change quotientMap (fieldSpecialization K c hc) Parameter.u g = 0 ↔
    g ∈ fieldFiberSubmodule K c
  rw [← field_quotient_specialization_kernel K c hc, LinearMap.mem_ker]

/-- Actual constant-parameter quotient identification over any characteristic-zero field. -/
def fieldFiberEquiv (c : K)
    (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0) :
    ((ClosedResidueQuotient (Parameter.u : ParameterRing K)) ⧸
      (fieldFiberSubmodule K c).restrictScalars K) ≃ₗ[K] ClosedResidueQuotient c := by
  let e := (fieldQuotientMap K c hc).quotKerEquivOfSurjective
    (fieldQuotientMap_surjective K c hc)
  rw [fieldQuotientMap_kernel, fieldSpecialization_u] at e
  exact e

theorem tenth_denominator_nonzero :
    Polynomial.eval (1 / 10 : K) (denominatorPolynomial K) ≠ 0 := by
  norm_num [denominatorPolynomial, discriminantPolynomial]

def tenthSpecialization : ParameterRing K →+* K :=
  fieldSpecialization K (1 / 10) (tenth_denominator_nonzero K)

@[simp] theorem tenthSpecialization_u :
    tenthSpecialization K (Parameter.u : ParameterRing K) = (1 / 10 : K) :=
  fieldSpecialization_u K (1 / 10) (tenth_denominator_nonzero K)

/-- The literal `1/10` family, including a characteristic-zero p-adic coefficient field. -/
def tenthFiberEquiv :
    ((ClosedResidueQuotient (Parameter.u : ParameterRing K)) ⧸
      (fieldFiberSubmodule K (1 / 10)).restrictScalars K) ≃ₗ[K]
        ClosedResidueQuotient (1 / 10 : K) :=
  fieldFiberEquiv K (1 / 10) (tenth_denominator_nonzero K)

end FieldFiber

/-- Multiples of the fiber parameter inside the literal rational residue quotient. -/
def rationalFiberSubmodule :
    Submodule (ParameterRing ℚ) (ClosedResidueQuotient (Parameter.u : ParameterRing ℚ)) :=
  LinearMap.range (rationalFiberParameter • LinearMap.id)

theorem mem_rationalFiberSubmodule (g : ClosedResidueQuotient (Parameter.u : ParameterRing ℚ)) :
    g ∈ rationalFiberSubmodule ↔ ∃ h, g = rationalFiberParameter • h := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, hh.symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, rfl⟩

theorem rational_quotient_specialization_kernel :
    LinearMap.ker (quotientMap rationalSpecialization (Parameter.u : ParameterRing ℚ)) =
      rationalFiberSubmodule := by
  ext g
  rw [LinearMap.mem_ker, mem_rationalFiberSubmodule]
  exact quotientMap_eq_zero_iff rationalSpecialization rationalFiberParameter
    rationalSpecialization_eq_zero_iff rationalSpecialization_surjective Parameter.u g

/-- The actual specialization map is linear over the rational scalar field. -/
def rationalQuotientMap :
    ClosedResidueQuotient (Parameter.u : ParameterRing ℚ) →ₗ[ℚ]
      ClosedResidueQuotient (rationalSpecialization (Parameter.u : ParameterRing ℚ)) where
  toFun := quotientMap rationalSpecialization Parameter.u
  map_add' g h := map_add (quotientMap rationalSpecialization Parameter.u) g h
  map_smul' q g := by
    rw [← IsScalarTower.algebraMap_smul (ParameterRing ℚ) q g, map_smulₛₗ,
      rationalSpecialization_scalar]
    rfl

theorem rationalQuotientMap_surjective : Function.Surjective rationalQuotientMap :=
  quotientMap_surjective rationalSpecialization rationalSpecialization_surjective Parameter.u

theorem rationalQuotientMap_kernel : LinearMap.ker rationalQuotientMap =
    rationalFiberSubmodule.restrictScalars ℚ := by
  ext g
  change quotientMap rationalSpecialization Parameter.u g = 0 ↔ g ∈ rationalFiberSubmodule
  rw [← rational_quotient_specialization_kernel, LinearMap.mem_ker]

/-- The actual constant-parameter quotient is the actual parameter quotient modulo `(u-1/10)`. -/
def rationalFiberEquiv :
    ((ClosedResidueQuotient (Parameter.u : ParameterRing ℚ)) ⧸
      rationalFiberSubmodule.restrictScalars ℚ) ≃ₗ[ℚ]
        ClosedResidueQuotient (1 / 10 : ℚ) := by
  let e := rationalQuotientMap.quotKerEquivOfSurjective rationalQuotientMap_surjective
  rw [rationalQuotientMap_kernel, rationalSpecialization_u] at e
  exact e

end

end WPResidueQuotient.Specialization
