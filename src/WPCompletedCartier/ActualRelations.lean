import WPResidueQuotient.PolePresentation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace WPCompletedCartier

noncomputable section

open scoped BigOperators
open WPResidueQuotient

variable {R : Type*} [CommRing R]

abbrev ClosedIndex := {i : ℕ × Exponents // canonicalDegreeNat i.2 ≤ i.1 + 1}

abbrev ClosedPresentation (R : Type*) [CommRing R] := ClosedIndex →₀ R

def presentationGenerator (u : R) (i : ClosedIndex) : ActualRing u :=
  canonicalNumeratorGenerator u i.val.2 i.val.1

def presentationMap (u : R) : ClosedPresentation R →ₗ[R] ActualRing u :=
  Finsupp.linearCombination R (presentationGenerator u)

theorem presentationGenerator_mem (u : R) (i : ClosedIndex) :
    presentationGenerator u i ∈ FClosed u := by
  rw [FClosed_eq_canonical_span]
  exact Submodule.subset_span ⟨i.val.2, i.val.1, i.property, rfl⟩

theorem presentationMap_mem (u : R) (v : ClosedPresentation R) :
    presentationMap u v ∈ FClosed u := by
  classical
  change v.sum (fun i r => r • presentationGenerator u i) ∈ FClosed u
  exact (FClosed u).sum_mem (fun i _ =>
    (FClosed u).smul_mem (v i) (presentationGenerator_mem u i))

def presentationToClosed (u : R) : ClosedPresentation R →ₗ[R] FClosed u :=
  (presentationMap u).codRestrict (FClosed u) (presentationMap_mem u)

theorem presentationMap_range (u : R) :
    LinearMap.range (presentationMap u) = FClosed u := by
  rw [presentationMap, Finsupp.range_linearCombination, FClosed_eq_canonical_span]
  congr 1
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val.2, i.val.1, i.property, rfl⟩
  · rintro ⟨x, n, hx, rfl⟩
    exact ⟨⟨(n, x), hx⟩, rfl⟩

theorem presentationToClosed_surjective (u : R) :
    Function.Surjective (presentationToClosed u) := by
  intro g
  have hg : g.val ∈ LinearMap.range (presentationMap u) :=
    (presentationMap_range u).symm ▸ g.property
  obtain ⟨v, hv⟩ := hg
  exact ⟨v, Subtype.ext hv⟩

def commonNumeratorGenerator (u : R) (M : ℕ) (i : ClosedIndex) :
    WPResidueQuotient.LaurentPolynomial R :=
  (i.val.1.factorial : R) •
    (AddMonoidAlgebra.single i.val.2 1 * torusPolynomial u ^ (M - (i.val.1 + 1)))

def commonNumerator (u : R) (M : ℕ) :
    ClosedPresentation R →ₗ[R] WPResidueQuotient.LaurentPolynomial R :=
  Finsupp.linearCombination R (commonNumeratorGenerator u M)

theorem commonNumeratorGenerator_supported (u : R) (M : ℕ) (i : ClosedIndex)
    (hi : i.val.1 + 1 ≤ M) : commonNumeratorGenerator u M i ∈ numeratorFiltration R M := by
  have h := numeratorFiltration_mul_f_pow u (i.val.1 + 1)
    (M - (i.val.1 + 1))
    (single_mem_numeratorFiltration i.val.2 (1 : R) (i.val.1 + 1) i.property)
  rw [Nat.add_sub_of_le hi] at h
  exact (numeratorFiltration R M).smul_mem _ h

theorem presentationGenerator_common_pole (u : R) (M : ℕ) (i : ClosedIndex)
    (hi : i.val.1 + 1 ≤ M) :
    presentationGenerator u i = poleLinearMap u M (commonNumeratorGenerator u M i) := by
  rw [presentationGenerator, canonicalNumeratorGenerator,
    factorialNumeratorMap_apply, factorialPole_common_pole u i.val.1 M hi]
  simp only [commonNumeratorGenerator, poleLinearMap_apply, map_mul, map_pow,
    Algebra.smul_def, map_natCast]
  ring

theorem presentationMap_common_pole (u : R) (M : ℕ) (v : ClosedPresentation R)
    (hM : ∀ i ∈ v.support, i.val.1 + 1 ≤ M) :
    presentationMap u v = poleLinearMap u M (commonNumerator u M v) := by
  classical
  change (∑ i ∈ v.support, v i • presentationGenerator u i) =
    poleLinearMap u M (∑ i ∈ v.support, v i • commonNumeratorGenerator u M i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, presentationGenerator_common_pole u M i (hM i hi)]

theorem presentation_relation_iff [IsDomain R] (u : R) (M : ℕ)
    (v : ClosedPresentation R) (hM : ∀ i ∈ v.support, i.val.1 + 1 ≤ M) :
    presentationMap u v = 0 ↔ commonNumerator u M v = 0 := by
  rw [presentationMap_common_pole u M v hM, poleLinearMap_eq_zero_iff]

def commonPoleBound (v : ClosedPresentation R) : ℕ :=
  1 + ∑ i ∈ v.support, i.val.1

theorem le_commonPoleBound (v : ClosedPresentation R) (i : ClosedIndex)
    (hi : i ∈ v.support) : i.val.1 + 1 ≤ commonPoleBound v := by
  have h : i.val.1 ≤ ∑ j ∈ v.support, j.val.1 :=
    Finset.single_le_sum (fun j _ => Nat.zero_le j.val.1) hi
  unfold commonPoleBound
  omega

theorem all_actual_relations_are_common_numerators [IsDomain R] (u : R)
    (v : ClosedPresentation R) :
    presentationMap u v = 0 ↔ commonNumerator u (commonPoleBound v) v = 0 :=
  presentation_relation_iff u _ v (le_commonPoleBound v)

end

end WPCompletedCartier
