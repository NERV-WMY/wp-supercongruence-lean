import WPResidueQuotient.MellinIntegral
import WPResidueQuotient.VertexBoundary
import WPResidueQuotient.PoleRecurrence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis

/-!
The actual eleven-generator section is built from the five literal
factorial poles and six literal boundary fractions. Vertex and Mellin
functionals prove independence, and the proved finite numerator reduction
proves surjectivity. The resulting coordinate map and exact direct summand
are consequently constructed, rather than supplied as hypotheses.
-/

noncomputable section

namespace WPResidueQuotient.Actual

open scoped BigOperators LaurentSeries
open MellinFactors

variable {R : Type*} [CommRing R]

def gammaClosedElement (u : R) (i : Fin 5) : FClosed u :=
  ⟨factorialPole u i.val, FInterior_le_FClosed u (factorialPole_mem_interior u i.val)⟩

def elevenClosedElement (u : R) : Fin 11 → FClosed u :=
  Fin.append (gammaClosedElement u) (vertexBoundaryElement u)

@[simp] theorem elevenClosedElement_left (u : R) (i : Fin 5) :
    elevenClosedElement u (Fin.castAdd 6 i) = gammaClosedElement u i :=
  Fin.append_left _ _ _

@[simp] theorem elevenClosedElement_right (u : R) (i : Fin 6) :
    elevenClosedElement u (Fin.natAdd 5 i) = vertexBoundaryElement u i :=
  Fin.append_right _ _ _

/-- Literal coefficient sums on the requested eleven actual fractions. -/
def elevenSection (u : R) : (Fin 11 → R) →ₗ[R] FClosed u :=
  Fintype.linearCombination R (elevenClosedElement u)

theorem elevenSection_apply (u : R) (c : Fin 11 → R) :
    elevenSection u c = ∑ i : Fin 11, c i • elevenClosedElement u i :=
  Fintype.linearCombination_apply _ _ _

@[simp] theorem elevenSection_single (u : R) (i : Fin 11) :
    elevenSection u (Pi.single i 1) = elevenClosedElement u i := by
  classical
  rw [elevenSection, Fintype.linearCombination_apply_single, one_smul]

theorem elevenSection_apply_blocks (u : R) (c : Fin 11 → R) :
    elevenSection u c =
      (∑ i : Fin 5, c (Fin.castAdd 6 i) • gammaClosedElement u i) +
        ∑ i : Fin 6, c (Fin.natAdd 5 i) • vertexBoundaryElement u i := by
  rw [elevenSection_apply, Fin.sum_univ_add (a := 5) (b := 6)]
  simp only [elevenClosedElement_left, elevenClosedElement_right]

theorem elevenSection_append_val (u : R) (a : Fin 5 → R) (c : Fin 6 → R) :
    ((elevenSection u (Fin.append a c) : FClosed u) : ActualRing u) =
      (∑ i : Fin 5, a i • factorialPole u i.val) + ∑ i : Fin 6, c i • b u i := by
  rw [elevenSection_apply_blocks]
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    Fin.append_left, Fin.append_right, gammaClosedElement, vertexBoundaryElement]

def elevenQuotientFamily (u : R) (i : Fin 11) : ClosedResidueQuotient u :=
  (exactSubmodule u).mkQ (elevenClosedElement u i)

@[simp] theorem elevenQuotientFamily_left (u : R) (i : Fin 5) :
    elevenQuotientFamily u (Fin.castAdd 6 i) = gammaQuotientFamily u i := by
  rw [elevenQuotientFamily, elevenClosedElement_left]
  rfl

@[simp] theorem elevenQuotientFamily_right (u : R) (i : Fin 6) :
    elevenQuotientFamily u (Fin.natAdd 5 i) =
      (exactSubmodule u).mkQ (vertexBoundaryElement u i) := by
  rw [elevenQuotientFamily, elevenClosedElement_right]

def elevenQuotientSection (u : R) : (Fin 11 → R) →ₗ[R] ClosedResidueQuotient u :=
  (exactSubmodule u).mkQ.comp (elevenSection u)

theorem elevenQuotientSection_apply (u : R) (c : Fin 11 → R) :
    elevenQuotientSection u c = ∑ i : Fin 11, c i • elevenQuotientFamily u i := by
  simp only [elevenQuotientSection, LinearMap.comp_apply, elevenSection_apply,
    map_sum, map_smul, elevenQuotientFamily]

theorem uUnitOfInverse (u v : R) (huv : v * (6 * u) = 1) : IsUnit u :=
  IsUnit.of_mul_eq_one_right (6 * v) (by
    calc
      (6 * v) * u = v * (6 * u) := by ring
      _ = 1 := huv)

def interiorInClosed (u : R) : Submodule R (FClosed u) :=
  (FInterior u).comap (FClosed u).subtype

def interiorCoordinates (R : Type*) [CommRing R] : Submodule R (Fin 11 → R) where
  carrier := {c | ∀ j : Fin 6, c (Fin.natAdd 5 j) = 0}
  zero_mem' _ := rfl
  add_mem' := by
    intro a b ha hb j
    simp only [Pi.add_apply, ha j, hb j, add_zero]
  smul_mem' := by
    intro r c hc j
    simp only [Pi.smul_apply, hc j, smul_zero]

theorem elevenClosedElement_left_interior (u : R) (i : Fin 5) :
    ((elevenClosedElement u (Fin.castAdd 6 i) : FClosed u) : ActualRing u) ∈ FInterior u := by
  rw [elevenClosedElement_left]
  exact factorialPole_mem_interior u i.val

theorem elevenSection_left_interior (u : R) (i : Fin 5) :
    elevenSection u (Pi.single (Fin.castAdd 6 i) 1) ∈ interiorInClosed u := by
  rw [elevenSection_single]
  exact elevenClosedElement_left_interior u i

theorem elevenSection_interior_of_boundary_zero (u : R) (c : Fin 11 → R)
    (hc : ∀ j : Fin 6, c (Fin.natAdd 5 j) = 0) :
    elevenSection u c ∈ interiorInClosed u := by
  change ((elevenSection u c : FClosed u) : ActualRing u) ∈ FInterior u
  rw [elevenSection_apply_blocks]
  simp only [hc, zero_smul, Finset.sum_const_zero, add_zero,
    Submodule.coe_sum, Submodule.coe_smul]
  exact (FInterior u).sum_mem (fun i _ => (FInterior u).smul_mem _
    (factorialPole_mem_interior u i.val))

section Domain

variable [IsDomain R]

theorem vertexQuotientMap_gamma_zero (u : R) (hu : IsUnit u) (i : Fin 5) :
    vertexQuotientMap u hu (gammaQuotientFamily u i) = 0 :=
  vertexCoordinateMap_interior_zero u hu _ (factorialPole_mem_interior u i.val)

theorem vertexQuotientMap_boundary_combination (u : R) (hu : IsUnit u)
    (c : Fin 6 → R) (v : Fin 6) :
    vertexQuotientMap u hu
      (∑ j : Fin 6, c j • (exactSubmodule u).mkQ (vertexBoundaryElement u j)) v =
        -(↑hu.unit⁻¹ : R) * c v := by
  classical
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    vertexQuotientMap_mkQ, vertexCoordinateMap_boundaryElement, smul_eq_mul]
  rw [Finset.sum_eq_single v]
  · simp only [ite_true, mul_one]
    ring
  · intro j _ hj
    rw [if_neg hj, mul_zero, mul_zero]
  · simp

variable (K : Type*) [Field K] [CharZero K]
variable (σ : R →+* LaurentSeries K) (u v d : R)
variable (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1)
variable (hu : σ u = uSeries K) (hσ : Function.Injective σ)

include huv hu hσ in
/-- The actual six vertex coordinates first force all boundary coefficients
to vanish; the actual Mellin determinant then forces the five pole coefficients. -/
theorem elevenQuotientFamily_independent : LinearIndependent R (elevenQuotientFamily u) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c h i
  rw [Fin.sum_univ_add (a := 5) (b := 6)] at h
  simp only [elevenQuotientFamily_left, elevenQuotientFamily_right] at h
  let hu' := uUnitOfInverse u v huv
  have hGamma : vertexQuotientMap u hu'
      (∑ j : Fin 5, c (Fin.castAdd 6 j) • gammaQuotientFamily u j) = 0 := by
    simp only [map_sum, map_smul, vertexQuotientMap_gamma_zero, smul_zero,
      Finset.sum_const_zero]
  have hboundary : ∀ j : Fin 6, c (Fin.natAdd 5 j) = 0 := by
    intro j
    have hj := congrArg (fun q => vertexQuotientMap u hu' q j) h
    rw [map_add, hGamma, zero_add,
      vertexQuotientMap_boundary_combination, map_zero, Pi.zero_apply] at hj
    exact (mul_eq_zero.mp hj).resolve_left (neg_ne_zero.mpr (Units.ne_zero hu'.unit⁻¹))
  have hpoles : ∑ j : Fin 5, c (Fin.castAdd 6 j) • gammaQuotientFamily u j = 0 := by
    simpa only [hboundary, zero_smul, Finset.sum_const_zero, add_zero] using h
  have hp : ∀ j : Fin 5, c (Fin.castAdd 6 j) = 0 :=
    Fintype.linearIndependent_iff.mp (gammaQuotientFamily_independent K σ u hu hσ) _ hpoles
  exact Fin.addCases (m := 5) (n := 6) (motive := fun j : Fin 11 => c j = 0)
    hp hboundary i

include huv hu hσ in
theorem elevenQuotientSection_injective : Function.Injective (elevenQuotientSection u) := by
  intro a c h
  apply (elevenQuotientFamily_independent K σ u v huv hu hσ).fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply, ← elevenQuotientSection_apply] using h

/- The finite-generation argument below uses no domain hypothesis. -/
omit [IsDomain R] in
include huv hd in
/-- The proved finite-generation theorem is converted through the literal
ambient exact image to surjectivity on the actual closed quotient. -/
theorem elevenQuotientSection_surjective : Function.Surjective (elevenQuotientSection u) := by
  classical
  intro q
  obtain ⟨g, rfl⟩ := (exactSubmodule u).mkQ_surjective q
  obtain ⟨e, he, z, hz, hg⟩ := Submodule.mem_sup.mp
    (FClosed_finite_generation u v d huv hd g.property)
  change e ∈ (exactSubmodule u).map (FClosed u).subtype at he
  obtain ⟨n, hn, hne⟩ := he
  change (n : ActualRing u) = e at hne
  change z ∈ finitePoleSpan u ⊔ Submodule.span R (Set.range (b u)) at hz
  obtain ⟨p, hp, b', hb, hpb⟩ := Submodule.mem_sup.mp hz
  change p ∈ Submodule.span R (Set.range (fun i : Fin 5 => factorialPole u i.val)) at hp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hb
  have hrep : g = n + elevenSection u (Fin.append a c) := by
    apply Subtype.ext
    change (g : ActualRing u) = (n : ActualRing u) + _
    rw [hne, elevenSection_append_val, ha, hc, hpb]
    exact hg.symm
  refine ⟨Fin.append a c, ?_⟩
  change (exactSubmodule u).mkQ (elevenSection u (Fin.append a c)) = (exactSubmodule u).mkQ g
  have hn0 : (exactSubmodule u).mkQ n = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).mpr hn
  rw [hrep, map_add, hn0, zero_add]

/-- The eleven actual quotient classes are a proved coordinate equivalence. -/
def quotientEquiv : (Fin 11 → R) ≃ₗ[R] ClosedResidueQuotient u :=
  LinearEquiv.ofBijective (elevenQuotientSection u)
    ⟨elevenQuotientSection_injective K σ u v huv hu hσ,
      elevenQuotientSection_surjective u v d huv hd⟩

def quotientBasis : Module.Basis (Fin 11) R (ClosedResidueQuotient u) :=
  (Pi.basisFun R (Fin 11)).map (quotientEquiv K σ u v d huv hd hu hσ)

theorem quotientBasis_eq_family (i : Fin 11) :
    quotientBasis K σ u v d huv hd hu hσ i = elevenQuotientFamily u i := by
  rw [quotientBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change (exactSubmodule u).mkQ (elevenSection u (Pi.single i 1)) = _
  rw [elevenSection_single]
  rfl

def coordinates : FClosed u →ₗ[R] (Fin 11 → R) :=
  (quotientEquiv K σ u v d huv hd hu hσ).symm.toLinearMap.comp (exactSubmodule u).mkQ

theorem coordinates_section (c : Fin 11 → R) :
    coordinates K σ u v d huv hd hu hσ (elevenSection u c) = c := by
  change (quotientEquiv K σ u v d huv hd hu hσ).symm
    (quotientEquiv K σ u v d huv hd hu hσ c) = c
  exact LinearEquiv.symm_apply_apply _ _

theorem coordinates_gammaClosedElement (i : Fin 5) :
    coordinates K σ u v d huv hd hu hσ (gammaClosedElement u i) =
      Pi.single (Fin.castAdd 6 i) 1 := by
  simpa only [elevenSection_single, elevenClosedElement_left] using
    coordinates_section K σ u v d huv hd hu hσ (Pi.single (Fin.castAdd 6 i) 1)

theorem coordinates_vertexBoundaryElement (j : Fin 6) :
    coordinates K σ u v d huv hd hu hσ (vertexBoundaryElement u j) =
      Pi.single (Fin.natAdd 5 j) 1 := by
  simpa only [elevenSection_single, elevenClosedElement_right] using
    coordinates_section K σ u v d huv hd hu hσ (Pi.single (Fin.natAdd 5 j) 1)

theorem coordinates_ker : (coordinates K σ u v d huv hd hu hσ).ker = exactSubmodule u := by
  ext g
  change coordinates K σ u v d huv hd hu hσ g = 0 ↔ g ∈ exactSubmodule u
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).mp
    have he := congrArg (quotientEquiv K σ u v d huv hd hu hσ) h
    change (quotientEquiv K σ u v d huv hd hu hσ)
      ((quotientEquiv K σ u v d huv hd hu hσ).symm ((exactSubmodule u).mkQ g)) =
        (quotientEquiv K σ u v d huv hd hu hσ) 0 at he
    rw [LinearEquiv.apply_symm_apply, map_zero] at he
    simpa only [Submodule.mkQ_apply] using he
  · intro h
    change (quotientEquiv K σ u v d huv hd hu hσ).symm ((exactSubmodule u).mkQ g) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).mpr h, map_zero]

theorem coordinates_exact (n : exactSubmodule u) :
    coordinates K σ u v d huv hd hu hσ (n : FClosed u) = 0 := by
  have hn : (n : FClosed u) ∈ (coordinates K σ u v d huv hd hu hσ).ker := by
    rw [coordinates_ker]
    exact n.property
  exact hn

theorem residual_mem_exact (g : FClosed u) :
    g - elevenSection u (coordinates K σ u v d huv hd hu hσ g) ∈ exactSubmodule u := by
  rw [← coordinates_ker K σ u v d huv hd hu hσ]
  change coordinates K σ u v d huv hd hu hσ
    (g - elevenSection u (coordinates K σ u v d huv hd hu hσ g)) = 0
  rw [map_sub, coordinates_section, sub_self]

def exactProjection : FClosed u →ₗ[R] exactSubmodule u :=
  (LinearMap.id - (elevenSection u).comp (coordinates K σ u v d huv hd hu hσ)).codRestrict
    (exactSubmodule u) (residual_mem_exact K σ u v d huv hd hu hσ)

/-- The actual closed module splits into its actual exact submodule and
the displayed eleven free coordinates. -/
def splitEquiv : FClosed u ≃ₗ[R] ((exactSubmodule u) × (Fin 11 → R)) where
  toLinearMap := (exactProjection K σ u v d huv hd hu hσ).prod
    (coordinates K σ u v d huv hd hu hσ)
  invFun x := (x.1 : FClosed u) + elevenSection u x.2
  left_inv g := by
    change (g - elevenSection u (coordinates K σ u v d huv hd hu hσ g)) +
      elevenSection u (coordinates K σ u v d huv hd hu hσ g) = g
    exact sub_add_cancel _ _
  right_inv x := by
    rcases x with ⟨n, c⟩
    apply Prod.ext
    · apply Subtype.ext
      change ((n : FClosed u) + elevenSection u c) -
        elevenSection u (coordinates K σ u v d huv hd hu hσ
          ((n : FClosed u) + elevenSection u c)) = (n : FClosed u)
      rw [map_add, coordinates_exact, coordinates_section, zero_add, add_sub_cancel_right]
    · change coordinates K σ u v d huv hd hu hσ ((n : FClosed u) + elevenSection u c) = c
      rw [map_add, coordinates_exact, coordinates_section, zero_add]

theorem splitEquiv_symm_exact (n : exactSubmodule u) :
    (splitEquiv K σ u v d huv hd hu hσ).symm (n, 0) = (n : FClosed u) := by
  change (n : FClosed u) + elevenSection u 0 = (n : FClosed u)
  rw [map_zero, add_zero]

theorem splitEquiv_symm_section (c : Fin 11 → R) :
    (splitEquiv K σ u v d huv hd hu hσ).symm (0, c) = elevenSection u c := by
  change (0 : FClosed u) + elevenSection u c = elevenSection u c
  exact zero_add _

theorem splitEquiv_apply_exact (n : exactSubmodule u) :
    splitEquiv K σ u v d huv hd hu hσ (n : FClosed u) = (n, 0) := by
  rw [← splitEquiv_symm_exact K σ u v d huv hd hu hσ n, LinearEquiv.apply_symm_apply]

theorem splitEquiv_apply_section (c : Fin 11 → R) :
    splitEquiv K σ u v d huv hd hu hσ (elevenSection u c) = (0, c) := by
  rw [← splitEquiv_symm_section K σ u v d huv hd hu hσ c, LinearEquiv.apply_symm_apply]

theorem vertexCoordinateMap_section (c : Fin 11 → R) (j : Fin 6) :
    vertexCoordinateMap u (uUnitOfInverse u v huv) (elevenSection u c) j =
      -(↑(uUnitOfInverse u v huv).unit⁻¹ : R) * c (Fin.natAdd 5 j) := by
  change vertexQuotientMap u (uUnitOfInverse u v huv) (elevenQuotientSection u c) j = _
  rw [elevenQuotientSection_apply, Fin.sum_univ_add (a := 5) (b := 6)]
  simp only [elevenQuotientFamily_left, elevenQuotientFamily_right]
  have hGamma : vertexQuotientMap u (uUnitOfInverse u v huv)
      (∑ i : Fin 5, c (Fin.castAdd 6 i) • gammaQuotientFamily u i) = 0 := by
    simp only [map_sum, map_smul, vertexQuotientMap_gamma_zero, smul_zero,
      Finset.sum_const_zero]
  rw [map_add, hGamma, zero_add]
  exact vertexQuotientMap_boundary_combination u (uUnitOfInverse u v huv) _ j

theorem interior_coordinates_boundary_zero (g : FClosed u) (hg : g ∈ interiorInClosed u)
    (j : Fin 6) : coordinates K σ u v d huv hd hu hσ g (Fin.natAdd 5 j) = 0 := by
  let hu' := uUnitOfInverse u v huv
  have hz : vertexCoordinateMap u hu' g = 0 :=
    vertexCoordinateMap_interior_zero u hu' g hg
  have he := exactSubmodule_le_vertexCoordinateMap_ker u hu'
    (residual_mem_exact K σ u v d huv hd hu hσ g)
  change vertexCoordinateMap u hu'
    (g - elevenSection u (coordinates K σ u v d huv hd hu hσ g)) = 0 at he
  rw [map_sub, hz, zero_sub] at he
  have hs := congrFun (neg_eq_zero.mp he) j
  rw [vertexCoordinateMap_section u v huv
    (coordinates K σ u v d huv hd hu hσ g) j, Pi.zero_apply] at hs
  exact (mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr (Units.ne_zero hu'.unit⁻¹))

/-- The exact interior image is the first five free coordinates, including
surjectivity on every such coordinate vector. -/
theorem interior_coordinates_image :
    (interiorInClosed u).map (coordinates K σ u v d huv hd hu hσ) = interiorCoordinates R := by
  ext c
  constructor
  · rintro ⟨g, hg, rfl⟩
    change ∀ j : Fin 6, coordinates K σ u v d huv hd hu hσ g (Fin.natAdd 5 j) = 0
    exact interior_coordinates_boundary_zero K σ u v d huv hd hu hσ g hg
  · intro hc
    change (∀ j : Fin 6, c (Fin.natAdd 5 j) = 0) at hc
    refine ⟨elevenSection u c, elevenSection_interior_of_boundary_zero u c hc, ?_⟩
    exact coordinates_section K σ u v d huv hd hu hσ c

end Domain

section ParameterField

variable (K : Type*) [Field K] [CharZero K]

theorem parameterSixUUnit : IsUnit (6 * (Parameter.u : Parameter.ParameterRing K)) := by
  simpa only [map_ofNat] using
    ((isUnit_iff_ne_zero.mpr (by norm_num : (6 : K) ≠ 0)).map
      (algebraMap K (Parameter.ParameterRing K))).mul Parameter.u_isUnit

def parameterSixInverse : Parameter.ParameterRing K := ↑(parameterSixUUnit K).unit⁻¹

theorem parameterSixInverse_mul :
    parameterSixInverse K * (6 * (Parameter.u : Parameter.ParameterRing K)) = 1 :=
  (parameterSixUUnit K).val_inv_mul

omit [CharZero K] in
theorem parameterDiscriminantInverse_mul :
    (Parameter.discriminantInverse : Parameter.ParameterRing K) *
      (1 - (6 * Parameter.u) ^ 6) = 1 := by
  change (Parameter.discriminantInverse : Parameter.ParameterRing K) * Parameter.discriminant = 1
  rw [mul_comm]
  exact Parameter.discriminant_mul_inverse

def parameterQuotientEquiv :
    (Fin 11 → Parameter.ParameterRing K) ≃ₗ[Parameter.ParameterRing K]
      ClosedResidueQuotient (Parameter.u : Parameter.ParameterRing K) :=
  quotientEquiv K (parameterSeriesMap K) Parameter.u (parameterSixInverse K)
    Parameter.discriminantInverse (parameterSixInverse_mul K) (parameterDiscriminantInverse_mul K)
    (parameterSeriesMap_u K) (parameterSeriesMap_injective K)

def parameterCoordinates :
    FClosed (Parameter.u : Parameter.ParameterRing K) →ₗ[Parameter.ParameterRing K]
      (Fin 11 → Parameter.ParameterRing K) :=
  coordinates K (parameterSeriesMap K) Parameter.u (parameterSixInverse K)
    Parameter.discriminantInverse (parameterSixInverse_mul K) (parameterDiscriminantInverse_mul K)
    (parameterSeriesMap_u K) (parameterSeriesMap_injective K)

def parameterSplitEquiv :
    FClosed (Parameter.u : Parameter.ParameterRing K) ≃ₗ[Parameter.ParameterRing K]
      ((exactSubmodule (Parameter.u : Parameter.ParameterRing K)) ×
        (Fin 11 → Parameter.ParameterRing K)) :=
  splitEquiv K (parameterSeriesMap K) Parameter.u (parameterSixInverse K)
    Parameter.discriminantInverse (parameterSixInverse_mul K) (parameterDiscriminantInverse_mul K)
    (parameterSeriesMap_u K) (parameterSeriesMap_injective K)

end ParameterField

section IntegralParameter

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

include hp in
theorem integralSixUUnit : IsUnit (6 * (Parameter.u : Parameter.ParameterRing ℤ_[p])) :=
  (Parameter.integralParameter_six_unit p hp).mul Parameter.u_isUnit

def integralSixInverse : Parameter.ParameterRing ℤ_[p] := ↑(integralSixUUnit p hp).unit⁻¹

theorem integralSixInverse_mul :
    integralSixInverse p hp * (6 * (Parameter.u : Parameter.ParameterRing ℤ_[p])) = 1 :=
  (integralSixUUnit p hp).val_inv_mul

theorem integralDiscriminantInverse_mul :
    (Parameter.discriminantInverse : Parameter.ParameterRing ℤ_[p]) *
      (1 - (6 * Parameter.u) ^ 6) = 1 := by
  change (Parameter.discriminantInverse : Parameter.ParameterRing ℤ_[p]) * Parameter.discriminant = 1
  rw [mul_comm]
  exact Parameter.discriminant_mul_inverse

def integralQuotientEquiv :
    (Fin 11 → Parameter.ParameterRing ℤ_[p]) ≃ₗ[Parameter.ParameterRing ℤ_[p]]
      ClosedResidueQuotient (Parameter.u : Parameter.ParameterRing ℤ_[p]) :=
  quotientEquiv ℚ_[p] (integralParameterSeriesMap p) Parameter.u (integralSixInverse p hp)
    Parameter.discriminantInverse (integralSixInverse_mul p hp) (integralDiscriminantInverse_mul p)
    (integralParameterSeriesMap_u p) (integralParameterSeriesMap_injective p)

def integralCoordinates :
    FClosed (Parameter.u : Parameter.ParameterRing ℤ_[p]) →ₗ[Parameter.ParameterRing ℤ_[p]]
      (Fin 11 → Parameter.ParameterRing ℤ_[p]) :=
  coordinates ℚ_[p] (integralParameterSeriesMap p) Parameter.u (integralSixInverse p hp)
    Parameter.discriminantInverse (integralSixInverse_mul p hp) (integralDiscriminantInverse_mul p)
    (integralParameterSeriesMap_u p) (integralParameterSeriesMap_injective p)

def integralSplitEquiv :
    FClosed (Parameter.u : Parameter.ParameterRing ℤ_[p]) ≃ₗ[Parameter.ParameterRing ℤ_[p]]
      ((exactSubmodule (Parameter.u : Parameter.ParameterRing ℤ_[p])) ×
        (Fin 11 → Parameter.ParameterRing ℤ_[p])) :=
  splitEquiv ℚ_[p] (integralParameterSeriesMap p) Parameter.u (integralSixInverse p hp)
    Parameter.discriminantInverse (integralSixInverse_mul p hp) (integralDiscriminantInverse_mul p)
    (integralParameterSeriesMap_u p) (integralParameterSeriesMap_injective p)

end IntegralParameter

end WPResidueQuotient.Actual
