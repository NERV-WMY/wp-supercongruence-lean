import WPResidueQuotient.SplitCompletion
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.StdBasis
import WPResidueQuotient.ActualSplit
import WPResidueQuotient.ConnectionReduction
import WPResidueQuotient.ConstantSplit
import WPResidueQuotient.PadicScalarCompletion

/-!
The completion endpoint is instantiated on the actual factorial closed
module and its actual logarithmic derivative images.  The finite-coordinate
image lemma below preserves an actual split image before completion and
will be applied to the interior coordinates.
-/

namespace WPResidueQuotient.Adic

noncomputable section

variable {R M N K : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup K] [Module R K] [Module.Projective R K]

/-- If an actual image is a split projective submodule, completing its
source preserves that exact image.  This is stronger than closure equality. -/
theorem completed_range_of_split_image (p : R) (f : M →ₗ[R] N)
    (g : K →ₗ[R] N) (l : N →ₗ[R] K) (hl : l.comp g = LinearMap.id)
    (hr : LinearMap.range f = LinearMap.range g) :
    LinearMap.range (completeMap p f) = LinearMap.range (completeMap p g) := by
  let g' : K →ₗ[R] LinearMap.range f := g.codRestrict (LinearMap.range f)
    (fun k => hr.symm ▸ LinearMap.mem_range_self g k)
  have hsurj : Function.Surjective f.rangeRestrict := by
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict g' hsurj
  have hfs : f.comp s = g := by
    apply LinearMap.ext
    intro k
    exact congrArg Subtype.val (DFunLike.congr_fun hs k)
  have hfac : g.comp (l.comp f) = f := by
    apply LinearMap.ext
    intro x
    have hx : f x ∈ LinearMap.range g := hr ▸ LinearMap.mem_range_self f x
    rcases hx with ⟨k, hk⟩
    change g (l (f x)) = f x
    rw [← hk]
    have hlk := DFunLike.congr_fun hl k
    change l (g k) = k at hlk
    rw [hlk]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨completeMap p (l.comp f) y, ?_⟩
    rw [← completeMap_comp, hfac]
  · rintro ⟨y, rfl⟩
    refine ⟨completeMap p s y, ?_⟩
    rw [← completeMap_comp, hfs]

end
end WPResidueQuotient.Adic

namespace WPResidueQuotient.ActualCompletion

noncomputable section
open scoped LaurentSeries

set_option maxHeartbeats 2000000

section InteriorCoordinates

variable {R : Type*} [CommRing R]

def actualInteriorInclusion (u : R) : FInterior u →ₗ[R] FClosed u :=
  Submodule.inclusion (FInterior_le_FClosed u)

theorem actualInteriorInclusion_range (u : R) :
    LinearMap.range (actualInteriorInclusion u) = Actual.interiorInClosed u := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact i.property
  · intro hg
    change (g : ActualRing u) ∈ FInterior u at hg
    exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

def moduleInteriorInclusion : (Fin 5 → R) →ₗ[R] (Fin 11 → R) :=
  Adic.moduleExactInclusion Adic.elevenSplit

def moduleInteriorProjection : (Fin 11 → R) →ₗ[R] (Fin 5 → R) :=
  (LinearMap.fst R (Fin 5 → R) (Fin 6 → R)).comp Adic.elevenSplit.toLinearMap

theorem moduleInteriorProjection_leftInverse :
    (moduleInteriorProjection (R := R)).comp moduleInteriorInclusion = LinearMap.id := by
  ext c i
  simp [moduleInteriorProjection, moduleInteriorInclusion, Adic.moduleExactInclusion]

theorem moduleInteriorInclusion_range :
    LinearMap.range (moduleInteriorInclusion (R := R)) = Actual.interiorCoordinates R := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩ j
    change (if h : 5 + j.val < 5 then a ⟨5 + j.val, h⟩ else 0) = 0
    rw [dif_neg (by omega)]
  · intro hc
    refine ⟨fun j : Fin 5 => c (Fin.castAdd 6 j), ?_⟩
    funext i
    refine Fin.addCases (m := 5) (n := 6) (fun j => ?_) (fun j => ?_) i
    · change (if h : j.val < 5 then c (Fin.castAdd 6 ⟨j.val, h⟩) else 0) = c (Fin.castAdd 6 j)
      rw [dif_pos j.isLt]
    · change (if h : 5 + j.val < 5 then c (Fin.castAdd 6 ⟨5 + j.val, h⟩) else 0) =
        c (Fin.natAdd 5 j)
      rw [dif_neg (by omega)]
      exact (hc j).symm

def interiorCoordinatesEquiv : Actual.interiorCoordinates R ≃ₗ[R] (Fin 5 → R) where
  toLinearMap := moduleInteriorProjection.comp (Actual.interiorCoordinates R).subtype
  invFun c := ⟨moduleInteriorInclusion c,
    moduleInteriorInclusion_range (R := R) ▸ LinearMap.mem_range_self moduleInteriorInclusion c⟩
  left_inv c := by
    apply Subtype.ext
    have hc : (c : Fin 11 → R) ∈ LinearMap.range moduleInteriorInclusion :=
      (moduleInteriorInclusion_range (R := R)).symm ▸ c.property
    rcases hc with ⟨a, ha⟩
    change moduleInteriorInclusion (moduleInteriorProjection (c : Fin 11 → R)) =
      (c : Fin 11 → R)
    rw [← ha]
    have hl := DFunLike.congr_fun (moduleInteriorProjection_leftInverse (R := R)) a
    change moduleInteriorProjection (moduleInteriorInclusion a) = a at hl
    rw [hl]
  right_inv c := DFunLike.congr_fun (moduleInteriorProjection_leftInverse (R := R)) c

def completedInteriorInclusion (u q : R) :
    Adic.Completion q (FInterior u) →ₗ[R] Adic.Completion q (FClosed u) :=
  Adic.completeMap q (actualInteriorInclusion u)

end InteriorCoordinates

section Actual

variable {R : Type*} [CommRing R] [IsDomain R]
variable (K : Type*) [Field K] [CharZero K]
variable (σ : R →+* LaurentSeries K) (u v d : R)
variable (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1)
variable (hu : σ u = MellinFactors.uSeries K) (hσ : Function.Injective σ)

local notation "eActual" => Actual.splitEquiv K σ u v d huv hd hu hσ

def completedLinearCoordinates (q : R) :
    Adic.Completion q (FClosed u) →ₗ[R] Adic.Completion q (Fin 11 → R) :=
  Adic.coordinates (M := FClosed u) (N := exactSubmodule u) (K := Fin 11 → R) q eActual

def completedCoordinates (q : R) :
    Adic.Completion q (FClosed u) →ₗ[R] (Fin 11 → Adic.Completion q R) :=
  Adic.scalarCoordinates (M := FClosed u) (N := exactSubmodule u) q eActual

def completedSection (q : R) :
    (Fin 11 → Adic.Completion q R) →ₗ[R] Adic.Completion q (FClosed u) :=
  Adic.scalarCoordinateSection (M := FClosed u) (N := exactSubmodule u) q eActual

def completedExactInclusion (q : R) :
    Adic.Completion q (exactSubmodule u) →ₗ[R] Adic.Completion q (FClosed u) :=
  Adic.completeMap q (exactSubmodule u).subtype

theorem actual_exact_inclusion :
    Adic.moduleExactInclusion (M := FClosed u) (N := exactSubmodule u) (K := Fin 11 → R) eActual = (exactSubmodule u).subtype := by
  apply LinearMap.ext
  intro n
  exact Actual.splitEquiv_symm_exact K σ u v d huv hd hu hσ n

theorem completedExactInclusion_eq (q : R) :
    completedExactInclusion u q = Adic.exactInclusion (M := FClosed u) (N := exactSubmodule u) (K := Fin 11 → R) q eActual := by
  rw [Adic.exactInclusion_eq_completeMap, actual_exact_inclusion K σ u v d huv hd hu hσ]
  rfl

theorem completedLinearCoordinates_eq_map (q : R) :
    completedLinearCoordinates K σ u v d huv hd hu hσ q =
      Adic.completeMap q (Actual.coordinates K σ u v d huv hd hu hσ) := by
  apply LinearMap.ext
  intro x
  change Adic.completeMap (M := (exactSubmodule u) × (Fin 11 → R)) (N := Fin 11 → R) q
    (LinearMap.snd R (exactSubmodule u) (Fin 11 → R))
    (Adic.completeMap (M := FClosed u) (N := (exactSubmodule u) × (Fin 11 → R)) q (eActual).toLinearMap x) = _
  rw [← Adic.completeMap_comp]
  rfl

attribute [local irreducible] Actual.splitEquiv Actual.quotientEquiv
attribute [local irreducible] FClosed FInterior exactSubmodule

@[simp] theorem completedCoordinates_ofModule (q : R) (g : FClosed u) :
    completedCoordinates K σ u v d huv hd hu hσ q (Adic.ofModule q g) =
      fun i => Adic.ofModule q (Actual.coordinates K σ u v d huv hd hu hσ g i) := by
  funext i
  change Adic.completeMap q (LinearMap.proj i : (Fin 11 → R) →ₗ[R] R)
    (completedLinearCoordinates K σ u v d huv hd hu hσ q (Adic.ofModule q g)) = _
  rw [completedLinearCoordinates_eq_map, Adic.completeMap_ofModule, Adic.completeMap_ofModule]
  rfl

theorem completedCoordinates_gamma (q : R) (j : Fin 5) :
    completedCoordinates K σ u v d huv hd hu hσ q
        (Adic.ofModule q (Actual.gammaClosedElement u j)) =
      fun i => Adic.ofModule q ((Pi.single (Fin.castAdd 6 j) (1 : R) : Fin 11 → R) i) := by
  rw [completedCoordinates_ofModule, Actual.coordinates_gammaClosedElement]

theorem completedCoordinates_boundary (q : R) (j : Fin 6) :
    completedCoordinates K σ u v d huv hd hu hσ q
        (Adic.ofModule q (vertexBoundaryElement u j)) =
      fun i => Adic.ofModule q ((Pi.single (Fin.natAdd 5 j) (1 : R) : Fin 11 → R) i) := by
  rw [completedCoordinates_ofModule, Actual.coordinates_vertexBoundaryElement]

theorem completedInterior_linear_image (q : R) :
    LinearMap.range ((completedLinearCoordinates K σ u v d huv hd hu hσ q).comp
      (completedInteriorInclusion u q)) = LinearMap.range (Adic.interiorCoordinateInclusion q) := by
  rw [completedLinearCoordinates_eq_map]
  change LinearMap.range ((Adic.completeMap q (Actual.coordinates K σ u v d huv hd hu hσ)).comp
    (Adic.completeMap q (actualInteriorInclusion u))) =
      LinearMap.range (Adic.exactInclusion q (Adic.elevenSplit (R := R)))
  have hcomp : Adic.completeMap q
      ((Actual.coordinates K σ u v d huv hd hu hσ).comp (actualInteriorInclusion u)) =
        (Adic.completeMap q (Actual.coordinates K σ u v d huv hd hu hσ)).comp
          (Adic.completeMap q (actualInteriorInclusion u)) := by
    apply LinearMap.ext
    intro x
    exact Adic.completeMap_comp q (actualInteriorInclusion u)
      (Actual.coordinates K σ u v d huv hd hu hσ) x
  rw [← hcomp, Adic.exactInclusion_eq_completeMap]
  apply Adic.completed_range_of_split_image (M := FInterior u)
    (N := Fin 11 → R) (K := Fin 5 → R)
    (g := moduleInteriorInclusion) (l := moduleInteriorProjection)
  · exact moduleInteriorProjection_leftInverse
  · rw [LinearMap.range_comp, actualInteriorInclusion_range,
      Actual.interior_coordinates_image K σ u v d huv hd hu hσ,
      moduleInteriorInclusion_range]

/-- The image of the completed actual interior module is exactly the
completed five-coordinate summand, in the literal eleven scalar coordinates. -/
theorem completedInterior_scalar_image (q : R) :
    (LinearMap.range (completedInteriorInclusion u q)).map
        (completedCoordinates K σ u v d huv hd hu hσ q) =
      (LinearMap.range (Adic.interiorCoordinateInclusion q)).map
        (Adic.completePiEquiv q).toLinearMap := by
  rw [← LinearMap.range_comp]
  change LinearMap.range (((Adic.completePiEquiv q).toLinearMap.comp
    (completedLinearCoordinates K σ u v d huv hd hu hσ q)).comp
      (completedInteriorInclusion u q)) = _
  rw [LinearMap.comp_assoc, LinearMap.range_comp, completedInterior_linear_image]

@[simp] theorem completedCoordinates_section (q : R) (x : Fin 11 → Adic.Completion q R) :
    completedCoordinates K σ u v d huv hd hu hσ q
      (completedSection K σ u v d huv hd hu hσ q x) = x := by
  unfold completedCoordinates completedSection
  exact @Adic.scalarCoordinates_section (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual x

theorem completedCoordinates_kernel (q : R) :
    LinearMap.ker (completedCoordinates K σ u v d huv hd hu hσ q) =
      LinearMap.range (completedExactInclusion u q) := by
  rw [completedExactInclusion_eq K σ u v d huv hd hu hσ]
  unfold completedCoordinates
  exact @Adic.scalarCoordinates_kernel (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual

include huv hd hu hσ in
theorem completedExactInclusion_injective (q : R) :
    Function.Injective (completedExactInclusion u q) := by
  rw [completedExactInclusion_eq K σ u v d huv hd hu hσ]
  exact @Adic.exactInclusion_injective (R) inferInstance (FClosed u) (exactSubmodule u) (Fin 11 → R)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module
    (inferInstance : AddCommGroup (Fin 11 → R)) (inferInstance : Module R (Fin 11 → R)) q eActual

include huv hd hu hσ in
theorem completedExact_isClosed (q : R) :
    IsClosed (Set.range (completedExactInclusion u q)) := by
  rw [completedExactInclusion_eq K σ u v d huv hd hu hσ]
  exact @Adic.isClosed_range_exactInclusion (R) inferInstance (FClosed u) (exactSubmodule u) (Fin 11 → R)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module
    (inferInstance : AddCommGroup (Fin 11 → R)) (inferInstance : Module R (Fin 11 → R)) q eActual

include huv hd hu hσ in
theorem actual_exact_closure (q : R) :
    closure (Set.range ((Adic.ofModule q).comp (exactSubmodule u).subtype)) =
      Set.range (completedExactInclusion u q) := by
  rw [completedExactInclusion_eq K σ u v d huv hd hu hσ,
    ← actual_exact_inclusion K σ u v d huv hd hu hσ]
  exact @Adic.closure_actual_exact (R) inferInstance (FClosed u) (exactSubmodule u) (Fin 11 → R)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module
    (inferInstance : AddCommGroup (Fin 11 → R)) (inferInstance : Module R (Fin 11 → R)) q eActual

include huv hd hu hσ in
theorem completed_derivative_closure (q : R) :
    closure (Set.range (Adic.completeMap q (exactAggregate u))) =
      Set.range (completedExactInclusion u q) := by
  rw [completedExactInclusion_eq K σ u v d huv hd hu hσ]
  apply @Adic.closure_completedMap_of_range_eq (R) inferInstance (FClosed u) (exactSubmodule u) (Fin 11 → R)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module
    (inferInstance : AddCommGroup (Fin 11 → R)) (inferInstance : Module R (Fin 11 → R))
    (Fin 5 → FClosed u) (inferInstance : AddCommGroup (Fin 5 → FClosed u))
    (inferInstance : Module R (Fin 5 → FClosed u)) q eActual (exactAggregate u)
  rw [actual_exact_inclusion K σ u v d huv hd hu hσ, exactAggregate_range,
    Submodule.range_subtype]

theorem continuous_completedCoordinates (q : R) :
    Continuous (completedCoordinates K σ u v d huv hd hu hσ q) := by
  unfold completedCoordinates
  exact @Adic.continuous_scalarCoordinates (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual

theorem continuous_completedSection (q : R) :
    Continuous (completedSection K σ u v d huv hd hu hσ q) := by
  unfold completedSection
  exact @Adic.continuous_scalarCoordinateSection (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual

theorem completedCoordinates_isQuotientMap (q : R) :
    Topology.IsQuotientMap (completedCoordinates K σ u v d huv hd hu hσ q) := by
  unfold completedCoordinates
  exact @Adic.isQuotientMap_scalarCoordinates (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual

def completedQuotientEquiv (q : R) :
    (Adic.Completion q (FClosed u) ⧸ LinearMap.range (completedExactInclusion u q))
      ≃ₗ[R] (Fin 11 → Adic.Completion q R) :=
  (Submodule.quotEquivOfEq _ _
    (congrArg LinearMap.range (completedExactInclusion_eq K σ u v d huv hd hu hσ q))).trans
      (@Adic.completedElevenQuotientEquiv (R) inferInstance (FClosed u) (exactSubmodule u)
    (FClosed u).addCommGroup (FClosed u).module
    (exactSubmodule u).addCommGroup (exactSubmodule u).module q eActual)

@[simp] theorem completedQuotientEquiv_mk (q : R) (x : Adic.Completion q (FClosed u)) :
    completedQuotientEquiv K σ u v d huv hd hu hσ q (Submodule.Quotient.mk x) =
      completedCoordinates K σ u v d huv hd hu hσ q x := by
  simp only [completedQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

end Actual

section Padic

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

attribute [local irreducible] Actual.splitEquiv Actual.quotientEquiv
attribute [local irreducible] FClosed FInterior exactSubmodule

abbrev PadicCoeff := Parameter.ParameterRing ℤ_[p]
abbrev padicParameter : PadicCoeff p := Parameter.u

def padicInverseSixParameter : PadicCoeff p :=
  ActualConnection.boundaryScalar ℤ_[p] (Parameter.padic_six_unit p hp)

theorem padicInverseSixParameter_mul :
    padicInverseSixParameter p hp * (6 * padicParameter p) = 1 := by
  rw [mul_comm]
  exact ActualConnection.six_parameter_mul_boundaryScalar ℤ_[p] (Parameter.padic_six_unit p hp)

theorem padicDiscriminantInverse_mul :
    (Parameter.discriminantInverse : PadicCoeff p) * (1 - (6 * padicParameter p) ^ 6) = 1 := by
  rw [mul_comm]
  exact Parameter.discriminant_mul_inverse

def padicSplit : FClosed (padicParameter p) ≃ₗ[PadicCoeff p]
    ((exactSubmodule (padicParameter p)) × (Fin 11 → PadicCoeff p)) :=
  Actual.splitEquiv ℚ_[p] (MellinFactors.integralParameterSeriesMap p)
    (padicParameter p) (padicInverseSixParameter p hp) Parameter.discriminantInverse
    (padicInverseSixParameter_mul p hp) (padicDiscriminantInverse_mul p)
    (MellinFactors.integralParameterSeriesMap_u p)
    (MellinFactors.integralParameterSeriesMap_injective p)

def padicCompletedCoordinates :
    Adic.Completion (p : PadicCoeff p) (FClosed (padicParameter p)) →ₗ[PadicCoeff p]
      (Fin 11 → Adic.Completion (p : PadicCoeff p) (PadicCoeff p)) :=
  Adic.scalarCoordinates (M := FClosed (padicParameter p)) (N := exactSubmodule (padicParameter p)) (p : PadicCoeff p) (padicSplit p hp)

def padicCompletedSection :
    (Fin 11 → Adic.Completion (p : PadicCoeff p) (PadicCoeff p)) →ₗ[PadicCoeff p]
      Adic.Completion (p : PadicCoeff p) (FClosed (padicParameter p)) :=
  Adic.scalarCoordinateSection (M := FClosed (padicParameter p)) (N := exactSubmodule (padicParameter p)) (p : PadicCoeff p) (padicSplit p hp)

def padicCompletedExactInclusion :
    Adic.Completion (p : PadicCoeff p) (exactSubmodule (padicParameter p)) →ₗ[PadicCoeff p]
      Adic.Completion (p : PadicCoeff p) (FClosed (padicParameter p)) :=
  Adic.completeMap (p : PadicCoeff p) (exactSubmodule (padicParameter p)).subtype

theorem padicCompletedCoordinates_kernel :
    LinearMap.ker (padicCompletedCoordinates p hp) =
      LinearMap.range (padicCompletedExactInclusion p) :=
  completedCoordinates_kernel ℚ_[p] (MellinFactors.integralParameterSeriesMap p)
    (padicParameter p) (padicInverseSixParameter p hp) Parameter.discriminantInverse
    (padicInverseSixParameter_mul p hp) (padicDiscriminantInverse_mul p)
    (MellinFactors.integralParameterSeriesMap_u p)
    (MellinFactors.integralParameterSeriesMap_injective p) (p : PadicCoeff p)

theorem padicCompletedCoordinates_section
    (x : Fin 11 → Adic.Completion (p : PadicCoeff p) (PadicCoeff p)) :
    padicCompletedCoordinates p hp (padicCompletedSection p hp x) = x := by
  unfold padicCompletedCoordinates padicCompletedSection
  exact @Adic.scalarCoordinates_section (PadicCoeff p) inferInstance (FClosed (padicParameter p)) (exactSubmodule (padicParameter p))
    (FClosed (padicParameter p)).addCommGroup (FClosed (padicParameter p)).module
    (exactSubmodule (padicParameter p)).addCommGroup (exactSubmodule (padicParameter p)).module
    (p : PadicCoeff p) (padicSplit p hp) x

theorem padicCompletedCoordinates_isQuotientMap :
    Topology.IsQuotientMap (padicCompletedCoordinates p hp) := by
  unfold padicCompletedCoordinates
  exact @Adic.isQuotientMap_scalarCoordinates (PadicCoeff p) inferInstance (FClosed (padicParameter p)) (exactSubmodule (padicParameter p))
    (FClosed (padicParameter p)).addCommGroup (FClosed (padicParameter p)).module
    (exactSubmodule (padicParameter p)).addCommGroup (exactSubmodule (padicParameter p)).module
    (p : PadicCoeff p) (padicSplit p hp)

include hp in
theorem padic_completed_derivative_closure :
    closure (Set.range (Adic.completeMap (p : PadicCoeff p) (exactAggregate (padicParameter p)))) =
      Set.range (padicCompletedExactInclusion p) :=
  completed_derivative_closure ℚ_[p] (MellinFactors.integralParameterSeriesMap p)
    (padicParameter p) (padicInverseSixParameter p hp) Parameter.discriminantInverse
    (padicInverseSixParameter_mul p hp) (padicDiscriminantInverse_mul p)
    (MellinFactors.integralParameterSeriesMap_u p)
    (MellinFactors.integralParameterSeriesMap_injective p) (p : PadicCoeff p)

end Padic

section ConstantPadic

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "uConstant" => Parameter.integralTenth p hp
local notation "eConstant" =>
  ActualSpecialization.integralConstantClosedSplitEquiv p hp hp7 hp19

def constantCompletedLinearCoordinates :
    Adic.Completion (p : ℤ_[p]) (FClosed uConstant) →ₗ[ℤ_[p]]
      Adic.Completion (p : ℤ_[p]) (Fin 11 → ℤ_[p]) :=
  Adic.coordinates (M := FClosed uConstant) (N := exactSubmodule uConstant) (K := Fin 11 → ℤ_[p]) (p : ℤ_[p]) eConstant

def constantCompletedCoordinates :
    Adic.Completion (p : ℤ_[p]) (FClosed uConstant) →ₗ[ℤ_[p]]
      (Fin 11 → Adic.Completion (p : ℤ_[p]) ℤ_[p]) :=
  Adic.scalarCoordinates (M := FClosed uConstant) (N := exactSubmodule uConstant) (p : ℤ_[p]) eConstant

def constantCompletedSection :
    (Fin 11 → Adic.Completion (p : ℤ_[p]) ℤ_[p]) →ₗ[ℤ_[p]]
      Adic.Completion (p : ℤ_[p]) (FClosed uConstant) :=
  Adic.scalarCoordinateSection (M := FClosed uConstant) (N := exactSubmodule uConstant) (p : ℤ_[p]) eConstant

def constantCompletedExactInclusion :
    Adic.Completion (p : ℤ_[p]) (exactSubmodule uConstant) →ₗ[ℤ_[p]]
      Adic.Completion (p : ℤ_[p]) (FClosed uConstant) :=
  Adic.completeMap (p : ℤ_[p]) (exactSubmodule uConstant).subtype

theorem constant_actual_exact_inclusion :
    Adic.moduleExactInclusion (M := FClosed uConstant) (N := exactSubmodule uConstant) (K := Fin 11 → ℤ_[p]) eConstant = (exactSubmodule uConstant).subtype := by
  apply LinearMap.ext
  intro n
  change (eConstant).symm (n, 0) = (n : FClosed uConstant)
  unfold ActualSpecialization.integralConstantClosedSplitEquiv
  rw [ActualSpecialization.closedSplitFromQuotient_symm_apply, map_zero, add_zero]

theorem constantCompletedExactInclusion_eq :
    constantCompletedExactInclusion p hp = Adic.exactInclusion (M := FClosed uConstant) (N := exactSubmodule uConstant) (K := Fin 11 → ℤ_[p]) (p : ℤ_[p]) eConstant := by
  rw [Adic.exactInclusion_eq_completeMap,
    constant_actual_exact_inclusion p hp hp7 hp19]
  rfl

attribute [local irreducible]
  ActualSpecialization.integralConstantClosedSplitEquiv
  ActualSpecialization.integralConstantQuotientEquiv
attribute [local irreducible] FClosed FInterior exactSubmodule

theorem constantCompletedCoordinates_kernel :
    LinearMap.ker (constantCompletedCoordinates p hp hp7 hp19) =
      LinearMap.range (constantCompletedExactInclusion p hp) := by
  rw [constantCompletedExactInclusion_eq p hp hp7 hp19]
  unfold constantCompletedCoordinates
  exact @Adic.scalarCoordinates_kernel (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant

@[simp] theorem constantCompletedCoordinates_section
    (x : Fin 11 → Adic.Completion (p : ℤ_[p]) ℤ_[p]) :
    constantCompletedCoordinates p hp hp7 hp19 (constantCompletedSection p hp hp7 hp19 x) = x := by
  unfold constantCompletedCoordinates constantCompletedSection
  exact @Adic.scalarCoordinates_section (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant x

theorem constantCompletedCoordinates_isQuotientMap :
    Topology.IsQuotientMap (constantCompletedCoordinates p hp hp7 hp19) := by
  unfold constantCompletedCoordinates
  exact @Adic.isQuotientMap_scalarCoordinates (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant

include hp7 hp19 in
theorem constantCompletedExactInclusion_injective :
    Function.Injective (constantCompletedExactInclusion p hp) := by
  rw [constantCompletedExactInclusion_eq p hp hp7 hp19]
  exact @Adic.exactInclusion_injective (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant) (Fin 11 → ℤ_[p])
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module
    (inferInstance : AddCommGroup (Fin 11 → ℤ_[p])) (inferInstance : Module ℤ_[p] (Fin 11 → ℤ_[p])) (p : ℤ_[p]) eConstant

include hp7 hp19 in
theorem constant_exact_closure :
    closure (Set.range ((Adic.ofModule (p : ℤ_[p])).comp (exactSubmodule uConstant).subtype)) =
      Set.range (constantCompletedExactInclusion p hp) := by
  rw [constantCompletedExactInclusion_eq p hp hp7 hp19,
    ← constant_actual_exact_inclusion p hp hp7 hp19]
  exact @Adic.closure_actual_exact (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant) (Fin 11 → ℤ_[p])
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module
    (inferInstance : AddCommGroup (Fin 11 → ℤ_[p])) (inferInstance : Module ℤ_[p] (Fin 11 → ℤ_[p])) (p : ℤ_[p]) eConstant

include hp7 hp19 in
theorem constant_completed_derivative_closure :
    closure (Set.range (Adic.completeMap (p : ℤ_[p]) (exactAggregate uConstant))) =
      Set.range (constantCompletedExactInclusion p hp) := by
  rw [constantCompletedExactInclusion_eq p hp hp7 hp19]
  apply @Adic.closure_completedMap_of_range_eq (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant) (Fin 11 → ℤ_[p])
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module
    (inferInstance : AddCommGroup (Fin 11 → ℤ_[p])) (inferInstance : Module ℤ_[p] (Fin 11 → ℤ_[p]))
    (Fin 5 → FClosed uConstant) (inferInstance : AddCommGroup (Fin 5 → FClosed uConstant))
    (inferInstance : Module ℤ_[p] (Fin 5 → FClosed uConstant)) (p : ℤ_[p]) eConstant (exactAggregate uConstant)
  rw [constant_actual_exact_inclusion p hp hp7 hp19, exactAggregate_range,
    Submodule.range_subtype]

def constantCompletedQuotientEquiv :
    (Adic.Completion (p : ℤ_[p]) (FClosed uConstant) ⧸
        LinearMap.range (constantCompletedExactInclusion p hp)) ≃ₗ[ℤ_[p]]
      (Fin 11 → Adic.Completion (p : ℤ_[p]) ℤ_[p]) :=
  (Submodule.quotEquivOfEq _ _
    (congrArg LinearMap.range (constantCompletedExactInclusion_eq p hp hp7 hp19))).trans
      (@Adic.completedElevenQuotientEquiv (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant)

@[simp] theorem constantCompletedQuotientEquiv_mk
    (x : Adic.Completion (p : ℤ_[p]) (FClosed uConstant)) :
    constantCompletedQuotientEquiv p hp hp7 hp19 (Submodule.Quotient.mk x) =
      constantCompletedCoordinates p hp hp7 hp19 x := by
  simp only [constantCompletedQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

theorem constantCompletedLinearCoordinates_eq_map :
    constantCompletedLinearCoordinates p hp hp7 hp19 =
      Adic.completeMap (p : ℤ_[p])
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19) := by
  apply LinearMap.ext
  intro x
  change Adic.completeMap (M := (exactSubmodule uConstant) × (Fin 11 → ℤ_[p]))
    (N := Fin 11 → ℤ_[p]) (p : ℤ_[p])
    (LinearMap.snd ℤ_[p] (exactSubmodule uConstant) (Fin 11 → ℤ_[p]))
      (Adic.completeMap (M := FClosed uConstant) (N := (exactSubmodule uConstant) × (Fin 11 → ℤ_[p]))
        (p : ℤ_[p]) (eConstant).toLinearMap x) = _
  rw [← Adic.completeMap_comp]
  unfold ActualSpecialization.integralConstantClosedSplitEquiv
  rfl

theorem constantCompletedInterior_linear_image :
    LinearMap.range ((constantCompletedLinearCoordinates p hp hp7 hp19).comp
      (completedInteriorInclusion uConstant (p : ℤ_[p]))) =
        LinearMap.range (Adic.interiorCoordinateInclusion (p : ℤ_[p])) := by
  rw [constantCompletedLinearCoordinates_eq_map]
  have hcomp : Adic.completeMap (p : ℤ_[p])
      ((ActualSpecialization.integralConstantCoordinates p hp hp7 hp19).comp
        (actualInteriorInclusion uConstant)) =
      (Adic.completeMap (p : ℤ_[p])
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19)).comp
          (Adic.completeMap (p : ℤ_[p]) (actualInteriorInclusion uConstant)) := by
    apply LinearMap.ext
    intro x
    exact Adic.completeMap_comp (p : ℤ_[p]) (actualInteriorInclusion uConstant)
      (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19) x
  change LinearMap.range ((Adic.completeMap (p : ℤ_[p])
    (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19)).comp
      (Adic.completeMap (p : ℤ_[p]) (actualInteriorInclusion uConstant))) =
        LinearMap.range (Adic.exactInclusion (p : ℤ_[p]) (Adic.elevenSplit (R := ℤ_[p])))
  rw [← hcomp, Adic.exactInclusion_eq_completeMap]
  apply Adic.completed_range_of_split_image (M := FInterior uConstant)
    (N := Fin 11 → ℤ_[p]) (K := Fin 5 → ℤ_[p])
    (g := moduleInteriorInclusion) (l := moduleInteriorProjection)
  · exact moduleInteriorProjection_leftInverse
  · rw [LinearMap.range_comp, actualInteriorInclusion_range,
      ActualSpecialization.integralConstantCoordinates_interior_image p hp hp7 hp19,
      moduleInteriorInclusion_range]

theorem constantCompletedInterior_scalar_image :
    (LinearMap.range (completedInteriorInclusion uConstant (p : ℤ_[p]))).map
        (constantCompletedCoordinates p hp hp7 hp19) =
      (LinearMap.range (Adic.interiorCoordinateInclusion (p : ℤ_[p]))).map
        (Adic.completePiEquiv (p : ℤ_[p])).toLinearMap := by
  rw [← LinearMap.range_comp]
  change LinearMap.range (((Adic.completePiEquiv (p : ℤ_[p])).toLinearMap.comp
    (constantCompletedLinearCoordinates p hp hp7 hp19)).comp
      (completedInteriorInclusion uConstant (p : ℤ_[p]))) = _
  rw [LinearMap.comp_assoc, LinearMap.range_comp, constantCompletedInterior_linear_image]

/-- Literal numerical coordinates in `Zp^11`, after the independently
proved scalar completion equivalence. -/
def constantCoordinatesZp :
    Adic.Completion (p : ℤ_[p]) (FClosed uConstant) →ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  (PadicScalarCompletion.scalarPiEquiv p (Fin 11)).toLinearMap.comp
    (constantCompletedCoordinates p hp hp7 hp19)

def constantSectionZp :
    (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]] Adic.Completion (p : ℤ_[p]) (FClosed uConstant) :=
  (constantCompletedSection p hp hp7 hp19).comp
    (PadicScalarCompletion.scalarPiEquiv p (Fin 11)).symm.toLinearMap

@[simp] theorem constantCoordinatesZp_ofModule (g : FClosed uConstant) :
    constantCoordinatesZp p hp hp7 hp19 (Adic.ofModule (p : ℤ_[p]) g) =
      ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g := by
  funext i
  change PadicScalarCompletion.scalarEquiv p
    (Adic.completeMap (p : ℤ_[p]) (LinearMap.proj i : (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p])
      (constantCompletedLinearCoordinates p hp hp7 hp19 (Adic.ofModule (p : ℤ_[p]) g))) = _
  rw [constantCompletedLinearCoordinates_eq_map, Adic.completeMap_ofModule,
    Adic.completeMap_ofModule, PadicScalarCompletion.scalarEquiv_ofModule]
  rfl

theorem constantCoordinatesZp_gamma (i : Fin 5) :
    constantCoordinatesZp p hp hp7 hp19
      (Adic.ofModule (p : ℤ_[p]) (Actual.gammaClosedElement uConstant i)) =
        Pi.single (Fin.castAdd 6 i) 1 := by
  rw [constantCoordinatesZp_ofModule, ActualSpecialization.integralConstantCoordinates_gamma]

theorem constantCoordinatesZp_boundary (i : Fin 6) :
    constantCoordinatesZp p hp hp7 hp19
      (Adic.ofModule (p : ℤ_[p]) (vertexBoundaryElement uConstant i)) =
        Pi.single (Fin.natAdd 5 i) 1 := by
  rw [constantCoordinatesZp_ofModule, ActualSpecialization.integralConstantCoordinates_boundary]

@[simp] theorem constantCoordinatesZp_section (x : Fin 11 → ℤ_[p]) :
    constantCoordinatesZp p hp hp7 hp19 (constantSectionZp p hp hp7 hp19 x) = x := by
  change PadicScalarCompletion.scalarPiEquiv p (Fin 11)
    (constantCompletedCoordinates p hp hp7 hp19
      (constantCompletedSection p hp hp7 hp19
        ((PadicScalarCompletion.scalarPiEquiv p (Fin 11)).symm x))) = x
  rw [constantCompletedCoordinates_section]
  exact (PadicScalarCompletion.scalarPiEquiv p (Fin 11)).apply_symm_apply x

theorem constantCoordinatesZp_kernel :
    LinearMap.ker (constantCoordinatesZp p hp hp7 hp19) =
      LinearMap.range (constantCompletedExactInclusion p hp) := by
  rw [← constantCompletedCoordinates_kernel p hp hp7 hp19]
  ext x
  change PadicScalarCompletion.scalarPiEquiv p (Fin 11)
      (constantCompletedCoordinates p hp hp7 hp19 x) = 0 ↔
    constantCompletedCoordinates p hp hp7 hp19 x = 0
  exact (PadicScalarCompletion.scalarPiEquiv p (Fin 11)).map_eq_zero_iff

theorem continuous_constantCoordinatesZp :
    Continuous (constantCoordinatesZp p hp hp7 hp19) := by
  unfold constantCoordinatesZp constantCompletedCoordinates
  exact (PadicScalarCompletion.continuous_scalarPiEquiv p (Fin 11)).comp
    (@Adic.continuous_scalarCoordinates (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant)

theorem continuous_constantSectionZp :
    Continuous (constantSectionZp p hp hp7 hp19) := by
  unfold constantSectionZp constantCompletedSection
  exact (@Adic.continuous_scalarCoordinateSection (ℤ_[p]) inferInstance (FClosed uConstant) (exactSubmodule uConstant)
    (FClosed uConstant).addCommGroup (FClosed uConstant).module
    (exactSubmodule uConstant).addCommGroup (exactSubmodule uConstant).module (p : ℤ_[p]) eConstant).comp
    (PadicScalarCompletion.continuous_scalarPiEquiv_symm p (Fin 11))

theorem constantCoordinatesZp_isQuotientMap :
    Topology.IsQuotientMap (constantCoordinatesZp p hp hp7 hp19) :=
  Topology.IsQuotientMap.of_inverse (continuous_constantSectionZp p hp hp7 hp19)
    (continuous_constantCoordinatesZp p hp hp7 hp19)
    (constantCoordinatesZp_section p hp hp7 hp19)

def constantQuotientZpEquiv :
    (Adic.Completion (p : ℤ_[p]) (FClosed uConstant) ⧸
        LinearMap.range (constantCompletedExactInclusion p hp)) ≃ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  (constantCompletedQuotientEquiv p hp hp7 hp19).trans
    (PadicScalarCompletion.scalarPiEquiv p (Fin 11))

@[simp] theorem constantQuotientZpEquiv_mk
    (x : Adic.Completion (p : ℤ_[p]) (FClosed uConstant)) :
    constantQuotientZpEquiv p hp hp7 hp19 (Submodule.Quotient.mk x) =
      constantCoordinatesZp p hp hp7 hp19 x := by
  simp only [constantQuotientZpEquiv, LinearEquiv.trans_apply, constantCompletedQuotientEquiv_mk]
  rfl

/-- The image of the actual completed interior module is literally `Zp^5`
in the first five positions, with its six boundary coordinates zero. -/
theorem constantInteriorZp_image :
    (LinearMap.range (completedInteriorInclusion uConstant (p : ℤ_[p]))).map
      (constantCoordinatesZp p hp hp7 hp19) = Actual.interiorCoordinates ℤ_[p] := by
  rw [← LinearMap.range_comp]
  change LinearMap.range ((PadicScalarCompletion.finiteScalarEquiv p 11).toLinearMap.comp
    ((constantCompletedLinearCoordinates p hp hp7 hp19).comp
      (completedInteriorInclusion uConstant (p : ℤ_[p])))) = _
  rw [LinearMap.range_comp, constantCompletedInterior_linear_image, ← LinearMap.range_comp]
  have hnat : (PadicScalarCompletion.finiteScalarEquiv p 11).toLinearMap.comp
      (Adic.interiorCoordinateInclusion (p : ℤ_[p])) =
        (moduleInteriorInclusion (R := ℤ_[p])).comp
          (PadicScalarCompletion.finiteScalarEquiv p 5).toLinearMap := by
    apply LinearMap.ext
    intro x
    change PadicScalarCompletion.finiteScalarEquiv p 11
      (Adic.exactInclusion (p : ℤ_[p]) Adic.elevenSplit x) = _
    rw [Adic.exactInclusion_eq_completeMap]
    exact PadicScalarCompletion.finiteScalarEquiv_natural p 5 11 moduleInteriorInclusion x
  rw [hnat, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (PadicScalarCompletion.finiteScalarEquiv p 5).surjective,
    Submodule.map_top, moduleInteriorInclusion_range]

/-- The literal image of the actual completed interior module has exactly
the five numerical scalar coordinates. -/
def constantInteriorZpEquiv :
    ((LinearMap.range (completedInteriorInclusion uConstant (p : ℤ_[p]))).map
      (constantCoordinatesZp p hp hp7 hp19)) ≃ₗ[ℤ_[p]] (Fin 5 → ℤ_[p]) :=
  (LinearEquiv.ofEq _ _ (constantInteriorZp_image p hp hp7 hp19)).trans
    interiorCoordinatesEquiv

def constantInteriorSectionZp :
    (Fin 5 → ℤ_[p]) →ₗ[ℤ_[p]] Adic.Completion (p : ℤ_[p]) (FClosed uConstant) :=
  (Adic.interiorSection (M := FClosed uConstant) (N := exactSubmodule uConstant) (p : ℤ_[p]) eConstant).comp
    (PadicScalarCompletion.finiteScalarEquiv p 5).symm.toLinearMap

theorem constantCoordinatesZp_interiorSection (c : Fin 5 → ℤ_[p]) :
    constantCoordinatesZp p hp hp7 hp19 (constantInteriorSectionZp p hp hp7 hp19 c) =
      moduleInteriorInclusion c := by
  change PadicScalarCompletion.finiteScalarEquiv p 11
    (Adic.coordinates (M := FClosed uConstant) (N := exactSubmodule uConstant) (K := Fin 11 → ℤ_[p]) (p : ℤ_[p]) eConstant
      (Adic.interiorSection (M := FClosed uConstant) (N := exactSubmodule uConstant) (p : ℤ_[p]) eConstant
        ((PadicScalarCompletion.finiteScalarEquiv p 5).symm c))) = _
  rw [Adic.coordinates_interiorSection]
  change PadicScalarCompletion.finiteScalarEquiv p 11
    (Adic.exactInclusion (p : ℤ_[p]) Adic.elevenSplit
      ((PadicScalarCompletion.finiteScalarEquiv p 5).symm c)) = _
  rw [Adic.exactInclusion_eq_completeMap, PadicScalarCompletion.finiteScalarEquiv_natural]
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ConstantPadic

end
end WPResidueQuotient.ActualCompletion
