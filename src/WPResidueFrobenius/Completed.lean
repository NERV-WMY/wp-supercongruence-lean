import WPResidueFrobenius.IntegralOperator
import WPResidueQuotient.ActualCompletion

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

abbrev CompletedClosedQuotient :=
  Adic.Completion (p : ℤ_[p]) (FClosed (Parameter.integralTenth p hp)) ⧸
    LinearMap.range (ActualCompletion.constantCompletedExactInclusion p hp)

def completedCoordinates : CompletedClosedQuotient p hp →ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).toLinearMap

def completedSection : (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]] CompletedClosedQuotient p hp :=
  (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).symm.toLinearMap

@[simp] theorem completedCoordinates_section (v : Fin 11 → ℤ_[p]) :
    completedCoordinates p hp hp7 hp19 (completedSection p hp hp7 hp19 v) = v :=
  (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).apply_symm_apply v

@[simp] theorem completedSection_coordinates (g : CompletedClosedQuotient p hp) :
    completedSection p hp hp7 hp19 (completedCoordinates p hp hp7 hp19 g) = g :=
  (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).symm_apply_apply g

@[simp] theorem completedCoordinates_mk
    (x : Adic.Completion (p : ℤ_[p]) (FClosed (Parameter.integralTenth p hp))) :
    completedCoordinates p hp hp7 hp19 (Submodule.Quotient.mk x) =
      ActualCompletion.constantCoordinatesZp p hp hp7 hp19 x :=
  ActualCompletion.constantQuotientZpEquiv_mk p hp hp7 hp19 x

theorem continuous_completedCoordinates : Continuous (completedCoordinates p hp hp7 hp19) := by
  apply (Submodule.isQuotientMap_mkQ
    (LinearMap.range (ActualCompletion.constantCompletedExactInclusion p hp))).continuous_iff.mpr
  simpa only [Function.comp_def, Submodule.mkQ_apply, completedCoordinates_mk] using
    ActualCompletion.continuous_constantCoordinatesZp p hp hp7 hp19

theorem completedSection_eq_mk (v : Fin 11 → ℤ_[p]) :
    completedSection p hp hp7 hp19 v = Submodule.Quotient.mk
      (ActualCompletion.constantSectionZp p hp hp7 hp19 v) := by
  apply (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).injective
  change completedCoordinates p hp hp7 hp19 (completedSection p hp hp7 hp19 v) =
    completedCoordinates p hp hp7 hp19 (Submodule.Quotient.mk
      (ActualCompletion.constantSectionZp p hp hp7 hp19 v))
  rw [completedCoordinates_section, completedCoordinates_mk,
    ActualCompletion.constantCoordinatesZp_section]

theorem continuous_completedSection : Continuous (completedSection p hp hp7 hp19) := by
  have he : (completedSection p hp hp7 hp19 : (Fin 11 → ℤ_[p]) → CompletedClosedQuotient p hp) =
      fun v => Submodule.Quotient.mk (ActualCompletion.constantSectionZp p hp hp7 hp19 v) :=
    funext (completedSection_eq_mk p hp hp7 hp19)
  rw [he]
  exact continuous_quotient_mk'.comp (ActualCompletion.continuous_constantSectionZp p hp hp7 hp19)

/-- Numerical original Frobenius, transported from the actual raw pullback descended above. -/
def PhiU : CompletedClosedQuotient p hp →ₗ[ℤ_[p]] CompletedClosedQuotient p hp :=
  (completedSection p hp hp7 hp19).comp
    ((coordinatePhi p hp hp7 hp19).comp (completedCoordinates p hp hp7 hp19))

theorem PhiU_coordinates (g : CompletedClosedQuotient p hp) :
    completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19 g) =
      coordinatePhi p hp hp7 hp19 (completedCoordinates p hp hp7 hp19 g) := by
  exact completedCoordinates_section p hp hp7 hp19 _

theorem continuous_PhiU : Continuous (PhiU p hp hp7 hp19) :=
  (continuous_completedSection p hp hp7 hp19).comp
    ((continuous_coordinatePhi p hp hp7 hp19).comp (continuous_completedCoordinates p hp hp7 hp19))

def moduleClass (g : FClosed (Parameter.integralTenth p hp)) : CompletedClosedQuotient p hp :=
  Submodule.Quotient.mk (Adic.ofModule (p : ℤ_[p]) g)

theorem moduleClass_coordinates (g : FClosed (Parameter.integralTenth p hp)) :
    completedCoordinates p hp hp7 hp19 (moduleClass p hp g) =
      ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g := by
  rw [moduleClass, completedCoordinates_mk, ActualCompletion.constantCoordinatesZp_ofModule]

theorem PhiU_moduleClass_raw (g : FClosed (Parameter.integralTenth p hp)) :
    presentedPullback p hp g = fun i => IntegralTransport.padicCoefficientMap p
      (completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19 (moduleClass p hp g)) i) := by
  rw [PhiU_coordinates, moduleClass_coordinates]
  exact presentedPullback_coordinates p hp hp7 hp19 g

theorem completed_exact_class_zero
    (g : Adic.Completion (p : ℤ_[p]) (exactSubmodule (Parameter.integralTenth p hp))) :
    PhiU p hp hp7 hp19 (Submodule.Quotient.mk
      (ActualCompletion.constantCompletedExactInclusion p hp g)) = 0 := by
  rw [(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ g), map_zero]

theorem completed_closed_derivative_range_zero
    (x : Adic.Completion (p : ℤ_[p]) (FClosed (Parameter.integralTenth p hp)))
    (hx : x ∈ closure (Set.range (Adic.completeMap (p : ℤ_[p])
      (exactAggregate (Parameter.integralTenth p hp))))) :
    PhiU p hp hp7 hp19 (Submodule.Quotient.mk x) = 0 := by
  rw [ActualCompletion.constant_completed_derivative_closure p hp hp7 hp19] at hx
  obtain ⟨g, rfl⟩ := hx
  exact completed_exact_class_zero p hp hp7 hp19 g

end WPResidueFrobenius
