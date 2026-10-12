import WPCompletedCartier.ActualRelations
import Mathlib.LinearAlgebra.Isomorphisms

namespace WPCompletedCartier

noncomputable section

open WPResidueQuotient

variable {R T : Type*} [CommRing R] [AddCommGroup T] [Module R T]

theorem presentationToClosed_kernel (u : R) :
    LinearMap.ker (presentationToClosed u) = LinearMap.ker (presentationMap u) := by
  ext v
  change presentationToClosed u v = 0 ↔ presentationMap u v = 0
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Lift only after the kernel of the literal actual presentation is proved killed. -/
def liftActualPresentation (u : R) (L : ClosedPresentation R →ₗ[R] T)
    (hL : LinearMap.ker (presentationMap u) ≤ LinearMap.ker L) : FClosed u →ₗ[R] T :=
  ((LinearMap.ker (presentationToClosed u)).liftQ L
    (by rw [presentationToClosed_kernel]; exact hL)).comp
      ((presentationToClosed u).quotKerEquivOfSurjective
        (presentationToClosed_surjective u)).symm.toLinearMap

@[simp] theorem liftActualPresentation_apply (u : R) (L : ClosedPresentation R →ₗ[R] T)
    (hL : LinearMap.ker (presentationMap u) ≤ LinearMap.ker L)
    (v : ClosedPresentation R) :
    liftActualPresentation u L hL (presentationToClosed u v) = L v := by
  simp only [liftActualPresentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

theorem liftActualPresentation_unique (u : R) (L : ClosedPresentation R →ₗ[R] T)
    (hL : LinearMap.ker (presentationMap u) ≤ LinearMap.ker L)
    (C : FClosed u →ₗ[R] T) (hC : ∀ v, C (presentationToClosed u v) = L v) :
    C = liftActualPresentation u L hL := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := presentationToClosed_surjective u x
  rw [hC, liftActualPresentation_apply]

end

end WPCompletedCartier
