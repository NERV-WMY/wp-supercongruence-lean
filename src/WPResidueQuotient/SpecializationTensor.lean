import WPResidueQuotient.RationalSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
The actual constant family is scalar base change through the actual
coefficient fiber. The coefficient fiber is proved isomorphic to the ground
field; the tensor quotient isomorphism is combined with the already proved
finite-numerator specialization kernel. No finite rank statement is used.
-/

namespace WPResidueQuotient.Specialization

noncomputable section

open Parameter
open scoped TensorProduct Pointwise

variable (K : Type*) [Field K] [CharZero K]
variable (c : K) (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0)

def fieldSpecializationAlg : ParameterRing K →ₐ[K] K where
  __ := fieldSpecialization K c hc
  commutes' := fieldSpecialization_scalar K c hc

omit [CharZero K] in
theorem fieldSpecialization_kernel_ideal :
    RingHom.ker (fieldSpecialization K c hc) = Ideal.span {fieldFiberParameter K c} := by
  ext r
  change fieldSpecialization K c hc r = 0 ↔ r ∈ Ideal.span {fieldFiberParameter K c}
  rw [Ideal.mem_span_singleton]
  exact fieldSpecialization_eq_zero_iff K c hc r

/-- Coefficient base change really is evaluation in the ground field. -/
def fieldCoefficientFiberEquiv :
    (ParameterRing K ⧸ RingHom.ker (fieldSpecialization K c hc)) ≃ₐ[K] K :=
  Ideal.quotientKerAlgEquivOfSurjective (f := fieldSpecializationAlg K c hc)
    (fieldSpecialization_surjective K c hc)

omit [CharZero K] in
@[simp] theorem fieldCoefficientFiberEquiv_mk (r : ParameterRing K) :
    fieldCoefficientFiberEquiv K c hc
      (Ideal.Quotient.mk (RingHom.ker (fieldSpecialization K c hc)) r) =
        fieldSpecialization K c hc r := rfl

omit [CharZero K] in
theorem coefficientKernel_smul_top :
    RingHom.ker (fieldSpecialization K c hc) •
        (⊤ : Submodule (ParameterRing K)
          (ClosedResidueQuotient (Parameter.u : ParameterRing K))) =
      fieldFiberSubmodule K c := by
  rw [fieldSpecialization_kernel_ideal, Submodule.ideal_span_singleton_smul]
  ext g
  rw [Submodule.mem_smul_pointwise_iff_exists, mem_fieldFiberSubmodule]
  simp only [Submodule.mem_top, true_and, eq_comm]

/-- Actual residue quotient base change through the proved coefficient fiber. -/
def fieldSpecializationTensorEquiv :
    ((ParameterRing K ⧸ RingHom.ker (fieldSpecialization K c hc)) ⊗[ParameterRing K]
      (ClosedResidueQuotient (Parameter.u : ParameterRing K))) ≃ₗ[K]
        ClosedResidueQuotient c := by
  let e := (TensorProduct.quotTensorEquivQuotSMul
    (ClosedResidueQuotient (Parameter.u : ParameterRing K))
    (RingHom.ker (fieldSpecialization K c hc))).restrictScalars K
  rw [coefficientKernel_smul_top K c hc] at e
  exact (e.trans (Submodule.Quotient.restrictScalarsEquiv K
    (fieldFiberSubmodule K c)).symm).trans (fieldFiberEquiv K c hc)

/-- Literal `1/10` scalar base change over any characteristic-zero field. -/
def tenthSpecializationTensorEquiv :
    ((ParameterRing K ⧸ RingHom.ker (tenthSpecialization K)) ⊗[ParameterRing K]
      (ClosedResidueQuotient (Parameter.u : ParameterRing K))) ≃ₗ[K]
        ClosedResidueQuotient (1 / 10 : K) :=
  fieldSpecializationTensorEquiv K (1 / 10) (tenth_denominator_nonzero K)

end

end WPResidueQuotient.Specialization
