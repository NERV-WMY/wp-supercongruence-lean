import WPResidueQuotient.ActualSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
Extension of the literal rational constant-family residue quotient to an
arbitrary characteristic-zero field. The equivalence is proved from the
actual constant coordinate equivalences, and is identified with the tensor
map induced by the actual localized coefficient map. Its eleven columns are
the literal five factorial poles and six boundary fractions in the target.
-/

namespace WPResidueQuotient.ActualSpecialization

noncomputable section

open scoped TensorProduct
open MellinFactors

variable (K : Type*) [Field K] [CharZero K]

theorem rationalConstant_parameter_map :
    algebraMap ℚ K (1 / 10 : ℚ) = (1 / 10 : K) := by
  norm_num [map_div₀]

/-- The actual localized rational coefficient map, restricted to the actual residue quotient. -/
def rationalConstantMap : ClosedResidueQuotient (1 / 10 : ℚ) →ₗ[ℚ]
    ClosedResidueQuotient (1 / 10 : K) where
  toFun := IntegralTransport.quotientMap (algebraMap ℚ K) (1 / 10) (1 / 10)
    (rationalConstant_parameter_map K)
  map_add' a b := map_add (IntegralTransport.quotientMap (algebraMap ℚ K)
    (1 / 10) (1 / 10) (rationalConstant_parameter_map K)) a b
  map_smul' a q := by
    change IntegralTransport.quotientMap (algebraMap ℚ K) (1 / 10) (1 / 10)
      (rationalConstant_parameter_map K) (a • q) = a • _
    rw [map_smulₛₗ]
    exact IsScalarTower.algebraMap_smul K a _

theorem rationalConstantMap_elevenSection (a : Fin 11 → ℚ) :
    rationalConstantMap K (Actual.elevenQuotientSection (1 / 10 : ℚ) a) =
      Actual.elevenQuotientSection (1 / 10 : K) (fun i => algebraMap ℚ K (a i)) :=
  transportedQuotientMap_elevenSection (algebraMap ℚ K) (1 / 10) (1 / 10)
    (rationalConstant_parameter_map K) a

theorem rationalConstantMap_elevenFamily (i : Fin 11) :
    rationalConstantMap K (Actual.elevenQuotientFamily (1 / 10 : ℚ) i) =
      Actual.elevenQuotientFamily (1 / 10 : K) i := by
  change IntegralTransport.quotientMap (algebraMap ℚ K) (1 / 10) (1 / 10)
      (rationalConstant_parameter_map K) (Submodule.Quotient.mk (Actual.elevenClosedElement _ i)) =
    Submodule.Quotient.mk (Actual.elevenClosedElement _ i)
  rw [IntegralTransport.quotientMap_mk, transportedClosedMap_elevenElement]

def rationalTensorBilinear : K →ₗ[K]
    (ClosedResidueQuotient (1 / 10 : ℚ) →ₗ[ℚ] ClosedResidueQuotient (1 / 10 : K)) where
  toFun a := a • rationalConstantMap K
  map_add' a b := add_smul a b (rationalConstantMap K)
  map_smul' a b := by
    change (a * b) • rationalConstantMap K = a • (b • rationalConstantMap K)
    exact mul_smul a b (rationalConstantMap K)

/-- The literal scalar extension map induced by the actual rational coefficient map. -/
def rationalScalarExtensionMap : K ⊗[ℚ] ClosedResidueQuotient (1 / 10 : ℚ) →ₗ[K]
    ClosedResidueQuotient (1 / 10 : K) :=
  TensorProduct.AlgebraTensorModule.lift (rationalTensorBilinear K)

@[simp] theorem rationalScalarExtensionMap_tmul
    (a : K) (q : ClosedResidueQuotient (1 / 10 : ℚ)) :
    rationalScalarExtensionMap K (a ⊗ₜ[ℚ] q) = a • rationalConstantMap K q := rfl

/-- Genuine field extension of the actual finite rational constant presentation. -/
def rationalScalarExtensionEquiv : K ⊗[ℚ] ClosedResidueQuotient (1 / 10 : ℚ) ≃ₗ[K]
    ClosedResidueQuotient (1 / 10 : K) :=
  (((rationalConstantQuotientEquiv).symm.baseChange ℚ K _ _).trans
    (TensorProduct.piScalarRight ℚ K K (Fin 11))).trans (tenthQuotientEquiv K)

theorem rationalScalarExtensionEquiv_tmul
    (a : K) (q : ClosedResidueQuotient (1 / 10 : ℚ)) :
    rationalScalarExtensionEquiv K (a ⊗ₜ[ℚ] q) = a • rationalConstantMap K q := by
  obtain ⟨b, rfl⟩ := rationalConstantQuotientEquiv.surjective q
  have hb : rationalConstantMap K (rationalConstantQuotientEquiv b) =
      Actual.elevenQuotientSection (1 / 10 : K) (fun i => algebraMap ℚ K (b i)) := by
    rw [show rationalConstantQuotientEquiv b = Actual.elevenQuotientSection (1 / 10 : ℚ) b
      from tenthQuotientEquiv_apply ℚ b]
    exact rationalConstantMap_elevenSection K b
  have hcoords : (fun i => b i • a) = a • (fun i => algebraMap ℚ K (b i)) := by
    ext i
    simp only [Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  simp only [rationalScalarExtensionEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rw [hcoords, map_smul, tenthQuotientEquiv_apply, hb]

theorem rationalScalarExtensionEquiv_is_actual_map :
    (rationalScalarExtensionEquiv K).toLinearMap = rationalScalarExtensionMap K := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a q
  exact rationalScalarExtensionEquiv_tmul K a q

@[simp] theorem rationalScalarExtensionEquiv_column (i : Fin 11) :
    rationalScalarExtensionEquiv K
      (1 ⊗ₜ[ℚ] Actual.elevenQuotientFamily (1 / 10 : ℚ) i) =
        Actual.elevenQuotientFamily (1 / 10 : K) i := by
  rw [rationalScalarExtensionEquiv_tmul, one_smul, rationalConstantMap_elevenFamily]

theorem rationalScalarExtensionEquiv_gamma_column (i : Fin 5) :
    rationalScalarExtensionEquiv K
      (1 ⊗ₜ[ℚ] gammaQuotientFamily (1 / 10 : ℚ) i) =
        gammaQuotientFamily (1 / 10 : K) i := by
  rw [← Actual.elevenQuotientFamily_left (1 / 10 : ℚ),
    rationalScalarExtensionEquiv_column, Actual.elevenQuotientFamily_left]

theorem rationalScalarExtensionEquiv_boundary_column (i : Fin 6) :
    rationalScalarExtensionEquiv K
      (1 ⊗ₜ[ℚ] (exactSubmodule (1 / 10 : ℚ)).mkQ (vertexBoundaryElement _ i)) =
        (exactSubmodule (1 / 10 : K)).mkQ (vertexBoundaryElement _ i) := by
  rw [← Actual.elevenQuotientFamily_right (1 / 10 : ℚ),
    rationalScalarExtensionEquiv_column, Actual.elevenQuotientFamily_right]

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- Literal p-adic scalar extension of the actual rational constant-family quotient. -/
def padicScalarExtensionEquiv :
    ℚ_[p] ⊗[ℚ] ClosedResidueQuotient (1 / 10 : ℚ) ≃ₗ[ℚ_[p]]
      ClosedResidueQuotient (1 / 10 : ℚ_[p]) := rationalScalarExtensionEquiv ℚ_[p]

theorem padicScalarExtensionEquiv_is_actual_map :
    (padicScalarExtensionEquiv p).toLinearMap = rationalScalarExtensionMap ℚ_[p] :=
  rationalScalarExtensionEquiv_is_actual_map ℚ_[p]

@[simp] theorem padicScalarExtensionEquiv_column (i : Fin 11) :
    padicScalarExtensionEquiv p
      (1 ⊗ₜ[ℚ] Actual.elevenQuotientFamily (1 / 10 : ℚ) i) =
        Actual.elevenQuotientFamily (1 / 10 : ℚ_[p]) i :=
  rationalScalarExtensionEquiv_column ℚ_[p] i

end Padic

end

end WPResidueQuotient.ActualSpecialization
