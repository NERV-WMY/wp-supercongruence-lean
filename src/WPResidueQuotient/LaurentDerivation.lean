import WPResidueQuotient.Basic
import WPResidueQuotient.LocalizationDerivation
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace WPResidueQuotient

noncomputable section

variable {R : Type*} [CommRing R]

def logarithmicLinear (w : Exponents →+ ℤ) :
    LaurentPolynomial R →ₗ[R] LaurentPolynomial R :=
  (Finsupp.lsum R (fun x => (w x : R) •
    (AddMonoidAlgebra.lsingle (R := R) x : R →ₗ[R] LaurentPolynomial R))).comp
      (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem logarithmicLinear_single (w : Exponents →+ ℤ) (x : Exponents) (r : R) :
    logarithmicLinear w (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single x ((w x : R) * r) := by
  simp [logarithmicLinear, AddMonoidAlgebra.smul_single]

theorem logarithmicLinear_leibniz (w : Exponents →+ ℤ)
    (P Q : LaurentPolynomial R) :
    logarithmicLinear w (P * Q) =
      P * logarithmicLinear w Q + Q * logarithmicLinear w P := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x =>
      induction Q using AddMonoidAlgebra.induction_on with
      | of y =>
          simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_add,
            map_add, Int.cast_add, add_comm]
      | add Q₁ Q₂ h₁ h₂ =>
          simp only [mul_add, map_add, h₁, h₂, add_mul]
          abel
      | smul r Q h =>
          simp only [mul_smul_comm, map_smul, h, smul_add, smul_mul_assoc]
  | add P₁ P₂ h₁ h₂ =>
      simp only [add_mul, map_add, h₁, h₂, mul_add]
      abel
  | smul r P h =>
      simp only [smul_mul_assoc, map_smul, h, smul_add, mul_smul_comm]

def logarithmicDerivation (w : Exponents →+ ℤ) :
    Derivation R (LaurentPolynomial R) (LaurentPolynomial R) :=
  Derivation.mk' (logarithmicLinear w) (by
    intro P Q
    simpa [Algebra.smul_def] using logarithmicLinear_leibniz w P Q)

@[simp] theorem logarithmicDerivation_single (w : Exponents →+ ℤ)
    (x : Exponents) (r : R) :
    logarithmicDerivation w (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single x ((w x : R) * r) :=
  logarithmicLinear_single w x r

def coordinateWeight (i : Fin 5) : Exponents →+ ℤ where
  toFun x := x i
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coordinateWeight_apply (i : Fin 5) (x : Exponents) :
    coordinateWeight i x = x i := rfl

def localizedLogarithmic (f : LaurentPolynomial R) (i : Fin 5) :
    Derivation R (Localization.Away f) (Localization.Away f) :=
  extendDerivation f (logarithmicDerivation (coordinateWeight i))

@[simp] theorem localizedLogarithmic_monomial (f : LaurentPolynomial R)
    (i : Fin 5) (x : Exponents) :
    localizedLogarithmic f i
      (algebraMap (LaurentPolynomial R) (Localization.Away f)
        (AddMonoidAlgebra.single x 1)) =
      algebraMap R (Localization.Away f) (x i : R) *
        algebraMap (LaurentPolynomial R) (Localization.Away f)
          (AddMonoidAlgebra.single x 1) := by
  simp only [localizedLogarithmic, extendDerivation_algebraMap,
    logarithmicDerivation_single, coordinateWeight_apply, mul_one]
  have h : AddMonoidAlgebra.single x (x i : R) =
      algebraMap R (LaurentPolynomial R) (x i : R) *
        AddMonoidAlgebra.single x 1 := by
    change AddMonoidAlgebra.single x (x i : R) =
      AddMonoidAlgebra.single 0 (x i : R) * AddMonoidAlgebra.single x 1
    simp
  rw [h, map_mul, ← IsScalarTower.algebraMap_apply R (LaurentPolynomial R)
    (Localization.Away f)]

end

end WPResidueQuotient
