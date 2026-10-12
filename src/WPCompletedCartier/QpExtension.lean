import WPCompletedCartier.PadicRationalization
import WPCompletedCartier.RationalizedCartier

namespace WPCompletedCartier.QpExtension

noncomputable section
open WPResidueQuotient WPResidueQuotient.Adic
open WPCompletedCartier.PadicRationalization

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

local notation "L" => RationalizedCartier.Coeff p
local notation "W" => RationalizedCartier.Rationalized p hp
local notation "e" => padicLocalizationEquiv p

/-- Scalar extension on the given rationalized strict completion, induced by
the proved inverse coefficient equivalence with the literal p-adic field. -/
instance qpModule : Module ℚ_[p] W :=
  Module.compHom W (e).symm.toRingHom

local instance : Module ℚ_[p] W := qpModule p hp

/-- Cache the scalar action of the transported module itself. -/
instance (priority := 1001) qpSMul : SMul ℚ_[p] W :=
  (qpModule p hp).toDistribMulAction.toMulAction.toSMul

/-- Its result type is fixed explicitly, so scalar notation does not search
for unrelated algebra structures on the actual localized module. -/
instance (priority := 1001) qpHSMul : HSMul ℚ_[p] W W :=
  ⟨@SMul.smul ℚ_[p] W (qpSMul p hp)⟩

theorem qp_smul (a : ℚ_[p]) (x : W) : (a • x : W) = ((e).symm a • x : W) := rfl

theorem qp_smul_original (a : L) (x : W) : ((e a : ℚ_[p]) • x : W) = (a • x : W) := by
  rw [qp_smul, AlgEquiv.symm_apply_apply]

/-- The existing integral action is preserved by the actual Zp embedding. -/
theorem qp_smul_integral (a : ℤ_[p]) (x : W) : ((a : ℚ_[p]) • x : W) = (a • x : W) := by
  rw [qp_smul, padicLocalizationEquiv_symm_coe]
  exact IsScalarTower.algebraMap_smul L a x

instance integralQpTower : IsScalarTower ℤ_[p] ℚ_[p] W where
  smul_assoc a b x := by
    change (e).symm ((a : ℚ_[p]) * b) • x = a • ((e).symm b • x)
    rw [map_mul, padicLocalizationEquiv_symm_coe, mul_smul,
      IsScalarTower.algebraMap_smul]

/-- This has the same underlying function as the constructed Cartier map on
the localization of the actual completed strict module. -/
def cartierQp : W →ₗ[ℚ_[p]] W where
  toFun := RationalizedCartier.cartier p hp
  map_add' x y := map_add (RationalizedCartier.cartier p hp) x y
  map_smul' a x := by
    change RationalizedCartier.cartier p hp ((e).symm a • x) =
      (e).symm a • RationalizedCartier.cartier p hp x
    exact map_smul (RationalizedCartier.cartier p hp) ((e).symm a) x

@[simp] theorem cartierQp_apply (x : W) :
    cartierQp p hp x = RationalizedCartier.cartier p hp x := rfl

theorem cartierQp_integral (x : RationalizedCartier.Completed p hp) :
    cartierQp p hp (RationalizedCartier.integralMap p hp x) =
      RationalizedCartier.integralMap p hp (InteriorConstruction.completedCartier p hp x) :=
  RationalizedCartier.cartier_integral p hp x

theorem inverseFactorial_cast (n : ℕ) :
    e (RationalizedCartier.inverseFactorial p n) = (n.factorial : ℚ_[p])⁻¹ := by
  apply mul_right_cancel₀ (show (n.factorial : ℚ_[p]) ≠ 0 from
    by exact_mod_cast Nat.factorial_ne_zero n)
  rw [inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n)]
  have h := congrArg e (RationalizedCartier.factorial_mul_inverse p n)
  simpa only [map_mul, map_one, padicLocalizationEquiv_algebraMap,
    PadicInt.coe_natCast, mul_comm] using h

/-- The raw pole is divided by its literal factorial in Qp on the same
localized actual module. -/
theorem rawPole_qp (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    RationalizedCartier.rawPole p hp n A = ((n.factorial : ℚ_[p])⁻¹ •
      RationalizedCartier.integralMap p hp
        (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp n A)) : W) := by
  rw [← inverseFactorial_cast]
  exact (qp_smul_original p hp (RationalizedCartier.inverseFactorial p n) _).symm

theorem cartierQp_rawPole (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    cartierQp p hp (RationalizedCartier.rawPole p hp n A) = ((n.factorial : ℚ_[p])⁻¹ •
      RationalizedCartier.integralMap p hp (InteriorSeries.generatorImage p hp n A) : W) := by
  rw [cartierQp_apply, RationalizedCartier.cartier_rawPole, ← inverseFactorial_cast]
  exact (qp_smul_original p hp (RationalizedCartier.inverseFactorial p n) _).symm

/-- The honest arbitrary admissible-height normalization, now over literal
Qp, is inherited from the same constructed rationalized Cartier function. -/
theorem cartierQp_rawPole_normalized (n h : ℕ)
    (A : numeratorFiltration ℤ_[p] n) (hh : 1 ≤ h) (hadm : n + 1 ≤ p * h) :
    cartierQp p hp (RationalizedCartier.rawPole p hp n A) =
      (((h - 1).factorial : ℚ_[p])⁻¹ • RationalizedCartier.integralMap p hp
        (InteriorSeries.clearedSeriesMap p hp (n + 1) h (by omega) hh hadm
          ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩) : W) := by
  rw [cartierQp_apply, RationalizedCartier.cartier_rawPole_normalized p hp n h A hh hadm,
    ← inverseFactorial_cast]
  exact (qp_smul_original p hp (RationalizedCartier.inverseFactorial p (h - 1)) _).symm

end
end WPCompletedCartier.QpExtension
