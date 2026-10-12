import WPCompletedCartier.InteriorConstruction

namespace WPCompletedCartier.RationalizedCartier

noncomputable section
open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

abbrev Coeff := Localization (Submonoid.powers (p : ℤ_[p]))
abbrev Strict := FInterior (Parameter.integralTenth p hp7)
abbrev Completed := Completion (p : ℤ_[p]) (Strict p hp7)
abbrev Rationalized := LocalizedModule (Submonoid.powers (p : ℤ_[p])) (Completed p hp7)

def integralMap : Completed p hp7 →ₗ[ℤ_[p]] Rationalized p hp7 :=
  LocalizedModule.mkLinearMap (Submonoid.powers (p : ℤ_[p])) _

theorem integralMap_injective : Function.Injective (integralMap p hp7) :=
  AdicSeries.rationalization_injective (p : ℤ_[p])
    (AdicSeries.actualInterior_smul_injective (Parameter.integralTenth p hp7)
      (p : ℤ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

theorem factorial_isUnit (n : ℕ) :
    IsUnit (algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p])) := by
  obtain ⟨b, e, he⟩ := NumericalTerms.factorial_clear_p_power p n
  have hunit : IsUnit (algebraMap ℤ_[p] (Coeff p) ((p : ℤ_[p]) ^ e)) :=
    IsLocalization.map_units (M := Submonoid.powers (p : ℤ_[p])) (Coeff p)
      ⟨(p : ℤ_[p]) ^ e, e, rfl⟩
  rw [← he, map_mul] at hunit
  exact isUnit_of_mul_isUnit_right hunit

def inverseFactorial (n : ℕ) : Coeff p := (factorial_isUnit p n).unit⁻¹.val

theorem factorial_mul_inverse (n : ℕ) :
    algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p]) * inverseFactorial p n = 1 := by
  let hu := factorial_isUnit p n
  change algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p]) * hu.unit⁻¹.val = 1
  calc
    _ = hu.unit.val * hu.unit⁻¹.val :=
      congrArg (fun z : Coeff p => z * hu.unit⁻¹.val) hu.unit_spec.symm
    _ = 1 := Units.mul_inv _

/-- A raw pole is the actual factorial representative divided by its factorial
in the localization of the given strict completion. -/
def rawPole (n : ℕ) (A : numeratorFiltration ℤ_[p] n) : Rationalized p hp7 :=
  inverseFactorial p n • integralMap p hp7
    (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp7 n A))

theorem rawPole_factorial (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p]) • rawPole p hp7 n A =
      integralMap p hp7
        (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp7 n A)) := by
  rw [rawPole, smul_smul, factorial_mul_inverse, one_smul]

def cartier : Rationalized p hp7 →ₗ[Coeff p] Rationalized p hp7 :=
  AdicSeries.rationalizedMap (p : ℤ_[p]) (InteriorConstruction.completedCartier p hp7)

theorem cartier_integral (x : Completed p hp7) :
    cartier p hp7 (integralMap p hp7 x) =
      integralMap p hp7 (InteriorConstruction.completedCartier p hp7 x) := by
  exact AdicSeries.rationalizedMap_mk _ _ x 1

set_option maxHeartbeats 800000 in
theorem cartier_rawPole (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    cartier p hp7 (rawPole p hp7 n A) = inverseFactorial p n •
      integralMap p hp7 (InteriorSeries.generatorImage p hp7 n A) := by
  have hC := (InteriorConstruction.completedCartier_ofModule p hp7
    (InteriorConstruction.numeratorToInterior p hp7 n A)).trans
      (InteriorConstruction.cartier_numerator p hp7 n A)
  calc
    _ = inverseFactorial p n • cartier p hp7 (integralMap p hp7
        (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp7 n A))) :=
      map_smul (cartier p hp7) (inverseFactorial p n) _
    _ = inverseFactorial p n • integralMap p hp7
        (InteriorConstruction.completedCartier p hp7
          (ofModule (p : ℤ_[p]) (InteriorConstruction.numeratorToInterior p hp7 n A))) :=
      congrArg (fun z : Rationalized p hp7 => inverseFactorial p n • z)
        (cartier_integral p hp7 _)
    _ = _ := congrArg (fun z : Completed p hp7 =>
      inverseFactorial p n • integralMap p hp7 z) hC

theorem height_le_of_admissible (n h : ℕ) (hadm : n + 1 ≤ p * h) :
    ActualSeries.height p n ≤ h := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have ht : n < h * p := by
    simpa only [Nat.mul_comm] using (show n < p * h by omega)
  have hd : n / p < h := (Nat.div_lt_iff_lt_mul hp).mpr ht
  unfold ActualSeries.height
  omega

set_option maxHeartbeats 800000 in
theorem cartier_rawPole_normalized (n h : ℕ)
    (A : numeratorFiltration ℤ_[p] n) (hh : 1 ≤ h) (hadm : n + 1 ≤ p * h) :
    cartier p hp7 (rawPole p hp7 n A) = inverseFactorial p (h - 1) •
      integralMap p hp7
        (InteriorSeries.clearedSeriesMap p hp7 (n + 1) h (by omega) hh hadm
          ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩) := by
  have he := InteriorSeries.generatorImage_factorial_cleared p hp7 n h A
    (height_le_of_admissible p n h hadm)
  have hmap := congrArg (integralMap p hp7) he
  rw [map_smul, map_smul] at hmap
  have hmap' : algebraMap ℤ_[p] (Coeff p) ((h - 1).factorial : ℤ_[p]) •
      integralMap p hp7 (InteriorSeries.generatorImage p hp7 n A) =
    algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p]) •
      integralMap p hp7
        (InteriorSeries.clearedSeriesMap p hp7 (n + 1) h (by omega) hh hadm
          ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩) := by
    simpa only [IsScalarTower.algebraMap_smul] using hmap
  rw [cartier_rawPole]
  apply (factorial_isUnit p (h - 1)).smul_left_cancel.mp
  calc
    _ = inverseFactorial p n •
        (algebraMap ℤ_[p] (Coeff p) ((h - 1).factorial : ℤ_[p]) •
          integralMap p hp7 (InteriorSeries.generatorImage p hp7 n A)) := smul_comm _ _ _
    _ = inverseFactorial p n •
        (algebraMap ℤ_[p] (Coeff p) (n.factorial : ℤ_[p]) •
          integralMap p hp7
            (InteriorSeries.clearedSeriesMap p hp7 (n + 1) h (by omega) hh hadm
              ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩)) := by rw [hmap']
    _ = integralMap p hp7
        (InteriorSeries.clearedSeriesMap p hp7 (n + 1) h (by omega) hh hadm
          ⟨A.val, by simpa only [Nat.add_sub_cancel] using A.property⟩) := by
      rw [smul_smul, mul_comm, factorial_mul_inverse, one_smul]
    _ = _ := by rw [smul_smul, factorial_mul_inverse, one_smul]

end

end WPCompletedCartier.RationalizedCartier
