import WPOperatorIntegration.FiniteGamma
import WPResidueFrobenius.Interior
import WPCompletedCartier.InverseTraceQuotient

noncomputable section

set_option maxHeartbeats 1600000

namespace WPOperatorIntegration

open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.Adic WPResidueQuotient.ActualCompletion
open WPCompletedCartier.ActualRationalizedQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local instance : Module ℚ_[p] (RationalizedQuotient p hp) := quotientQpModule p hp

theorem actual_rawPole_coordinates (n : ℕ) (A : numeratorFiltration ℤ_[p] n) :
    gammaQuotientEquiv p hp hp7 hp19 (rawPoleQuotient p hp n A) =
      fun i => (n.factorial : ℚ_[p])⁻¹ *
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
          (actualInteriorInclusion (Parameter.integralTenth p hp)
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A))
          (Fin.castAdd 6 i) : ℚ_[p]) := by
  let x := ofModule (p : ℤ_[p])
    (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A)
  let q := integralProjection p hp x
  have hcoords : WPCompletedCartier.ActualQuotient.actualInteriorQuotientEquiv
      p hp hp7 hp19 q = moduleInteriorProjection
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
          (actualInteriorInclusion (Parameter.integralTenth p hp)
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A))) := by
    have hq := WPCompletedCartier.ActualQuotient.actualInteriorQuotientEquiv_coordinates
      p hp hp7 hp19 q
    have hmk := constantQuotientZpEquiv_mk p hp hp7 hp19
      (completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) x)
    have hx : constantCoordinatesZp p hp hp7 hp19
        (completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) x) =
      ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
        (actualInteriorInclusion (Parameter.integralTenth p hp)
          (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A)) := by
      have he : completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p])
          (ofModule (p : ℤ_[p])
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A)) =
        ofModule (p : ℤ_[p])
          (actualInteriorInclusion (Parameter.integralTenth p hp)
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A)) :=
        completeMap_ofModule _ _ _
      change constantCoordinatesZp p hp hp7 hp19
        (completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p])
          (ofModule (p : ℤ_[p])
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp n A))) = _
      rw [he, constantCoordinatesZp_ofModule]
    exact hq.trans ((congrArg (moduleInteriorProjection (R := ℤ_[p])) hmk).trans
      (congrArg (moduleInteriorProjection (R := ℤ_[p])) hx))
  have hraw := rawPoleQuotient_eq p hp n A
  have hs := (gammaQuotientEquiv p hp hp7 hp19).map_smul
    (n.factorial : ℚ_[p])⁻¹ (integralQuotientMap p hp q)
  have hi := gammaQuotientEquiv_integral p hp hp7 hp19 q
  have h := (congrArg (gammaQuotientEquiv p hp hp7 hp19) hraw).trans
    (hs.trans (congrArg (fun v : Fin 5 → ℚ_[p] => (n.factorial : ℚ_[p])⁻¹ • v) hi))
  exact h.trans (congrArg (fun v : Fin 5 → ℤ_[p] =>
    (n.factorial : ℚ_[p])⁻¹ • WPCompletedCartier.InverseTraceCoordinates.coeVector p v)
    hcoords)

theorem actual_term_normalization (j : Fin 5) (k : ℕ) :
    (fun i : Fin 5 => ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (WPResidueFrobenius.rawPullbackTerm p hp (j.val + 1) k (by omega)
        (WPResidueFrobenius.gammaNumerator p)
        (WPResidueFrobenius.gammaNumerator_supported p (j.val + 1)))
      (Fin.castAdd 6 i)) =
    ((p : ℚ_[p])^5 * (j.val.factorial : ℚ_[p])) •
      gammaQuotientEquiv p hp hp7 hp19
        ((WPCompletedCartier.InverseTraceConstruction.inputCoefficient p j k : ℚ_[p]) •
          rawPoleQuotient p hp
            (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
            (WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k)) := by
  have hs := (gammaQuotientEquiv p hp hp7 hp19).map_smul
    (WPCompletedCartier.InverseTraceConstruction.inputCoefficient p j k : ℚ_[p])
    (rawPoleQuotient p hp (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
      (WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k))
  rw [hs, actual_rawPole_coordinates]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [WPResidueFrobenius.rawPullbackTerm, map_smul,
    WPResidueFrobenius.integralToField_coordinates,
    actual_numerator_inclusion, actual_pullbackScalar_normalization]
  change ((p : ℚ_[p])^5 * (j.val.factorial : ℚ_[p]) *
      (WPCompletedCartier.InverseTraceConstruction.inputCoefficient p j k : ℚ_[p]) /
      ((WPCompletedCartier.InverseTraceConstruction.inputIndex p j k).factorial : ℚ_[p])) *
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19
          (actualInteriorInclusion (Parameter.integralTenth p hp)
            (WPCompletedCartier.InteriorConstruction.numeratorToInterior p hp
              (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
              (WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k)))
          (Fin.castAdd 6 i) : ℚ_[p]) = _
  ring

theorem actual_finite_normalization (N : ℕ) (j : Fin 5) :
    finiteGammaColumn p hp N j =
      ((p : ℚ_[p])^5 * (j.val.factorial : ℚ_[p])) •
        gammaQuotientEquiv p hp hp7 hp19 (finitePullbackQuotient p hp N j) := by
  let term : ℕ → RationalizedQuotient p hp := fun k =>
    ((WPCompletedCartier.InverseTraceConstruction.inputCoefficient p j k : ℚ_[p]) •
      rawPoleQuotient p hp
        (WPCompletedCartier.InverseTraceConstruction.inputIndex p j k)
        (WPCompletedCartier.InverseTraceConstruction.inputNumerator p hp j k))
  have hsum := map_sum (gammaQuotientEquiv p hp hp7 hp19).toAddMonoidHom term
    (Finset.range N)
  have hfinite := finitePullbackQuotient_eq p hp N j
  have ht : finiteGammaColumn p hp N j =
      ∑ k ∈ Finset.range N, (((p : ℚ_[p])^5 * (j.val.factorial : ℚ_[p])) •
        gammaQuotientEquiv p hp hp7 hp19 (term k)) := by
    ext i
    simp only [finiteGammaColumn, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact congrFun (actual_term_normalization p hp hp7 hp19 j k) i
  exact ht.trans (Finset.smul_sum.symm.trans
    (congrArg (fun v : Fin 5 → ℚ_[p] => ((p : ℚ_[p])^5 *
      (j.val.factorial : ℚ_[p])) • v)
      (hsum.symm.trans (congrArg (gammaQuotientEquiv p hp hp7 hp19) hfinite.symm))))

end WPOperatorIntegration
