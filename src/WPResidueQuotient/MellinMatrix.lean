import WPResidueQuotient.MellinSeries

/-!
# Independence of the actual five formal Mellin images

The matrix entries below are constructed u-series. Its constant coefficient
is the previously proved actual rho-coefficient matrix, with determinant
`6^10`. This proves independence of the five formal images over `ℚ((u))`.
Descent to the actual rational-function quotient is a separate dependency.
-/

noncomputable section

namespace WPResidueQuotient
namespace MellinFactors

open scoped BigOperators LaurentSeries RatFunc

def zeroExponent : ExponentVector := fun _ => 0

theorem mellinTerm_zeroExponent (m : ℤ) : mellinTerm m 0 zeroExponent = G m := by
  simp [mellinTerm, poleIndex, denominatorIndices, coefficient, zeroExponent, inverseH]

theorem rhoCoordinate_polynomial (r : Fin 5) (p : Polynomial ℚ) :
    rhoCoordinate r (algebraMap (Polynomial ℚ) RF p) = p.coeff r.val := by
  rw [rhoCoordinate_apply]
  change ((p : RF) : LS).coeff (r.val : ℤ) = p.coeff r.val
  rw [← RatFunc.coe_coe, PowerSeries.coeff_coe]
  simp

def interiorPowerSeriesMatrix : Matrix (Fin 5) (Fin 5) (PowerSeries ℚ) :=
  fun r c => sparsePowerSeries
    (fun n => termCoordinate r ((c.val : ℤ) + 1) (n : ℤ) zeroExponent)

theorem interiorPowerSeriesMatrix_constantCoeff :
    (PowerSeries.constantCoeff : PowerSeries ℚ →+* ℚ).mapMatrix
      interiorPowerSeriesMatrix = constantCoefficientMatrix := by
  ext r c
  change PowerSeries.constantCoeff
      (sparsePowerSeries
        (fun n => termCoordinate r ((c.val : ℤ) + 1) (n : ℤ) zeroExponent)) =
    (positivePolynomial 6 c.val).coeff r.val
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sparsePowerSeries_coeff]
  simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero]
  unfold termCoordinate
  rw [mellinTerm_zeroExponent, G_positive_polynomial, rhoCoordinate_polynomial]
  simp

theorem interiorPowerSeriesMatrix_det_constantCoeff :
    PowerSeries.constantCoeff interiorPowerSeriesMatrix.det = (6 : ℚ) ^ 10 := by
  rw [RingHom.map_det, interiorPowerSeriesMatrix_constantCoeff, constantCoefficientMatrix_det]

theorem interiorPowerSeriesMatrix_det_ne_zero : interiorPowerSeriesMatrix.det ≠ 0 := by
  intro h
  have hc := interiorPowerSeriesMatrix_det_constantCoeff
  rw [h, map_zero] at hc
  norm_num at hc

/-- The matrix of actual formal images of Gamma_1,...,Gamma_5. -/
def interiorMellinMatrix : Matrix (Fin 5) (Fin 5) LS :=
  fun r c => mellinSeries r ((c.val : ℤ) + 1) zeroExponent

theorem interiorMellinMatrix_eq_map :
    interiorMellinMatrix =
      (algebraMap (PowerSeries ℚ) LS).mapMatrix interiorPowerSeriesMatrix := by
  ext r c
  simp [interiorMellinMatrix, interiorPowerSeriesMatrix, mellinSeries,
    seriesOfSequence, zeroExponent]

theorem interiorMellinMatrix_det_ne_zero : interiorMellinMatrix.det ≠ 0 := by
  rw [interiorMellinMatrix_eq_map, ← RingHom.map_det]
  intro h
  apply interiorPowerSeriesMatrix_det_ne_zero
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
  simpa only [LaurentSeries.coe_algebraMap, map_zero] using h

/-- Independence concerns the actual constructed formal images; it is not
an assumed functional or a claim that quotient descent is already supplied. -/
theorem interiorMellinMatrix_columns_independent :
    LinearIndependent LS
      (fun c : Fin 5 => fun r : Fin 5 =>
        mellinSeries r ((c.val : ℤ) + 1) zeroExponent) := by
  change LinearIndependent LS interiorMellinMatrix.col
  exact Matrix.linearIndependent_cols_of_det_ne_zero interiorMellinMatrix_det_ne_zero

end MellinFactors
end WPResidueQuotient
