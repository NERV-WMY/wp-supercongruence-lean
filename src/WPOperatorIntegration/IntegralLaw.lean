import WPOperatorIntegration.Limit
import WPOperatorIntegration.QuotientCompatibility
import WPOperatorIntegration.IntegralConsequences

noncomputable section

set_option maxHeartbeats 1600000

namespace WPOperatorIntegration

open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.ActualCompletion
open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

/-- The constructed integral matrices satisfy the literal product law. -/
theorem actual_integral_matrix_law :
    actualGammaMatrix p hp hp7 hp19 *
      WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 =
        (p : ℤ_[p])^5 • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p]) := by
  apply integral_matrix_of_Qp_columns p
  intro j
  have h := actual_gamma_column_law p hp hp7 hp19 j
  change Matrix.mulVec ((fun i k =>
    (actualGammaMatrix p hp hp7 hp19 i k : ℚ_[p])) : Matrix (Fin 5) (Fin 5) ℚ_[p])
      (fun k => (WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 k j : ℚ_[p])) =
        (p : ℚ_[p])^5 • Pi.single j (1 : ℚ_[p]) at h
  simpa only [PadicInt.coe_pow, PadicInt.coe_natCast] using h

theorem actual_integral_coordinate_law (v : Fin 5 → ℤ_[p]) :
    actual5 p hp hp7 hp19 (WPResidueFrobenius.interiorPhi p hp hp7 hp19 v) =
      (p : ℤ_[p])^5 • v :=
  coordinate_law_of_matrix_product p hp hp7 hp19
    (actual_integral_matrix_law p hp hp7 hp19) v

/-- The law on the same actual completed interior quotient image. -/
theorem actual_cartier_frobenius (g : interiorQuotientImage p hp) :
    actualInteriorQuotientOperator p hp hp7 hp19
      (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g) =
        (p : ℤ_[p])^5 • g :=
  quotient_law_of_matrix_product p hp hp7 hp19
    (actual_integral_matrix_law p hp hp7 hp19) g

theorem actual_cartier_frobenius_linear :
    (actualInteriorQuotientOperator p hp hp7 hp19).comp
      (WPResidueFrobenius.PhiUInterior p hp hp7 hp19) =
        (p : ℤ_[p])^5 • LinearMap.id := by
  apply LinearMap.ext
  intro g
  change actualInteriorQuotientOperator p hp hp7 hp19
    (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g) = (p : ℤ_[p])^5 • g
  exact actual_cartier_frobenius p hp hp7 hp19 g

end WPOperatorIntegration
