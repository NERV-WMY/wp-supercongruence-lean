import WPOperatorIntegration.FiniteGamma
import WPCompletedCartier.ActualQuotient

noncomputable section

set_option maxHeartbeats 1600000

namespace WPOperatorIntegration

open WPResidueQuotient WPResidueQuotient.ActualCompletion
open WPCompletedCartier.ActualQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

/-- The two constructed images are the literal same range in the literal
same completed closed-exact quotient. -/
theorem actual_interior_images_eq :
    interiorQuotientImage p hp = WPResidueFrobenius.completedInteriorImage p hp := rfl

theorem actual_interior_Phi_coordinates (g : interiorQuotientImage p hp) :
    actualInteriorQuotientEquiv p hp hp7 hp19
      (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g) =
    WPResidueFrobenius.interiorPhi p hp hp7 hp19
      (actualInteriorQuotientEquiv p hp hp7 hp19 g) := by
  exact (actualInteriorQuotientEquiv_coordinates p hp hp7 hp19
    (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g)).trans
      ((WPResidueFrobenius.PhiUInterior_coordinates p hp hp7 hp19 g).trans
        (congrArg (WPResidueFrobenius.interiorPhi p hp hp7 hp19)
          (actualInteriorQuotientEquiv_coordinates p hp hp7 hp19 g).symm))

end WPOperatorIntegration
