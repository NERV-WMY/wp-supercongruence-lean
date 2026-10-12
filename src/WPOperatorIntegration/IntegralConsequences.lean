import WPOperatorIntegration.MatrixTransport

noncomputable section

set_option maxHeartbeats 1600000

namespace WPOperatorIntegration

open scoped BigOperators
open WPResidueQuotient WPResidueQuotient.ActualCompletion
open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem coordinate_law_of_matrix_product (hprod : actualGammaMatrix p hp hp7 hp19 * WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 = (p : ℤ_[p])^5 • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p])) (v : Fin 5 → ℤ_[p]) :
    actual5 p hp hp7 hp19 (WPResidueFrobenius.interiorPhi p hp hp7 hp19 v) =
      (p : ℤ_[p])^5 • v := by
  change actual5 p hp hp7 hp19
    ((WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19).mulVec v) = _
  rw [← LinearMap.toMatrix'_mulVec]
  change (actualGammaMatrix p hp hp7 hp19).mulVec
    ((WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19).mulVec v) = _
  rw [Matrix.mulVec_mulVec, hprod, Matrix.smul_mulVec,
    Matrix.one_mulVec]

/-- Cartier applied after the original numerical Frobenius on the actual
completed interior quotient image is multiplication by p^5. -/
theorem quotient_law_of_matrix_product (hprod : actualGammaMatrix p hp hp7 hp19 * WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 = (p : ℤ_[p])^5 • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p])) (g : interiorQuotientImage p hp) :
    actualInteriorQuotientOperator p hp hp7 hp19
      (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g) =
        (p : ℤ_[p])^5 • g := by
  apply (actualInteriorQuotientEquiv p hp hp7 hp19).injective
  calc
    actualInteriorQuotientEquiv p hp hp7 hp19
        (actualInteriorQuotientOperator p hp hp7 hp19
          (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g)) =
      actual5 p hp hp7 hp19 (actualInteriorQuotientEquiv p hp hp7 hp19
        (WPResidueFrobenius.PhiUInterior p hp hp7 hp19 g)) :=
          (actual5_interior_quotient p hp hp7 hp19 _).symm
    _ = actual5 p hp hp7 hp19 (WPResidueFrobenius.interiorPhi p hp hp7 hp19
        (actualInteriorQuotientEquiv p hp hp7 hp19 g)) :=
      congrArg (actual5 p hp hp7 hp19) (actual_interior_Phi_coordinates p hp hp7 hp19 g)
    _ = (p : ℤ_[p])^5 • actualInteriorQuotientEquiv p hp hp7 hp19 g :=
      coordinate_law_of_matrix_product p hp hp7 hp19 hprod _
    _ = actualInteriorQuotientEquiv p hp hp7 hp19 ((p : ℤ_[p])^5 • g) :=
      (map_smul (actualInteriorQuotientEquiv p hp hp7 hp19) ((p : ℤ_[p])^5) g).symm

/-- The literal T128 matrix is the raw pullback with precisely k < 123,
not a chosen approximation. Its error has an integral matrix witness. -/
theorem literal_T128_error_matrix :
    ∃ E : Matrix (Fin 5) (Fin 5) ℤ_[p],
      WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 -
        WPResidueFrobenius.gammaT128InteriorMatrix p hp hp7 hp19 =
          (p : ℤ_[p])^8 • E := by
  classical
  have h (i j : Fin 5) :=
    WPResidueFrobenius.gammaT128Matrix_mod_p8 p hp hp7 hp19 (Fin.castAdd 6 i) j
  choose E hE using h
  refine ⟨E, ?_⟩
  ext i j
  exact hE i j

theorem T128_mod_p8_of_matrix_product (hprod : actualGammaMatrix p hp hp7 hp19 * WPResidueFrobenius.gammaRawInteriorMatrix p hp hp7 hp19 = (p : ℤ_[p])^5 • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p])) :
    ∃ E : Matrix (Fin 5) (Fin 5) ℤ_[p],
      actualGammaMatrix p hp hp7 hp19 *
        WPResidueFrobenius.gammaT128InteriorMatrix p hp hp7 hp19 -
        (p : ℤ_[p])^5 • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p]) =
          (p : ℤ_[p])^8 • E := by
  obtain ⟨E, hE⟩ := literal_T128_error_matrix p hp hp7 hp19
  refine ⟨-(actualGammaMatrix p hp hp7 hp19 * E), ?_⟩
  rw [← hprod, ← Matrix.mul_sub, ← neg_sub,
    hE, Matrix.mul_neg, Matrix.mul_smul]
  simp only [smul_neg]


end WPOperatorIntegration
