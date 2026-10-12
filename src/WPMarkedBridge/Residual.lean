import WPOperatorIntegration.IntegralLaw
import WPCompletedCartier.ActualNormalization

namespace WPMarkedBridge

noncomputable section

open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualNormalization

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem actualGammaMatrix_mulVec (v : Fin 5 → ℤ_[p]) :
    (actualGammaMatrix p hp hp7 hp19).mulVec v = actual5 p hp hp7 hp19 v := by
  change (LinearMap.toMatrix' (actual5 p hp hp7 hp19)).mulVec v = _
  exact LinearMap.toMatrix'_mulVec _ v

/-- Applying the actual Cartier operator and cancelling p^3 retains an
integral p^5 witness. The residual equation is the sole marked hypothesis. -/
theorem actual_marked_cartier_correction (e : Fin 5 → ℤ_[p])
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    actual5 p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^2 • gammaMarkedZp p hp =
        (p : ℤ_[p])^5 • (-actual5 p hp hp7 hp19 e) := by
  have hc := congrArg (actual5 p hp hp7 hp19) hres
  rw [map_sub, map_smul, map_smul,
    WPOperatorIntegration.actual_integral_coordinate_law] at hc
  ext i
  have hi := congrFun hc i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hi ⊢
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ (pow_ne_zero 3 hp0)
  calc
    (p : ℤ_[p])^3 *
        (actual5 p hp hp7 hp19 (gammaMarkedZp p hp) i -
          (p : ℤ_[p])^2 * gammaMarkedZp p hp i) =
      -((p : ℤ_[p])^5 * gammaMarkedZp p hp i -
        (p : ℤ_[p])^3 * actual5 p hp hp7 hp19 (gammaMarkedZp p hp) i) := by ring
    _ = -((p : ℤ_[p])^8 * actual5 p hp hp7 hp19 e i) := congrArg Neg.neg hi
    _ = (p : ℤ_[p])^3 * ((p : ℤ_[p])^5 * -actual5 p hp hp7 hp19 e i) := by ring

end
end WPMarkedBridge
