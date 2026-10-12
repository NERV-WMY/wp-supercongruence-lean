import WPMarkedBridge

namespace WPScalarMarkedBridge

noncomputable section

open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualNormalization

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

/-- The actual one-row residual after the constructed integral Cartier map. -/
def actualScalarResidual : ℤ_[p] :=
  lambdaGammaZp p (actual5 p hp hp7 hp19
    (WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp))

theorem actual_scalar_residual_identity :
    actualScalarResidual p hp hp7 hp19 = -((p : ℤ_[p])^3) *
      (lambdaGammaZp p (actual5 p hp hp7 hp19 (gammaMarkedZp p hp)) -
        9 * (p : ℤ_[p])^2) := by
  rw [actualScalarResidual, map_sub, map_smul,
    WPOperatorIntegration.actual_integral_coordinate_law,
    WPMarkedBridge.lambdaGammaZp_sub, WPMarkedBridge.lambdaGammaZp_smul,
    WPMarkedBridge.lambdaGammaZp_smul, gammaMarkedZp_pairing]
  ring

theorem p3_neg_mul_mem_p8_iff (x : ℤ_[p]) :
    -((p : ℤ_[p])^3) * x ∈ Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p]) ↔
      x ∈ Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 3 hp0)
    calc
      (p : ℤ_[p])^3 * x = -(-((p : ℤ_[p])^3) * x) := by ring
      _ = -((p : ℤ_[p])^8 * z) := congrArg Neg.neg hz
      _ = (p : ℤ_[p])^3 * ((p : ℤ_[p])^5 * -z) := by ring
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    rw [hz]
    ring

theorem actual_scalar_residual_mem_iff_pairing :
    actualScalarResidual p hp hp7 hp19 ∈
        Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p]) ↔
      lambdaGammaZp p (actual5 p hp hp7 hp19 (gammaMarkedZp p hp)) -
        9 * (p : ℤ_[p])^2 ∈ Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) := by
  rw [actual_scalar_residual_identity]
  exact p3_neg_mul_mem_p8_iff p _

end
end WPScalarMarkedBridge
