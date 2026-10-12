import WPMarkedBridge.RationalTransfer
import WPMarkedBridge.Residual

namespace WPMarkedBridge

noncomputable section

open scoped BigOperators
open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualNormalization
open WPCompletedCartier.ScalarBridge

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem lambdaGammaZp_sub (v w : Fin 5 → ℤ_[p]) :
    lambdaGammaZp p (v - w) = lambdaGammaZp p v - lambdaGammaZp p w := by
  simp only [lambdaGammaZp, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem lambdaGammaZp_smul (s : ℤ_[p]) (v : Fin 5 → ℤ_[p]) :
    lambdaGammaZp p (s • v) = s * lambdaGammaZp p v := by
  simp only [lambdaGammaZp, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actual_marked_pairing_correction (e : Fin 5 → ℤ_[p])
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    lambdaGammaZp p (actual5 p hp hp7 hp19 (gammaMarkedZp p hp)) -
      9 * (p : ℤ_[p])^2 = (p : ℤ_[p])^5 *
        lambdaGammaZp p (-actual5 p hp hp7 hp19 e) := by
  have h := congrArg (lambdaGammaZp p)
    (actual_marked_cartier_correction p hp hp7 hp19 e hres)
  rw [lambdaGammaZp_sub, lambdaGammaZp_smul, lambdaGammaZp_smul,
    gammaMarkedZp_pairing] at h
  simpa only [mul_comm ((p : ℤ_[p])^2) 9] using h

/-- The existing actual Cartier comparison supplies the literal scalar bridge. -/
theorem actual_marked_literal_integral (e : Fin 5 → ℤ_[p])
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    literalSumZp p hp - 9 * (p : ℤ_[p])^2 ∈
      Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) := by
  let I : Ideal ℤ_[p] := Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p])
  have hpair : lambdaGammaZp p
      ((actualGammaMatrix p hp hp7 hp19).mulVec (gammaMarkedZp p hp)) -
      9 * (p : ℤ_[p])^2 ∈ I := by
    rw [actualGammaMatrix_mulVec, Ideal.mem_span_singleton]
    exact ⟨lambdaGammaZp p (-actual5 p hp hp7 hp19 e),
      actual_marked_pairing_correction p hp hp7 hp19 e hres⟩
  have hfinite := actualGamma_literal_congruence p hp hp7 hp19
  have h := I.sub_mem hpair hfinite
  convert h using 1
  ring

/-- Conditional on the sole actual marked residual, this is the original
literal rational factorial sum, with no scalar or eigenline premise. -/
theorem actual_marked_literal_congruence (e : Fin 5 → ℤ_[p])
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  have h := (qpCongruent_coe_iff_ideal p 5 (literalSumZp p hp)
    (9 * (p : ℤ_[p])^2)).mpr
      (actual_marked_literal_integral p hp hp7 hp19 e hres)
  rw [literalSumZp_coe] at h
  have hcast : ((9 * (p : ℤ_[p])^2 : ℤ_[p]) : ℚ_[p]) =
      ((9 * (p : ℚ)^2 : ℚ) : ℚ_[p]) := by
    have h9 : ((9 : ℤ_[p]) : ℚ_[p]) = 9 := by
      change PadicInt.Coe.ringHom (9 : ℤ_[p]) = 9
      simp only [map_ofNat]
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      h9, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  rw [hcast] at h
  exact rationalCongruent_of_qpCongruent p 5 _ _ h

theorem actual_marked_cleared_divisibility (e : Fin 5 → ℤ_[p])
    (hres : WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
      (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    (p : ℤ)^5 ∣ WPReview.clearedDifference p :=
  (WPReview.literal_congruence_iff p (Fact.out : p.Prime) hp).mp
    (actual_marked_literal_congruence p hp hp7 hp19 e hres)

theorem actual_marked_literal_of_residual_mem
    (hres : ∃ e : Fin 5 → ℤ_[p],
      WPResidueFrobenius.interiorPhi p hp hp7 hp19 (gammaMarkedZp p hp) -
        (p : ℤ_[p])^3 • gammaMarkedZp p hp = (p : ℤ_[p])^8 • e) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  obtain ⟨e, he⟩ := hres
  exact actual_marked_literal_congruence p hp hp7 hp19 e he

end
end WPMarkedBridge
