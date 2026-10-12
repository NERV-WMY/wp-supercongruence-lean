import WPScalarMarkedBridge.ScalarResidual

namespace WPScalarMarkedBridge

noncomputable section

open WPCompletedCartier.ActualMatrix WPCompletedCartier.ActualNormalization
open WPCompletedCartier.ScalarBridge

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem pairing_mem_iff_literal_integral :
    lambdaGammaZp p (actual5 p hp hp7 hp19 (gammaMarkedZp p hp)) -
        9 * (p : ℤ_[p])^2 ∈ Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) ↔
      literalSumZp p hp - 9 * (p : ℤ_[p])^2 ∈
        Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) := by
  let I : Ideal ℤ_[p] := Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p])
  have hfinite := actualGamma_literal_congruence p hp hp7 hp19
  rw [WPMarkedBridge.actualGammaMatrix_mulVec] at hfinite
  constructor
  · intro hpair
    have h := I.sub_mem hpair hfinite
    convert h using 1
    abel
  · intro hliteral
    have h := I.add_mem hfinite hliteral
    convert h using 1
    abel

theorem literal_integral_iff_rational :
    literalSumZp p hp - 9 * (p : ℤ_[p])^2 ∈
        Ideal.span ({(p : ℤ_[p])^5} : Set ℤ_[p]) ↔
      WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  rw [← qpCongruent_coe_iff_ideal p 5 (literalSumZp p hp) (9 * (p : ℤ_[p])^2)]
  rw [literalSumZp_coe]
  have hcast : ((9 * (p : ℤ_[p])^2 : ℤ_[p]) : ℚ_[p]) =
      ((9 * (p : ℚ)^2 : ℚ) : ℚ_[p]) := by
    have h9 : ((9 : ℤ_[p]) : ℚ_[p]) = 9 := by
      change PadicInt.Coe.ringHom (9 : ℤ_[p]) = 9
      simp only [map_ofNat]
    simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      h9, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  rw [hcast]
  exact (WPMarkedBridge.rationalCongruent_iff_qpCongruent p 5 _ _).symm

/-- This is the exact scalar residual equivalence for the original rational sum. -/
theorem actual_scalar_residual_iff_literal :
    actualScalarResidual p hp hp7 hp19 ∈
        Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p]) ↔
      WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) :=
  (actual_scalar_residual_mem_iff_pairing p hp hp7 hp19).trans
    ((pairing_mem_iff_literal_integral p hp hp7 hp19).trans
      (literal_integral_iff_rational p hp))

theorem actual_literal_of_scalar_residual
    (hres : actualScalarResidual p hp hp7 hp19 ∈
      Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p])) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) :=
  (actual_scalar_residual_iff_literal p hp hp7 hp19).mp hres

theorem actual_cleared_of_scalar_residual
    (hres : actualScalarResidual p hp hp7 hp19 ∈
      Ideal.span ({(p : ℤ_[p])^8} : Set ℤ_[p])) :
    (p : ℤ)^5 ∣ WPReview.clearedDifference p :=
  (WPReview.literal_congruence_iff p (Fact.out : p.Prime) hp).mp
    (actual_literal_of_scalar_residual p hp hp7 hp19 hres)

end
end WPScalarMarkedBridge
