import WPFiniteCarry.NextLog
import WPFiniteCarry.CubicCarry
import WPActualPullbackSource

open scoped Polynomial
open Polynomial WPActualRankTwoHatLift WPActualRankTwoCarrySource
  WPActualRankTwoCarryField WPActualPullbackSource WPActualRankTwoResidueSource
  WPActualRankTwoDividedDifference WPPIntegralReduction

namespace WPFiniteCarry

set_option maxHeartbeats 800000

/-- Original x-coordinate on the retained square-root cover t^2=(x+1)/5. -/
noncomputable def originalX : ℚ[X] := 5 * X ^ 2 - 1

/-- Exact original T=t(4x-11)/5, with x=5t^2-1. -/
noncomputable def originalT : ℚ[X] := C (1 / 5 : ℚ) * X * (4 * originalX - 11)

private theorem fifth_constant : (C (1 / 5 : ℚ) : ℚ[X]) * 5 = 1 := by
  change C (1 / 5 : ℚ) * C (5 : ℚ) = 1
  rw [← C_mul]
  norm_num

theorem originalT_chebyshev : originalT = (4 * X ^ 3 - 3 * X : ℚ[X]) := by
  unfold originalT originalX
  calc
    _ = (C (1 / 5 : ℚ) * 5) * (4 * X ^ 3 - 3 * X) := by ring
    _ = _ := by rw [fifth_constant, one_mul]

theorem original_s_coordinate :
    C (1 / 5 : ℚ) * (originalX + 1) = (X ^ 2 : ℚ[X]) := by
  unfold originalX
  calc
    _ = (C (1 / 5 : ℚ) * 5) * X ^ 2 := by ring
    _ = _ := by rw [fifth_constant, one_mul]

theorem original_V_coordinate :
    Vpolynomial.comp originalX = (1 - originalT ^ 2 : ℚ[X]) := by
  simp only [Vpolynomial, mul_comp, C_comp, pow_comp, sub_comp,
    ofNat_comp, one_comp, X_comp]
  rw [originalT_chebyshev]
  unfold originalX
  have hc : (C (1 / 125 : ℚ) : ℚ[X]) * 125 = 1 := by
    change C (1 / 125 : ℚ) * C (125 : ℚ) = 1
    rw [← C_mul]
    norm_num
  calc
    _ = (C (1 / 125 : ℚ) * 125) * (1 - (4 * X ^ 3 - 3 * X) ^ 2) := by ring
    _ = _ := by rw [hc, one_mul]

theorem originalT_outer_endpoint : originalT.eval 1 = 1 := by
  rw [originalT_chebyshev]
  norm_num

theorem originalT_inner_endpoint : originalT.eval (1 / 2) = -1 := by
  rw [originalT_chebyshev]
  norm_num

theorem originalX_outer_endpoint : originalX.eval 1 = 4 := by
  norm_num [originalX]

theorem originalX_inner_endpoint : originalX.eval (1 / 2) = 1 / 4 := by
  norm_num [originalX]

/-- Whole rational next-log source in the original cover, retaining its p^2 error. -/
theorem actual_rational_evenLog_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rationalEvenLog p).comp originalT +
      C (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) =
      ((rationalCentralLog p).comp Vpolynomial).comp originalX +
      C (p : ℚ) * (C (actualEvenLogEndpointCarry p) -
        ((rationalSecondLog p).comp Vpolynomial).comp originalX) +
      C ((p : ℚ) ^ 2) *
        (((integralLogRemainder p).map (WPPIntegralReduction.integralRationals p).subtype).comp
          Vpolynomial).comp originalX := by
  have h := congrArg (fun P : ℚ[X] => P.comp originalT)
    (actual_rational_evenLog_nextCarry p hp)
  simp only [add_comp, mul_comp, sub_comp, pow_comp, one_comp, X_comp, C_comp,
    Polynomial.comp_assoc] at h ⊢
  rw [← original_V_coordinate] at h
  exact h

/-- The actual divided rank-two source under the original coordinate map. -/
theorem actualSecondCarry_original_difference (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankDividedJacobi p).comp originalT - (rationalRankHat p).comp originalT =
      C (p : ℚ) * (actualSecondCarryPolynomial p).comp originalT := by
  have h := congrArg (fun P : ℚ[X] => P.comp originalT)
    (actualSecondCarryPolynomial_source p hp)
  simpa only [sub_comp, mul_comp, C_comp] using h

/-- The imported full Jacobi source, including the low second-order error, is retained. -/
theorem actualSecondCarry_original_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPActualRankTwoGaussODE.legendreJacobi (p / 6) (actualSecondCarryPolynomial p)).comp
      originalT = (carryForcing p).comp originalT := by
  exact congrArg (fun P : ℚ[X] => P.comp originalT) (actualSecondCarryPolynomial_ODE p hp)

theorem actualSecondCarry_original_outer_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((actualSecondCarryPolynomial p).comp originalT).eval 1 =
      -actualEvenLogEndpointCarry p := by
  rw [eval_comp, originalT_outer_endpoint, actualSecondCarry_endpoint_rational p hp]

noncomputable def integralOriginalT (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  4 * X ^ 3 - 3 * X

noncomputable def originalTField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (integralOriginalT p).map (residueHom p)

theorem integralOriginalT_value (p : ℕ) [Fact p.Prime] :
    (integralOriginalT p).map (integralRationals p).subtype = originalT := by
  rw [originalT_chebyshev]
  simp [integralOriginalT]

theorem originalTField_explicit (p : ℕ) [Fact p.Prime] :
    originalTField p = (4 * X ^ 3 - 3 * X : (ZMod p)[X]) := by
  simp [originalTField, integralOriginalT]

noncomputable def integralSecondCarryOriginal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] := (integralSecondCarry p hp).comp (integralOriginalT p)

noncomputable def actualSecondCarryFieldOriginal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] := (integralSecondCarryOriginal p hp).map (residueHom p)

theorem integralSecondCarryOriginal_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralSecondCarryOriginal p hp).map (integralRationals p).subtype =
      (actualSecondCarryPolynomial p).comp originalT := by
  rw [integralSecondCarryOriginal, Polynomial.map_comp,
    integralSecondCarry_value, integralOriginalT_value]

theorem actualSecondCarry_original_coefficient_integral (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    0 ≤ padicValRat p (((actualSecondCarryPolynomial p).comp originalT).coeff r) := by
  rw [← integralSecondCarryOriginal_value p hp, coeff_map]
  exact ((integralSecondCarryOriginal p hp).coeff r).property

theorem actualSecondCarryFieldOriginal_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualSecondCarryFieldOriginal p hp = (actualSecondCarryField p hp).comp (originalTField p) := by
  simp only [actualSecondCarryFieldOriginal, integralSecondCarryOriginal,
    Polynomial.map_comp, actualSecondCarryField, originalTField]

/-- The complete integral Jacobi source is composed before the residue map. -/
theorem actualSecondCarry_original_integral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPActualRankTwoGaussODE.legendreJacobi (p / 6) (integralSecondCarry p hp)).comp
      (integralOriginalT p) = (integralCarrySource p (by omega : 7 ≤ p)).comp
        (integralOriginalT p) := by
  exact congrArg (fun P : (integralRationals p)[X] => P.comp (integralOriginalT p))
    (actualSecondCarryIntegral_source p hp)

/-- Whole original-cover field source, obtained from the actual Q-divided carry. -/
theorem actualSecondCarry_original_field_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPActualRankTwoGaussODE.legendreJacobi (p / 6) (actualSecondCarryField p hp)).comp
      (originalTField p) = (actualCarryFieldSource p (by omega : 7 ≤ p)).comp
        (originalTField p) := by
  exact congrArg (fun P : (ZMod p)[X] => P.comp (originalTField p))
    (actualSecondCarryField_source p hp)

theorem actualSecondCarry_original_field_outer_endpoint (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (actualSecondCarryFieldOriginal p hp).eval 1 = -actualEvenLogEndpointField p hp := by
  rw [actualSecondCarryFieldOriginal_value, eval_comp, originalTField_explicit]
  have he : (4 * X ^ 3 - 3 * X : (ZMod p)[X]).eval 1 = 1 := by
    norm_num
  rw [he, actualSecondCarry_endpoint_field p hp]

end WPFiniteCarry
