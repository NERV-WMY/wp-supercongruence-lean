import WPFiniteCarry.EvenLogLift
import WPFiniteCarry.FiniteProduct

open scoped Polynomial BigOperators
open Polynomial WPActualEvenLogCarry WPActualNativeHasse WPActualRankTwoLegendreField
  WPActualRankTwoHatLift WPActualRankTwoCarryField WPPIntegralReduction

namespace WPFiniteCarry

set_option maxHeartbeats 800000

/-- The literal rational central-binomial logarithm L(q). -/
noncomputable def rationalCentralLog (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else centralCoefficient ℚ r / (2 * (r : ℚ)))

/-- The complete literal next logarithmic carry E_L(q), before reduction. -/
noncomputable def rationalSecondLog (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else
      centralCoefficient ℚ r * oddHarmonicQ r / (2 * (r : ℚ)))

noncomputable def integralCentralLog (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else
      centralCoefficientIntegral p r * smallIntegralInverse p (2 * r))

noncomputable def integralSecondLog (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else
      centralOddIntegral p r * smallIntegralInverse p (2 * r))

noncomputable def integralLogRemainder (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else logCoefficientRemainder p r)

theorem integralCentralLog_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralCentralLog p).map (integralRationals p).subtype = rationalCentralLog p := by
  ext r
  rw [coeff_map, integralCentralLog, rationalCentralLog,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs with hr hr0
  · exact map_zero _
  · have hN := prime_half_identity p (by omega : 7 ≤ p)
    change (centralLogCoefficientIntegral p r).val = _
    exact centralLogCoefficientIntegral_value p r hp (by omega) (by omega)
  · exact map_zero _

theorem integralSecondLog_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralSecondLog p).map (integralRationals p).subtype = rationalSecondLog p := by
  ext r
  rw [coeff_map, integralSecondLog, rationalSecondLog,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs with hr hr0
  · exact map_zero _
  · have hN := prime_half_identity p (by omega : 7 ≤ p)
    change (centralOddIntegral p r).val * (smallIntegralInverse p (2 * r)).val = _
    rw [centralOddIntegral_value p r hp (by omega),
      smallIntegralInverse_value p (2 * r) (by omega) (by omega)]
    push_cast
    ring
  · exact map_zero _

theorem rationalCentralLog_origin (p : ℕ) : (rationalCentralLog p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, rationalCentralLog, rankCoefficientPolynomial_coeff]
  simp

theorem rationalSecondLog_origin (p : ℕ) : (rationalSecondLog p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, rationalSecondLog, rankCoefficientPolynomial_coeff]
  simp

theorem rationalSecondLog_degree (p : ℕ) :
    (rationalSecondLog p).natDegree ≤ (p - 1) / 2 := rankCoefficientPolynomial_degree _ _

/-- Exact polynomial first Taylor expansion, including a specified integral p^2 error. -/
theorem rationalBinomialLog_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rationalBinomialLog ((p - 1) / 2) = rationalCentralLog p -
      C (p : ℚ) * rationalSecondLog p +
      C ((p : ℚ) ^ 2) * (integralLogRemainder p).map (integralRationals p).subtype := by
  ext r
  rw [coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_map,
    rationalBinomialLog, rationalCentralLog, rationalSecondLog, integralLogRemainder,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs with hr hr0
  · simp
  · exact signedChooseQ_div_firstTaylor p r hp (by omega) (by omega)
  · simp

/-- Full next-digit lift NC81a in characteristic zero; no endpoint is assigned. -/
theorem actual_rational_evenLog_nextCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rationalEvenLog p + C (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) =
      (rationalCentralLog p).comp (1 - X ^ 2) +
      C (p : ℚ) * (C (actualEvenLogEndpointCarry p) -
        (rationalSecondLog p).comp (1 - X ^ 2)) +
      C ((p : ℚ) ^ 2) *
        ((integralLogRemainder p).map (integralRationals p).subtype).comp (1 - X ^ 2) := by
  rw [actual_rational_evenLog_binomial p (by omega), rationalBinomialLog_firstTaylor p hp]
  simp only [add_comp, sub_comp, mul_comp, C_comp]
  have h := congrArg (C : ℚ → ℚ[X]) (actualEvenLogEndpointCarry_source p)
  simp only [map_add, map_mul] at h
  linear_combination h

/-- Actual Q division of the specified full log defect, before a residue map. -/
noncomputable def actualNextLogCarry (p : ℕ) : ℚ[X] :=
  C (1 / (p : ℚ)) * (rationalEvenLog p +
    C (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
      (rationalCentralLog p).comp (1 - X ^ 2))

noncomputable def integralNextLogCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  C (integralEvenLogEndpointCarry p hp) - (integralSecondLog p).comp (1 - X ^ 2) +
    C (p : integralRationals p) * (integralLogRemainder p).comp (1 - X ^ 2)

theorem integralNextLogCarry_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralNextLogCarry p hp).map (integralRationals p).subtype = actualNextLogCarry p := by
  have h := actual_rational_evenLog_nextCarry p hp
  have hi : C (p : ℚ) * C (1 / (p : ℚ)) = (1 : ℚ[X]) := by
    rw [← C_mul, mul_one_div_cancel (by positivity : (p : ℚ) ≠ 0), C_1]
  have hpP : C (p : ℚ) ≠ (0 : ℚ[X]) := C_ne_zero.mpr (by positivity)
  apply mul_left_cancel₀ hpP
  simp only [integralNextLogCarry, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, integralSecondLog_value p hp,
    Polynomial.map_natCast, map_natCast,
    Subring.coe_subtype, integralEvenLogEndpointCarry, actualNextLogCarry]
  simp only [map_pow, C_eq_natCast] at h hi
  linear_combination -h -
    (rationalEvenLog p + C (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
      (rationalCentralLog p).comp (1 - X ^ 2)) * hi

theorem actualNextLogCarry_coefficient_integral (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualNextLogCarry p).coeff r) := by
  rw [← integralNextLogCarry_value p hp, coeff_map]
  exact ((integralNextLogCarry p hp).coeff r).property

noncomputable def actualSecondLogField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (integralSecondLog p).map (residueHom p)

noncomputable def actualNextLogCarryField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] := (integralNextLogCarry p hp).map (residueHom p)

theorem actualNextLogCarry_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualNextLogCarryField p hp = C (actualEvenLogEndpointField p hp) -
      (actualSecondLogField p).comp (1 - X ^ 2) := by
  simp [actualNextLogCarryField, integralNextLogCarry, actualEvenLogEndpointField,
    actualSecondLogField, Polynomial.map_comp]

end WPFiniteCarry
