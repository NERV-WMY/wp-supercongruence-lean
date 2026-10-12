import WPActualEvenLogCarry

open scoped Polynomial BigOperators
open Polynomial WPActualEvenLogCarry WPActualRankTwoLegendreField
  WPActualNativeHasse WPActualRankTwoHatLift WPActualRankTwoCarrySource
  WPActualRankTwoCarryField WPPIntegralReduction

namespace WPFiniteCarry

set_option maxHeartbeats 800000

noncomputable def rationalBinomialLog (N : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial N
    (fun r => if r = 0 then 0 else (-1 : ℚ) ^ r * (N.choose r : ℚ) / (2 * (r : ℚ)))

theorem rationalBinomialLog_origin (N : ℕ) : (rationalBinomialLog N).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, rationalBinomialLog, rankCoefficientPolynomial_coeff]
  simp

theorem rationalBinomialLog_source (N : ℕ) :
    2 * theta (rationalBinomialLog N) = (1 - X) ^ N - 1 := by
  ext r
  rw [coeff_ofNat_mul, theta_coeff, coeff_sub, coeff_one_sub_X_pow, coeff_one]
  cases r with
  | zero => simp
  | succ r =>
    rw [rationalBinomialLog, rankCoefficientPolynomial_coeff]
    simp only [Nat.lt_succ_iff]
    by_cases hr : r + 1 ≤ N
    · rw [if_pos hr]
      simp only [if_neg (by omega : r + 1 ≠ 0), sub_zero]
      have hu : (2 : ℚ) * ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      calc
        _ = (2 * ((r + 1 : ℕ) : ℚ)) *
            (((-1 : ℚ) ^ (r + 1) * (N.choose (r + 1) : ℚ)) / (2 * ((r + 1 : ℕ) : ℚ))) := by ring
        _ = _ := mul_div_cancel₀ _ hu
    · rw [if_neg hr, Nat.choose_eq_zero_of_lt (by omega)]
      simp

theorem rationalBinomialLog_pullback_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (1 - X ^ 2) * ((rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2)).derivative =
      (X - X ^ p : ℚ[X]) := by
  have h := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2))
    (rationalBinomialLog_source ((p - 1) / 2))
  simp only [theta, mul_comp, ofNat_comp, X_comp, sub_comp, pow_comp, one_comp] at h
  have hexp : 2 * ((p - 1) / 2) = p - 1 := by have := prime_half_identity p hp; omega
  rw [show (1 - (1 - X ^ 2) : ℚ[X]) = X ^ 2 by ring, ← pow_mul, hexp] at h
  rw [derivative_comp, derivative_sub, derivative_one, derivative_X_pow]
  norm_num [map_ofNat] at h ⊢
  have hx : (X : ℚ[X]) * X ^ (p - 1) = X ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  linear_combination -X * h - hx

theorem rational_derivative_zero_one (P : ℚ[X]) (he : P.eval 1 = 0)
    (hs : P.derivative = 0) : P = 0 := by
  have hc := eq_C_of_derivative_eq_zero hs
  have hh := congrArg (fun Q : ℚ[X] => Q.eval 1) hc
  rw [he, eval_C] at hh
  rw [hc, ← hh, C_0]

/-- The rational even-log identity keeps its actual endpoint before any residue map. -/
theorem actual_rational_evenLog_binomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rationalEvenLog p = C ((rationalEvenLog p).eval 1) +
      (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) := by
  let D := rationalEvenLog p - C ((rationalEvenLog p).eval 1) -
    (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2)
  have hq : (1 - X ^ 2 : ℚ[X]) ≠ 0 := by
    intro hz
    have h := congrArg (fun P : ℚ[X] => P.eval 0) hz
    norm_num at h
  have hs : D.derivative = 0 := by
    have hh : (1 - X ^ 2) * D.derivative = 0 := by
      dsimp only [D]
      rw [derivative_sub, derivative_sub, derivative_C]
      linear_combination rationalEvenLog_source p hp - rationalBinomialLog_pullback_source p hp
    exact (mul_eq_zero.mp hh).resolve_left hq
  have he : D.eval 1 = 0 := by
    simp only [D, eval_sub, eval_C, eval_comp, eval_sub, eval_one, eval_pow,
      eval_X, one_pow, sub_self, rationalBinomialLog_origin]
  have hz := rational_derivative_zero_one D he hs
  dsimp only [D] at hz
  linear_combination hz

/-- NC81's endpoint carry is the literal Q division, never an assigned field value. -/
noncomputable def actualEvenLogEndpointCarry (p : ℕ) : ℚ :=
  ((rationalEvenLog p).eval 1 + (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)) / (p : ℚ)

theorem actualEvenLogEndpointCarry_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualEvenLogEndpointCarry p) := by
  have hv := congrArg (fun P : ℚ[X] => P.eval 1) (integralSecondCarry_value p hp)
  change ((integralSecondCarry p hp).map (integralRationals p).subtype).eval
    ((integralRationals p).subtype 1) = _ at hv
  rw [eval_map_apply] at hv
  have hs := actualSecondCarryPolynomial_endpoint_one p hp
  have he : actualEvenLogEndpointCarry p = -((integralSecondCarry p hp).eval 1).val := by
    change actualEvenLogEndpointCarry p =
      -(integralRationals p).subtype ((integralSecondCarry p hp).eval 1)
    rw [hv]
    unfold actualEvenLogEndpointCarry
    rw [hs]
    ring
  rw [he]
  exact (integralRationals p).neg_mem ((integralSecondCarry p hp).eval 1).property


/-- Integral representative of the actual divided endpoint, formed in Q first. -/
noncomputable def integralEvenLogEndpointCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  ⟨actualEvenLogEndpointCarry p, actualEvenLogEndpointCarry_integral p hp⟩

noncomputable def actualEvenLogEndpointField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ZMod p :=
  residueHom p (integralEvenLogEndpointCarry p hp)

theorem actualEvenLogEndpointCarry_source (p : ℕ) [Fact p.Prime] :
    (rationalEvenLog p).eval 1 + (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) =
      (p : ℚ) * actualEvenLogEndpointCarry p := by
  unfold actualEvenLogEndpointCarry
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact (mul_div_cancel₀ _ hp0).symm

theorem actualSecondCarry_endpoint_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSecondCarryPolynomial p).eval 1 = -actualEvenLogEndpointCarry p := by
  rw [actualSecondCarryPolynomial_endpoint_one p hp]
  unfold actualEvenLogEndpointCarry
  ring

theorem actualSecondCarry_endpoint_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralSecondCarry p hp).eval 1 = -integralEvenLogEndpointCarry p hp := by
  apply Subtype.ext
  have hv := congrArg (fun P : ℚ[X] => P.eval 1) (integralSecondCarry_value p hp)
  change ((integralSecondCarry p hp).map (integralRationals p).subtype).eval
    ((integralRationals p).subtype 1) = _ at hv
  rw [eval_map_apply] at hv
  change ((integralSecondCarry p hp).eval 1).val = -actualEvenLogEndpointCarry p
  exact hv.trans (actualSecondCarry_endpoint_rational p hp)

theorem actualSecondCarry_endpoint_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSecondCarryField p hp).eval 1 = -actualEvenLogEndpointField p hp := by
  have h := congrArg (residueHom p) (actualSecondCarry_endpoint_integral p hp)
  rw [map_neg] at h
  unfold actualSecondCarryField actualEvenLogEndpointField
  rw [← (residueHom p).map_one, eval_map_apply]
  exact h

end WPFiniteCarry


