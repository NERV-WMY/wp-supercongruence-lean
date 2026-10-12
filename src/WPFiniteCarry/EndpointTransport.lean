import WPFiniteCarry.ActualCB
import WPFiniteCarry.ResidueTransport
import WPActualNativeJacobiJet
import WPActualCentralNativeJet

open scoped Polynomial BigOperators
open Polynomial WPActualRankTwoHatLift WPActualPullbackSource
  WPActualRankTwoLegendreField WPPIntegralReduction

namespace WPFiniteCarry

set_option maxHeartbeats 1000000

/-- The literal Euler primitive of the actual rational low square F. -/
noncomputable def actualLowEulerPrimitive (p : ℕ) : ℚ[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun r => if r = 0 then 0 else (actualLowF p).coeff r / (r : ℚ))

noncomputable def integralLowEulerPrimitive (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun r => if r = 0 then 0 else
      (integralLowF p hp).coeff r * smallIntegralInverse p r)

theorem integralLowEulerPrimitive_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralLowEulerPrimitive p hp).map (integralRationals p).subtype =
      actualLowEulerPrimitive p := by
  ext r
  rw [coeff_map, integralLowEulerPrimitive, actualLowEulerPrimitive,
    rankCoefficientPolynomial_coeff, rankCoefficientPolynomial_coeff]
  split_ifs with hr hr0
  · exact map_zero _
  · have hv := congrArg (fun P : ℚ[X] => P.coeff r) (integralLowF_value p hp)
    rw [coeff_map] at hv
    rw [map_mul, hv,
      show (integralRationals p).subtype (smallIntegralInverse p r) = 1 / (r : ℚ)
        from smallIntegralInverse_value p r (by omega) (by omega)]
    ring
  · exact map_zero _

theorem actualLowEulerPrimitive_origin (p : ℕ) :
    (actualLowEulerPrimitive p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, actualLowEulerPrimitive, rankCoefficientPolynomial_coeff]
  simp

theorem actualLowEulerPrimitive_source (p : ℕ) (hp : 19 ≤ p) :
    X * (actualLowEulerPrimitive p).derivative = actualLowF p - 1 := by
  ext r
  rw [← WPActualNativeHasse.theta, WPActualNativeHasse.theta_coeff, coeff_sub, coeff_one]
  cases r with
  | zero =>
    have hf0 : (actualLowF p).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, actualLowF_origin p hp]
    simp [hf0]
  | succ r =>
    rw [actualLowEulerPrimitive, rankCoefficientPolynomial_coeff]
    by_cases hr : r + 1 < p / 6 + 1
    · rw [if_pos hr, if_neg (by omega : r + 1 ≠ 0)]
      simp only [Nat.succ_ne_zero, if_false, sub_zero]
      calc
        _ = ((r + 1 : ℕ) : ℚ) *
            ((actualLowF p).coeff (r + 1) / ((r + 1 : ℕ) : ℚ)) := by ring
        _ = _ := mul_div_cancel₀ _ (by positivity : ((r + 1 : ℕ) : ℚ) ≠ 0)
    · rw [if_neg hr, coeff_eq_zero_of_natDegree_lt
        ((actualLowF_degree p).trans_lt (by omega))]
      simp

/-- Literal NC69 normalization, before residue reduction or division. -/
noncomputable def actualLiteralR0 (p : ℕ) : ℚ :=
  -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) -
    (3 / 2 : ℚ) * ((WPFiniteInversion.integerFermatQuotient p 3 : ℚ) +
      (WPFiniteInversion.integerFermatQuotient p 5 : ℚ))

noncomputable def integralLiteralR0 (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -2 * (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
    3 * smallIntegralInverse p 2 *
      ((WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p) +
        (WPFiniteInversion.integerFermatQuotient p 5 : integralRationals p))

theorem integralLiteralR0_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralLiteralR0 p).val = actualLiteralR0 p := by
  change (integralRationals p).subtype (integralLiteralR0 p) = _
  simp only [integralLiteralR0, map_sub, map_mul, map_add, map_neg, map_ofNat, map_intCast]
  rw [show (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ)
    from smallIntegralInverse_value p 2 (by omega) (by omega)]
  unfold actualLiteralR0
  ring

/-- The actual polynomial-part coefficient, without an endpoint selection. -/
noncomputable def originalCarryCoefficient (p : ℕ) (J : ℚ[X]) : ℚ :=
  (originalPolynomialPart p J).coeff (p - 1)

theorem originalCarryCoefficient_add (p : ℕ) (J H : ℚ[X]) :
    originalCarryCoefficient p (J + H) =
      originalCarryCoefficient p J + originalCarryCoefficient p H := by
  simp only [originalCarryCoefficient, originalPolynomialPart_add, coeff_add]

theorem originalCarryCoefficient_C_mul (p : ℕ) (a : ℚ) (J : ℚ[X]) :
    originalCarryCoefficient p (C a * J) = a * originalCarryCoefficient p J := by
  simp only [originalCarryCoefficient, originalPolynomialPart_C_mul, coeff_C_mul]

theorem originalCarryCoefficient_sub (p : ℕ) (J H : ℚ[X]) :
    originalCarryCoefficient p (J - H) =
      originalCarryCoefficient p J - originalCarryCoefficient p H := by
  rw [show J - H = J + C (-1 : ℚ) * H by simp [sub_eq_add_neg],
    originalCarryCoefficient_add, originalCarryCoefficient_C_mul]
  ring

theorem originalCarryCoefficient_lowF_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalCarryCoefficient p ((actualLowF p).comp Vpolynomial) = 0 := by
  have hG : 3 * (actualLowF p).natDegree ≤ (p - 1) / 2 := by
    have hd := actualLowF_degree p
    have hN := WPActualEvenLogCarry.prime_half_identity p (by omega)
    omega
  exact residuePolynomialPart_low_coeff_zero p hp (actualLowF p) hG

/-- Actual Y Rhat transported to x, with its rational constant retained. -/
noncomputable def actualHatOriginal (p : ℕ) : ℚ[X] :=
  (actualLowF p).comp Vpolynomial *
    (C ((rationalEvenLog p).eval 1 +
      (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) - rationalHarmonic (p / 6)) +
      (rationalBinomialLog ((p - 1) / 2)).comp Vpolynomial) -
    rationalCubicPower p * actualCB p

/-- The original polynomial defining D0_p, including the entire C_B term. -/
noncomputable def actualD0Original (p : ℕ) : ℚ[X] :=
  (actualLowF p).comp Vpolynomial *
    ((rationalCentralLog p).comp Vpolynomial - C (rationalHarmonic (p / 6))) -
      (4 * X ^ p - 11) * actualCB p

/-- The original hat is the actual Y Rhat, before reduction and with the full proper term. -/
theorem actualHatOriginal_cover (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHatOriginal p).comp originalX =
      (WPActualRankTwoFirstLift.rationalLegendre (p / 6) * rationalRankHat p).comp
        originalT := by
  have hF := congrArg (fun P : ℚ[X] => P.comp originalT)
    (actualLowF_Jacobi_square p hp)
  simp only [Polynomial.comp_assoc, sub_comp, one_comp, pow_comp, X_comp] at hF
  have hlog := congrArg (fun P : ℚ[X] => P.comp originalT)
    (actual_rational_evenLog_binomial p (by omega))
  simp only [add_comp, C_comp, Polynomial.comp_assoc,
    sub_comp, one_comp, pow_comp, X_comp] at hlog
  have hCB := actualCB_original_proper_source p hp
  rw [mul_comp] at hCB
  unfold actualHatOriginal rationalRankHat
  simp only [sub_comp, mul_comp, add_comp, C_comp, pow_comp, X_comp, map_sub, map_add]
  rw [Polynomial.comp_assoc, original_V_coordinate, hF]
  rw [Polynomial.comp_assoc, original_V_coordinate,
    ← hCB]
  rw [hlog]
  ring

/-- Literal Dhat from NC79, expressed through the proved honest residue bridge. -/
noncomputable def actualDhat (p : ℕ) : ℚ :=
  2 * originalCarryCoefficient p (actualHatOriginal p) -
    (actualLowEulerPrimitive p).eval (4 / 125) / 2 - actualLiteralR0 p

/-- Literal D0_p from NC81, before the actual division by p. -/
noncomputable def actualD0 (p : ℕ) : ℚ :=
  2 * originalCarryCoefficient p (actualD0Original p) -
    (actualLowEulerPrimitive p).eval (4 / 125) / 2 - actualLiteralR0 p

noncomputable def actualDhatDivided (p : ℕ) : ℚ := actualDhat p / (p : ℚ)
noncomputable def actualD0Divided (p : ℕ) : ℚ := actualD0 p / (p : ℚ)

/-- Exact original-coordinate next-digit identity, including the p² error. -/
theorem actualHatOriginal_nextCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualHatOriginal p = actualD0Original p +
      C (p : ℚ) * ((actualLowF p).comp Vpolynomial *
        (C (actualEvenLogEndpointCarry p) - (rationalSecondLog p).comp Vpolynomial) -
          actualCubicCarry p * actualCB p) +
      C ((p : ℚ) ^ 2) * ((actualLowF p).comp Vpolynomial *
        ((integralLogRemainder p).map (integralRationals p).subtype).comp Vpolynomial) := by
  have hlog := congrArg (fun P : ℚ[X] => P.comp Vpolynomial)
    (rationalBinomialLog_firstTaylor p hp)
  simp only [sub_comp, add_comp, mul_comp, C_comp] at hlog
  have hend := congrArg (C : ℚ → ℚ[X]) (actualEvenLogEndpointCarry_source p)
  simp only [map_add, map_mul] at hend
  have hcub := actualCubicCarry_source p
  unfold actualHatOriginal actualD0Original
  simp only [map_sub, map_add]
  linear_combination (actualLowF p).comp Vpolynomial * hlog +
    (actualLowF p).comp Vpolynomial * hend - actualCB p * hcub

/-- NC79's actual hat residue, without changing its constant or Euler endpoint. -/
theorem actualDhat_origin_identity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualDhat p = -(originalOriginResidue p (actualHatOriginal p)) / 3 -
      (actualLowEulerPrimitive p).eval (4 / 125) / 2 - actualLiteralR0 p := by
  rw [original_origin_residue_polynomialPart p hp]
  unfold actualDhat originalCarryCoefficient
  ring

/-- Full characteristic-zero divided transport. Its last term records the lost next digit. -/
theorem actualDhat_divided_transport (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualDhatDivided p = actualD0Divided p -
      2 * originalCarryCoefficient p (actualCubicCarry p * actualCB p) +
      originalOriginResidue p ((actualLowF p).comp Vpolynomial *
        (rationalSecondLog p).comp Vpolynomial) / 3 -
      (p : ℚ) * originalOriginResidue p ((actualLowF p).comp Vpolynomial *
        ((integralLogRemainder p).map (integralRationals p).subtype).comp Vpolynomial) / 3 := by
  have hcoef := congrArg (originalCarryCoefficient p) (actualHatOriginal_nextCarry p hp)
  have hsplit : (actualLowF p).comp Vpolynomial *
      (C (actualEvenLogEndpointCarry p) - (rationalSecondLog p).comp Vpolynomial) =
      C (actualEvenLogEndpointCarry p) * (actualLowF p).comp Vpolynomial -
        (actualLowF p).comp Vpolynomial * (rationalSecondLog p).comp Vpolynomial := by ring
  rw [hsplit] at hcoef
  simp only [originalCarryCoefficient_add, originalCarryCoefficient_C_mul,
    originalCarryCoefficient_sub, originalCarryCoefficient_lowF_zero p hp,
    mul_zero, zero_sub] at hcoef
  rw [original_origin_residue_polynomialPart p hp,
    original_origin_residue_polynomialPart p hp]
  unfold actualDhatDivided actualD0Divided actualDhat actualD0 originalCarryCoefficient at *
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hp0]
  linear_combination 12 * hcoef

noncomputable def integralBinomialLog (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  integralCentralLog p - C (p : integralRationals p) * integralSecondLog p +
    C ((p : integralRationals p) ^ 2) * integralLogRemainder p

theorem integralBinomialLog_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralBinomialLog p).map (integralRationals p).subtype =
      rationalBinomialLog ((p - 1) / 2) := by
  rw [rationalBinomialLog_firstTaylor p hp]
  rw [integralBinomialLog, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    map_pow, map_natCast, integralCentralLog_value p hp, integralSecondLog_value p hp]

noncomputable def integralCubicPower (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  C (smallIntegralInverse p 5 ^ (p - 1)) * (4 * X - 11) ^ p

theorem integralCubicPower_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralCubicPower p).map (integralRationals p).subtype = rationalCubicPower p := by
  simp only [integralCubicPower, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat,
    map_pow]
  rw [show (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ)
    from smallIntegralInverse_value p 5 (by omega) (by omega), ← C_pow, one_div_pow]
  rfl

noncomputable def integralD0Original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (integralLowF p hp).comp (WPHasseIntegralTransport.integralV p (by omega)) *
    ((integralCentralLog p).comp (WPHasseIntegralTransport.integralV p (by omega)) -
      C (integralHarmonic p (p / 6))) -
    (4 * X ^ p - 11) * actualIntegralCB p hp

theorem integralD0Original_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralD0Original p hp).map (integralRationals p).subtype = actualD0Original p := by
  simp only [integralD0Original, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_comp, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, integralLowF_value p hp, integralCentralLog_value p hp,
    WPHasseIntegralTransport.integralV_map_rational, actualIntegralCB_value p hp,
    show (integralRationals p).subtype (integralHarmonic p (p / 6)) =
      rationalHarmonic (p / 6) from integralHarmonic_value p (p / 6) (by omega),
    actualD0Original]

noncomputable def integralHatOriginal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  (integralLowF p hp).comp (WPHasseIntegralTransport.integralV p (by omega)) *
    (C ((integralEvenLog p (by omega)).eval 1 +
      (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
        integralHarmonic p (p / 6)) +
      (integralBinomialLog p).comp (WPHasseIntegralTransport.integralV p (by omega))) -
    integralCubicPower p * actualIntegralCB p hp

theorem integralHatOriginal_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralHatOriginal p hp).map (integralRationals p).subtype = actualHatOriginal p := by
  have hlog : (integralRationals p).subtype ((integralEvenLog p (by omega)).eval 1) =
      (rationalEvenLog p).eval 1 := by
    rw [← eval_map_apply, integralEvenLog_value]
    rfl
  simp only [integralHatOriginal, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_comp, Polynomial.map_C, Polynomial.map_add,
    integralLowF_value p hp, WPHasseIntegralTransport.integralV_map_rational,
    integralCubicPower_value p hp, actualIntegralCB_value p hp, integralBinomialLog_value p hp,
    map_add, map_sub]
  simp only [map_intCast,
    show (integralRationals p).subtype (integralHarmonic p (p / 6)) =
      rationalHarmonic (p / 6) from integralHarmonic_value p (p / 6) (by omega),
    hlog, actualHatOriginal]
  simp only [map_add, map_sub, C_eq_intCast]

noncomputable def integralCMBase (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  (WPHasseIntegralTransport.integralV p (by omega)).eval 0

theorem integralCMBase_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralCMBase p hp).val = (4 / 125 : ℚ) := by
  change (integralRationals p).subtype
    ((WPHasseIntegralTransport.integralV p (by omega)).eval 0) = _
  rw [← eval_map_apply, WPHasseIntegralTransport.integralV_map_rational]
  norm_num [Vpolynomial]

noncomputable def integralEndpointCorrection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  -((integralLowEulerPrimitive p hp).eval (integralCMBase p hp)) * smallIntegralInverse p 2 -
    integralLiteralR0 p

theorem integralEndpointCorrection_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralEndpointCorrection p hp).val =
      -(actualLowEulerPrimitive p).eval (4 / 125) / 2 - actualLiteralR0 p := by
  have he : (integralRationals p).subtype
      ((integralLowEulerPrimitive p hp).eval (integralCMBase p hp)) =
      (actualLowEulerPrimitive p).eval (4 / 125) := by
    rw [← eval_map_apply, integralLowEulerPrimitive_value p hp]
    change (actualLowEulerPrimitive p).eval (integralCMBase p hp).val = _
    rw [integralCMBase_value p hp]
  change (integralRationals p).subtype (integralEndpointCorrection p hp) = _
  rw [integralEndpointCorrection, map_sub, map_mul, map_neg, he,
    show (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ)
      from smallIntegralInverse_value p 2 (by omega) (by omega),
    show (integralRationals p).subtype (integralLiteralR0 p) = actualLiteralR0 p
      from integralLiteralR0_value p hp]
  ring

/-- Integral representatives of the entire actual endpoint scalars before division. -/
noncomputable def integralDhat (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  2 * (integralOriginalPolynomialPart p hp (integralHatOriginal p hp)).coeff (p - 1) +
    integralEndpointCorrection p hp

noncomputable def integralD0 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  2 * (integralOriginalPolynomialPart p hp (integralD0Original p hp)).coeff (p - 1) +
    integralEndpointCorrection p hp

theorem integralDhat_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralDhat p hp).val = actualDhat p := by
  have hc := congrArg (fun P : ℚ[X] => P.coeff (p - 1))
    (integralOriginalPolynomialPart_value p hp (integralHatOriginal p hp))
  rw [coeff_map, integralHatOriginal_value p hp] at hc
  change (integralRationals p).subtype (integralDhat p hp) = _
  rw [integralDhat, map_add, map_mul, map_ofNat, hc]
  change 2 * originalCarryCoefficient p (actualHatOriginal p) +
    (integralEndpointCorrection p hp).val = _
  rw [integralEndpointCorrection_value p hp]
  unfold actualDhat
  ring

theorem integralD0_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralD0 p hp).val = actualD0 p := by
  have hc := congrArg (fun P : ℚ[X] => P.coeff (p - 1))
    (integralOriginalPolynomialPart_value p hp (integralD0Original p hp))
  rw [coeff_map, integralD0Original_value p hp] at hc
  change (integralRationals p).subtype (integralD0 p hp) = _
  rw [integralD0, map_add, map_mul, map_ofNat, hc]
  change 2 * originalCarryCoefficient p (actualD0Original p) +
    (integralEndpointCorrection p hp).val = _
  rw [integralEndpointCorrection_value p hp]
  unfold actualD0
  ring

/-- The actual rational endpoint is integral before any division or field reduction. -/
theorem actualDhat_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualDhat p) := by
  rw [← integralDhat_value p hp]
  exact (integralDhat p hp).property

theorem actualD0_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualD0 p) := by
  rw [← integralD0_value p hp]
  exact (integralD0 p hp).property

end WPFiniteCarry
