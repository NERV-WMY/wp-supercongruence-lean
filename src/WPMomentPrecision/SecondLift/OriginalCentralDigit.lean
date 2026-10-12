import WPMomentPrecision.SecondLift.OriginalNegativeDigit
import WPMomentPrecision.SecondLift.RationalEulerPrimitive

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualEtaPrimitive WPActualCentralResidueSource
  WPActualNativeRemainderSource WPActualNativeChiTaylor WPActualPullbackSource
  WPActualRankTwoLowTaylor WPActualRankTwoLegendreField WPPIntegralReduction WPActualPositiveResidueSource
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.NativeQSource
  WPMomentPrecision.OriginalNegativeDigit WPMomentPrecision.RationalEulerPrimitive

namespace WPMomentPrecision.OriginalCentralDigit

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- The leading central expression uses the actual rational terminating node
and the actual rational divided two-node polynomial. -/
noncomputable def actualCentralLeading : ℚ :=
  -2 * originalI p 0 (actualYUQ p) - (1 / 2 : ℚ) *
    (rationalEuler (p - 1 - p / 6) (nativeTermPolynomial p)).eval (4 / 125 : ℚ)

/-- The literal Fermat-quotient lift of NC59 is retained before division. -/
noncomputable def actualDeltaU : ℚ :=
  actualCentralLeading p - WPFirstResidue.LiteralNormalization.literalR0 p

noncomputable def actualCentralCorrection : ℚ :=
  6 * originalI p 0 (actualU2Q p) +
    (rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ)

noncomputable def integralActualCentralCorrection (hp : 19 ≤ p) : integralRationals p :=
  6 * integralOriginalI p hp 0 (integralActualU2Q p hp) +
    integralEulerValue p (p - 1 - p / 6) hp (by omega) (integralActualYUQ p hp)

theorem integralActualCentralCorrection_value (hp : 19 ≤ p) :
    (integralActualCentralCorrection p hp).val = actualCentralCorrection p := by
  change 6 * (integralOriginalI p hp 0 (integralActualU2Q p hp)).val +
    (integralEulerValue p (p - 1 - p / 6) hp (by omega) (integralActualYUQ p hp)).val = _
  rw [integralEulerValue_value]
  change 6 * originalI p 0 ((integralActualU2Q p hp).map (integralRationals p).subtype) +
    (rationalEuler (p - 1 - p / 6)
      ((integralActualYUQ p hp).map (integralRationals p).subtype)).eval (4 / 125 : ℚ) = _
  rw [integralActualU2Q_value, integralActualYUQ_value]
  rfl

theorem actual_log_I0_integral_split (hp : 19 ≤ p) :
    originalI p 0 (actualLogQ p) = (p : ℚ) *
      (integralOriginalI p hp 0 (integralActualUpperLogQ p hp)).val := by
  rw [actual_log_q_integral_split p hp, originalI_add, originalI_C_mul, actualLowLogQ,
    originalI_low_zero p 0 (p / 6) hp _ (WPActualNativeSecondTaylor.coefficientPolynomial_degree _ _)
      (by have := actual_third_cutoff p (by omega); simpa using this), zero_add]
  rfl

omit [Fact p.Prime] in
theorem actual_central_original_formula (hp : 19 ≤ p) :
    WPFirstResidue.LiteralNormalization.actualFirstResidue p =
      -(1 / 2 : ℚ) * (Hpolynomial (p - 1 - p / 6)).eval (4 / 125 : ℚ) -
        (1 / (p : ℚ)) * originalI p 0 (WPReview.nativePolynomial (p - p / 6)) := by
  rw [WPFirstResidue.LiteralNormalization.actualFirstResidue,
    actual_central_residue_formula, actual_HX_constant]
  unfold originalI
  simp only [Nat.cast_zero, zero_mul, neg_zero, zero_sub]
  rw [Fpull, show p - 1 - p / 6 + 1 = p - p / 6 by
    have := Nat.div_mul_le_self p 6; omega]

/-- The central residue through p² is extracted from the same full q source
as the negative resonance. Every omitted contribution is displayed in an
integral p² error, including the upper logarithmic coefficients. -/
theorem actual_central_leading_source (hp : 19 ≤ p) :
    ∃ R : integralRationals p,
      WPFirstResidue.LiteralNormalization.actualFirstResidue p =
        actualCentralLeading p - (p : ℚ) * actualCentralCorrection p + (p : ℚ) ^ 2 * R.val := by
  obtain ⟨E, hE⟩ := actual_full_q_expansion p hp
  let e := p - 1 - p / 6
  let c72 : integralRationals p := 5 * integralSeventyTwoInverse p hp
  let C2 : (integralRationals p)[X] :=
    Polynomial.C (6 : integralRationals p) * integralActualU2Q p hp +
      Polynomial.C c72 * integralActualLogQ p hp
  let IH := integralOriginalI p hp 0 (integralActualUpperLogQ p hp)
  let IE := integralOriginalI p hp 0 E
  let HC := integralEulerValue p e hp (by dsimp [e]; omega) C2
  let HE := integralEulerValue p e hp (by dsimp [e]; omega) E
  let R : integralRationals p := -c72 * IH - IE - integralHalf p (by omega) * HC -
    (p : integralRationals p) * integralHalf p (by omega) * HE
  have hc72 : c72.val = (5 / 72 : ℚ) := by
    change 5 * (1 / 72 : ℚ) = 5 / 72
    ring
  have hC2 : C2.map (integralRationals p).subtype =
      Polynomial.C (6 : ℚ) * actualU2Q p + Polynomial.C (5 / 72 : ℚ) * actualLogQ p := by
    simp only [C2, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      map_ofNat, Polynomial.map_ofNat, integralActualU2Q_value, integralActualLogQ_value]
    change Polynomial.C (6 : ℚ) * actualU2Q p + Polynomial.C c72.val * actualLogQ p = _
    rw [hc72]
    rw [Polynomial.C_ofNat 6]
  have hH : (Hpolynomial e).eval (4 / 125 : ℚ) =
      (rationalEuler e (nativeTermPolynomial p)).eval (4 / 125 : ℚ) +
        2 * (p : ℚ) * (rationalEuler e (actualYUQ p)).eval (4 / 125 : ℚ) +
        (p : ℚ) ^ 2 * HC.val + (p : ℚ) ^ 3 * HE.val := by
    rw [actual_Hpolynomial_Euler,
      show e + 1 = p - p / 6 by dsimp [e]; have := Nat.div_mul_le_self p 6; omega,
      hE]
    rw [rationalEuler_add, rationalEuler_add, rationalEuler_add,
      rationalEuler_C_mul, rationalEuler_C_mul, rationalEuler_C_mul]
    simp only [eval_add, eval_mul, eval_C]
    rw [show HC.val = (rationalEuler e (C2.map (integralRationals p).subtype)).eval
      (4 / 125 : ℚ) from integralEulerValue_value p e hp (by dsimp [e]; omega) C2,
      hC2]
    rw [show HE.val = (rationalEuler e (E.map (integralRationals p).subtype)).eval
      (4 / 125 : ℚ) from integralEulerValue_value p e hp (by dsimp [e]; omega) E]
  have hI : originalI p 0 (WPReview.nativePolynomial (p - p / 6)) =
      2 * (p : ℚ) * originalI p 0 (actualYUQ p) +
        (p : ℚ) ^ 2 * (6 * originalI p 0 (actualU2Q p) +
          (5 / 72 : ℚ) * originalI p 0 (actualLogQ p)) + (p : ℚ) ^ 3 * IE.val := by
    rw [hE, originalI_add, originalI_add, originalI_add,
      originalI_C_mul, originalI_C_mul, originalI_add, originalI_C_mul,
      originalI_C_mul, originalI_C_mul,
      originalI_low_zero p 0 (p / 6) hp _ (nativeTermPolynomial_degree p (by omega))
        (by have := actual_third_cutoff p (by omega); simpa using this), zero_add]
    rfl
  refine ⟨R, ?_⟩
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [actual_central_original_formula p hp, hH, hI, actual_log_I0_integral_split p hp]
  change _ = (-2 * originalI p 0 (actualYUQ p) - (1 / 2 : ℚ) *
      (rationalEuler e (nativeTermPolynomial p)).eval (4 / 125 : ℚ)) -
    (p : ℚ) * (6 * originalI p 0 (actualU2Q p) +
      (rationalEuler e (actualYUQ p)).eval (4 / 125 : ℚ)) +
    (p : ℚ) ^ 2 * (-c72.val * IH.val - IE.val - (1 / 2 : ℚ) * HC.val -
      (p : ℚ) * (1 / 2 : ℚ) * HE.val)
  rw [hc72]
  field_simp [hpq]
  ring

theorem actual_rho_DeltaU_source (hp : 19 ≤ p) :
    ∃ R : integralRationals p,
      WPFirstResidue.actualRho p = actualDeltaU p / (p : ℚ) -
        actualCentralCorrection p + (p : ℚ) * R.val := by
  obtain ⟨R, hR⟩ := actual_central_leading_source p hp
  refine ⟨R, ?_⟩
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [WPFirstResidue.actualRho, hR, actualDeltaU]
  field_simp [hpq]
  ring

/-- Delta_U is divided only after its literal NC59 lift has been attached.
Its integrality follows from the actual central digit and the integral source. -/
theorem actual_DeltaU_divided_integral (hp : 19 ≤ p) :
    actualDeltaU p / (p : ℚ) ∈ integralRationals p := by
  obtain ⟨R, hR⟩ := actual_rho_DeltaU_source p hp
  have he : actualDeltaU p / (p : ℚ) = WPFirstResidue.actualRho p +
      (integralActualCentralCorrection p hp).val - (p : ℚ) * R.val := by
    rw [integralActualCentralCorrection_value]
    linear_combination -hR
  rw [he]
  exact (WPFirstResidue.integralActualRho p hp + integralActualCentralCorrection p hp -
    (p : integralRationals p) * R).property

/-- IR29's rho equation uses the genuine Q-divided Delta_U and the original
U² and logarithmic primitive contributions. -/
theorem actual_rho_DeltaU_field (hp : 19 ≤ p) :
    ((WPFirstResidue.actualRho p : ℚ) : ZMod p) =
      ((actualDeltaU p / (p : ℚ) : ℚ) : ZMod p) -
        6 * ((originalI p 0 (actualU2Q p) : ℚ) : ZMod p) -
        (((rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) := by
  obtain ⟨R, hR⟩ := actual_rho_DeltaU_source p hp
  let DU : integralRationals p := ⟨actualDeltaU p / (p : ℚ), actual_DeltaU_divided_integral p hp⟩
  let IU := integralOriginalI p hp 0 (integralActualU2Q p hp)
  let HY := integralEulerValue p (p - 1 - p / 6) hp (by omega) (integralActualYUQ p hp)
  have hIU : IU.val = originalI p 0 (actualU2Q p) := by
    change originalI p 0 ((integralActualU2Q p hp).map (integralRationals p).subtype) = _
    rw [integralActualU2Q_value]
  have hHY : HY.val = (rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ) := by
    rw [show HY.val = (rationalEuler (p - 1 - p / 6)
      ((integralActualYUQ p hp).map (integralRationals p).subtype)).eval (4 / 125 : ℚ)
      from integralEulerValue_value p _ hp (by omega) _, integralActualYUQ_value]
  have hmodel : WPFirstResidue.integralActualRho p hp = DU - 6 * IU - HY +
      (p : integralRationals p) * R := by
    apply Subtype.ext
    change WPFirstResidue.actualRho p = actualDeltaU p / (p : ℚ) - 6 * IU.val -
      HY.val + (p : ℚ) * R.val
    rw [hIU, hHY]
    dsimp only [actualCentralCorrection] at hR
    linear_combination hR
  have h := congrArg (residueHom p) hmodel
  simp only [map_add, map_sub, map_mul, map_ofNat, map_natCast, ZMod.natCast_self,
    zero_mul, add_zero] at h
  change ((WPFirstResidue.actualRho p : ℚ) : ZMod p) =
    ((actualDeltaU p / (p : ℚ) : ℚ) : ZMod p) -
      6 * ((IU.val : ℚ) : ZMod p) - ((HY.val : ℚ) : ZMod p) at h
  simpa only [hIU, hHY] using h

/-- The complete original negative group retains the logarithmic cross
contribution until the separate actual H_J endpoint attachment. -/
theorem actual_negative_group_source (hp : 19 ≤ p) :
    2 * ((WPFirstResidue.actualRho p : ℚ) : ZMod p) +
        (5 / 4 : ZMod p) *
          ((WPMomentPrecision.ResonanceDigits.actualResonanceDigit p (-1) : ℚ) : ZMod p) =
      2 * ((actualDeltaU p / (p : ℚ) : ℚ) : ZMod p) -
        12 * ((originalI p 0 (actualU2Q p) : ℚ) : ZMod p) -
        2 * (((rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) -
        (15 / 2 : ZMod p) * ((originalI p 1 (actualU2Q p) : ℚ) : ZMod p) := by
  rw [actual_rho_DeltaU_field p hp, actual_negative_digit_U2_field p hp]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  field_simp [h2, h4]
  ring

end WPMomentPrecision.OriginalCentralDigit
