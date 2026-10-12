import WPMomentPrecision.MomentPrecision

open WPPIntegralReduction WPMomentPrecision.MomentPrecision
  WPMomentPrecision.MomentDigitAlgebra WPMomentPrecision.ResonanceDigits

namespace WPMomentPrecision.ResonanceFieldReduction

set_option maxHeartbeats 1000000

/-- Only the actual final positive digit is removed, using its complete native source. -/
theorem actual_second_positive_digit_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualResonanceDigit p 2 : ZMod p) = 0 := by
  change (WPActualPositiveResidueCarry.positiveDigit p 2 : ZMod p) = 0
  exact WPActualPositiveResidueCarry.actual_second_positive_digit p hp

/-- The rational NC69 resonance lift is reduced through the integral subring.
The denominators 28 and 112 use only the prime units 2 and 7. -/
theorem actualR_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualR p : ZMod p) = 2 * (WPFirstResidue.actualRho p : ZMod p) +
      (5 / 4) * (actualResonanceDigit p (-1) : ZMod p) +
      (113 / 28) * (actualResonanceDigit p 1 : ZMod p) +
      (1067 / 112) * (actualResonanceDigit p 2 : ZMod p) := by
  let R := integralRationals p
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by norm_num) (by omega)⟩
  let c7 : R := ⟨1 / 7, WPFiniteConductorPolynomial.small_inverse_integral p 7
    (by norm_num) (by omega)⟩
  let a : R := 5 * c2 ^ 2
  let b : R := 113 * c2 ^ 2 * c7
  let c : R := 1067 * c2 ^ 4 * c7
  have ha : a.val = (5 / 4 : ℚ) := by
    change 5 * (1 / 2 : ℚ) ^ 2 = 5 / 4
    norm_num
  have hb : b.val = (113 / 28 : ℚ) := by
    change 113 * (1 / 2 : ℚ) ^ 2 * (1 / 7 : ℚ) = 113 / 28
    norm_num
  have hc : c.val = (1067 / 112 : ℚ) := by
    change 1067 * (1 / 2 : ℚ) ^ 4 * (1 / 7 : ℚ) = 1067 / 112
    norm_num
  let rho : R := ⟨WPFirstResidue.actualRho p, WPFirstResidue.actual_rho_integral p hp⟩
  let sm : R := ⟨actualResonanceDigit p (-1), actual_negative_digit_integral p hp⟩
  let s1 : R := ⟨actualResonanceDigit p 1, actual_first_positive_digit_integral p hp⟩
  let s2 : R := ⟨actualResonanceDigit p 2, actual_second_positive_digit_integral p hp⟩
  let total : R := ⟨actualR p, actualR_integral p hp⟩
  have ht : total = 2 * rho + a * sm + b * s1 + c * s2 := by
    apply Subtype.ext
    change actualR p = 2 * WPFirstResidue.actualRho p +
      a.val * actualResonanceDigit p (-1) + b.val * actualResonanceDigit p 1 +
      c.val * actualResonanceDigit p 2
    rw [ha, hb, hc]
    rfl
  have h := congrArg (residueHom p) ht
  simp only [map_add, map_mul, map_ofNat] at h
  have hfa : residueHom p a = (5 / 4 : ZMod p) := by
    change (a.val : ZMod p) = _
    rw [ha]
    norm_num [Rat.cast_def]
  have hfb : residueHom p b = (113 / 28 : ZMod p) := by
    change (b.val : ZMod p) = _
    rw [hb]
    norm_num [Rat.cast_def]
  have hfc : residueHom p c = (1067 / 112 : ZMod p) := by
    change (c.val : ZMod p) = _
    rw [hc]
    norm_num [Rat.cast_def]
  change (actualR p : ZMod p) = 2 * (WPFirstResidue.actualRho p : ZMod p) +
    residueHom p a * (actualResonanceDigit p (-1) : ZMod p) +
    residueHom p b * (actualResonanceDigit p 1 : ZMod p) +
    residueHom p c * (actualResonanceDigit p 2 : ZMod p) at h
  simpa only [hfa, hfb, hfc] using h

/-- NC70 and the full paired NC77b identity leave exactly the two negative slots.
The central endpoint C0 remains until its actual NC77c cancellation. -/
theorem actual_R_minus_U_NC72 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualR p : ZMod p) - (actualU p : ZMod p) =
      2 * (WPFirstResidue.actualRho p : ZMod p) +
        (5 / 4) * (actualResonanceDigit p (-1) : ZMod p) -
        WPMomentPrecision.ResonancePair.Bpair p hp +
        WPMomentPrecision.ResonancePair.C0 p / 6 := by
  rw [actualR_residue p hp, actual_second_positive_digit_zero p hp,
    mul_zero, add_zero, actualU_positive_pair p hp]
  ring

noncomputable def actualDefect (p : ℕ) : ℚ := actualP p - actualR p + actualU p

theorem actualDefect_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualDefect p) :=
  (integralRationals p).add_mem
    ((integralRationals p).sub_mem (actualP_integral p hp) (actualR_integral p hp))
    (actualU_integral p hp)

/-- The actual three-digit defect has no discarded resonance or source premise. -/
theorem actualDefect_NC72_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualDefect p : ZMod p) = (actualP p : ZMod p) -
      (2 * (WPFirstResidue.actualRho p : ZMod p) +
        (5 / 4) * (actualResonanceDigit p (-1) : ZMod p) -
        WPMomentPrecision.ResonancePair.Bpair p hp +
        WPMomentPrecision.ResonancePair.C0 p / 6) := by
  rw [actualDefect, Rat.cast_add_of_ne_zero
    (integral_denominator_cast_ne_zero p _
      ((integralRationals p).sub_mem (actualP_integral p hp) (actualR_integral p hp)))
    (integral_denominator_cast_ne_zero p _ (actualU_integral p hp)),
    Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p _ (actualP_integral p hp))
      (integral_denominator_cast_ne_zero p _ (actualR_integral p hp))]
  have h := actual_R_minus_U_NC72 p hp
  linear_combination -h

end WPMomentPrecision.ResonanceFieldReduction
