import WPMomentPrecision.MomentDigitAlgebra
import WPMomentPrecision.ResonanceDigits
import WPMomentPrecision.CanonicalPairReduction
import WPActualCanonicalSource

open scoped BigOperators
open WPPIntegralReduction WPNativeMomentIntegrality WPActualPullbackSource
  WPActualEtaPrimitive WPActualEtaIntegration WPActualResonanceReduction
  WPMomentPrecision.BasePole WPMomentPrecision.MomentDigitAlgebra
  WPMomentPrecision.ResonanceDigits

namespace WPMomentPrecision.MomentPrecision

/-
Statement fidelity: NC68--NC69 use the original native cutoff e=p-1-p/6,
N=(p-1)/2, the full actual residues at -1,0,1,2, the canonical two-endpoint
period and the actual base and coupled endpoint pole. The exact NC64 theorem
is the source identity; the checked SB7/SB9 and full resonance kernels supply
the required precisions. `actualU` divides no residue: it is the rational
lift (625/216)*canonicalPeriod. The retained literal cutoff theorem attaches
the full polynomial F_p. The exports require only a prime p>=19, with no
caller-supplied source, value or precision input. No equality R_p-U_p=P_p
is asserted. Human acceptance remains Pending. This helper source has no
executable check of its own; the package owner is the sole emitter.
-/

noncomputable def actualP (p : ℕ) : ℚ :=
  arithmeticDigit (fermatQ p 2) (fermatQ p 3) (fermatQ p 5) (actualAlpha p)

noncomputable def actualR (p : ℕ) : ℚ :=
  resonanceDigit (WPFirstResidue.actualRho p) (actualResonanceDigit p (-1))
    (actualResonanceDigit p 1) (actualResonanceDigit p 2)

/-- The canonical NC67 lift uses the whole original signed period. -/
noncomputable def actualU (p : ℕ) : ℚ :=
  (625 / 216) * canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6)

noncomputable def actualBaseTarget (p : ℕ) : ℚ :=
  baseNormalizer * (1 + (p : ℚ) * baseFirstCoefficient (fermatQ p 2) (fermatQ p 5) +
    (p : ℚ) ^ 2 * baseSecondCoefficient (fermatQ p 2) (fermatQ p 5) (actualAlpha p))

def actualPoleTarget (p : ℕ) : ℚ :=
  poleFirstCoefficient (fermatQ p 2) +
    (p : ℚ) * poleSecondCoefficient (fermatQ p 2) (fermatQ p 3) (fermatQ p 5)

noncomputable def actualTruncation (p : ℕ) : ℚ :=
  normalizedTruncation p (fermatQ p 2) (fermatQ p 3) (fermatQ p 5) (actualAlpha p)
    (WPFirstResidue.actualRho p) (actualResonanceDigit p (-1))
    (actualResonanceDigit p 1) (actualResonanceDigit p 2) (actualU p)

theorem actualP_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualP p) :=
  arithmeticDigit_integral p hp _ _ _ _ (fermatQ_integral p 2)
    (fermatQ_integral p 3) (fermatQ_integral p 5) (actualAlpha_integral p)

theorem actualR_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualR p) :=
  resonanceDigit_integral p hp _ _ _ _ (WPFirstResidue.actual_rho_integral p hp)
    (actual_negative_digit_integral p hp) (actual_first_positive_digit_integral p hp)
    (actual_second_positive_digit_integral p hp)

theorem canonicalNormalizer_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (625 / 216 : ℚ) := by
  let R := integralRationals p
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by norm_num) (by omega)⟩
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by norm_num) (by omega)⟩
  have h := (625 * c2 ^ 3 * c3 ^ 3).property
  change 0 ≤ padicValRat p (625 * (1 / 2 : ℚ) ^ 3 * (1 / 3) ^ 3) at h
  convert h using 1
  norm_num

theorem actualU_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (actualU p) :=
  (integralRationals p).mul_mem (canonicalNormalizer_integral p hp)
    (WPActualCanonicalSource.literal_canonicalPeriod_integral p hp)

theorem baseNormalizer_inverse_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p baseNormalizer⁻¹ := by
  let R := integralRationals p
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by norm_num) (by omega)⟩
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by norm_num) (by omega)⟩
  have h := (625 * c2 ^ 3 * c3).property
  change 0 ≤ padicValRat p (625 * (1 / 2 : ℚ) ^ 3 * (1 / 3)) at h
  convert h using 1
  norm_num [baseNormalizer]

theorem negativeNinth_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (-1 / 9 : ℚ) := by
  let R := integralRationals p
  let c3 : R := ⟨1 / 3, WPFiniteConductorPolynomial.small_inverse_integral p 3
    (by norm_num) (by omega)⟩
  have h := (-c3 ^ 2).property
  change 0 ≤ padicValRat p (-(1 / 3 : ℚ) ^ 2) at h
  convert h using 1
  norm_num

theorem resonanceMinusValue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (54 / 125 : ℚ) := by
  let R := integralRationals p
  let c5 : R := ⟨1 / 5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by norm_num) (by omega)⟩
  have h := (54 * c5 ^ 3).property
  change 0 ≤ padicValRat p (54 * (1 / 5 : ℚ) ^ 3) at h
  convert h using 1
  norm_num

theorem resonancePlusValue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (6102 / 4375 : ℚ) := by
  let R := integralRationals p
  let c5 : R := ⟨1 / 5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by norm_num) (by omega)⟩
  let c7 : R := ⟨1 / 7, WPFiniteConductorPolynomial.small_inverse_integral p 7
    (by norm_num) (by omega)⟩
  have h := (6102 * c5 ^ 4 * c7).property
  change 0 ≤ padicValRat p (6102 * (1 / 5 : ℚ) ^ 4 * (1 / 7)) at h
  convert h using 1
  norm_num

theorem resonanceTwoValue_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (28809 / 8750 : ℚ) := by
  let R := integralRationals p
  let c2 : R := ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2
    (by norm_num) (by omega)⟩
  let c5 : R := ⟨1 / 5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by norm_num) (by omega)⟩
  let c7 : R := ⟨1 / 7, WPFiniteConductorPolynomial.small_inverse_integral p 7
    (by norm_num) (by omega)⟩
  have h := (28809 * c2 * c5 ^ 4 * c7).property
  change 0 ≤ padicValRat p (28809 * (1 / 2 : ℚ) * (1 / 5) ^ 4 * (1 / 7)) at h
  convert h using 1
  norm_num

/-- The rational first digit comes from the complete original negative kernel. -/
theorem actual_resonanceMinus_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (resonancePeriod p (-1)) (54 / 125) := by
  apply (integral_residue_eq_iff p _ _
    (resonancePeriod_integral p hp (-1) (by norm_num) (by norm_num))
    (resonanceMinusValue_integral p hp)).mp
  rw [actual_resonanceMinus_residue p hp]
  norm_num [Rat.cast_def]

theorem actual_resonancePlus_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (resonancePeriod p 1) (6102 / 4375) := by
  apply (integral_residue_eq_iff p _ _
    (resonancePeriod_integral p hp 1 (by norm_num) (by norm_num))
    (resonancePlusValue_integral p hp)).mp
  rw [actual_resonancePlus_residue p hp]
  norm_num [Rat.cast_def]

theorem actual_resonanceTwo_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 1 (resonancePeriod p 2) (28809 / 8750) := by
  apply (integral_residue_eq_iff p _ _
    (resonancePeriod_integral p hp 2 (by norm_num) (by norm_num))
    (resonanceTwoValue_integral p hp)).mp
  rw [actual_resonanceTwo_residue p hp]
  norm_num [Rat.cast_def]

theorem literalR0_eq_residueBaseline (p : ℕ) :
    WPFirstResidue.LiteralNormalization.literalR0 p =
      residueBaseline (fermatQ p 2) (fermatQ p 3) (fermatQ p 5) := by
  unfold WPFirstResidue.LiteralNormalization.literalR0 residueBaseline fermatQ
  norm_num; ring

theorem actual_central_residue_exact_digit (p : ℕ) [Fact p.Prime] :
    actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 =
      residueBaseline (fermatQ p 2) (fermatQ p 3) (fermatQ p 5) +
        (p : ℚ) * WPFirstResidue.actualRho p := by
  change WPFirstResidue.LiteralNormalization.actualFirstResidue p = _
  rw [WPFirstResidue.actual_first_residue_exact_digit, literalR0_eq_residueBaseline]

theorem actual_base_target_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (WPActualMomentDefect.baseMoment p)
      (actualBaseTarget p) := by
  simpa only [actualBaseTarget, baseNormalizer, baseFirstCoefficient,
    baseSecondCoefficient] using actual_baseMoment_SB7 p hp

theorem actual_pole_target_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 2 (polePeriod p ((p - 1) / 2))
      (actualPoleTarget p) := by
  have h := actual_polePeriod_SB9 p hp
  rw [show actualPoleTarget p = (36 / 625) * fermatQ p 2 *
    (52 + (p : ℚ) * (-151 * fermatQ p 2 + 150 * fermatQ p 3 - 6 * fermatQ p 5)) by
      unfold actualPoleTarget poleFirstCoefficient poleSecondCoefficient
      ring]
  exact h

/-- Exact canonical-unit attachment; no replacement Fermat quotients are introduced. -/
theorem unitTarget_eq_actual_units (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    unitTarget p (fermatQ p 2) (fermatQ p 3) =
      (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3 := by
  have h2 := WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 := WPFiniteInversion.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  unfold unitTarget
  rw [← fermatUnit_eq p 2 (by simpa using h2),
    ← fermatUnit_eq p 3 (by simpa using h3)]

/-- All actual NC64 summands are kept until their exact scaled precision is applied. -/
theorem actual_short_truncation_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3 (actualShortMoment p (p - 1 - p / 6))
      (baseNormalizer * actualTruncation p) := by
  let R := integralRationals p
  let PP : R := ⟨p, natCast_mem R p⟩
  let r0 : R := ⟨actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0,
    actual_residue_integral p hp 0⟩
  have hC : 0 ≤ padicValRat p
      (1 - 2 * (p : ℚ) * actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0) :=
    (1 - 2 * PP * r0).property
  have hB : WPReview.RationalCongruent p 3
      ((1 - 2 * (p : ℚ) * actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0) *
        (WPActualMomentDefect.baseMoment p - actualBaseTarget p)) 0 := by
    have h := precision_mul_integral p 3 _ _ 0 hC
      ((reviewCongruent_iff_sub_zero p 3 _ _).mp
        (actual_base_target_precision p hp))
    simpa only [mul_zero] using h
  have hL := precision_prime_power_mul_integral p 2 1 (-1 / 9)
    (polePeriod p ((p - 1) / 2) - actualPoleTarget p) (negativeNinth_integral p hp)
    ((reviewCongruent_iff_sub_zero p 2 _ _).mp
      (actual_pole_target_precision p hp))
  have hm := precision_prime_power_mul_integral p 1 2
    ((-1 / 9) * actualResonanceDigit p (-1)) (resonancePeriod p (-1) - 54 / 125)
    (R.mul_mem (negativeNinth_integral p hp) (actual_negative_digit_integral p hp))
    ((reviewCongruent_iff_sub_zero p 1 _ _).mp
      (actual_resonanceMinus_precision p hp))
  have h1 := precision_prime_power_mul_integral p 1 2
    ((-1 / 9) * actualResonanceDigit p 1) (resonancePeriod p 1 - 6102 / 4375)
    (R.mul_mem (negativeNinth_integral p hp) (actual_first_positive_digit_integral p hp))
    ((reviewCongruent_iff_sub_zero p 1 _ _).mp
      (actual_resonancePlus_precision p hp))
  have h2 := precision_prime_power_mul_integral p 1 2
    ((-1 / 9) * actualResonanceDigit p 2) (resonancePeriod p 2 - 28809 / 8750)
    (R.mul_mem (negativeNinth_integral p hp) (actual_second_positive_digit_integral p hp))
    ((reviewCongruent_iff_sub_zero p 1 _ _).mp
      (actual_resonanceTwo_precision p hp))
  have hsum := reviewCongruent_zero_add p 3 _ _
    (reviewCongruent_zero_add p 3 _ _
      (reviewCongruent_zero_add p 3 _ _ (reviewCongruent_zero_add p 3 _ _ hB hL) hm) h1) h2
  apply (reviewCongruent_iff_sub_zero p 3 _ _).mpr
  rw [show actualShortMoment p (p - 1 - p / 6) - baseNormalizer * actualTruncation p =
      ((1 - 2 * (p : ℚ) * actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0) *
        (WPActualMomentDefect.baseMoment p - actualBaseTarget p) +
      (p : ℚ) ^ 1 * (-1 / 9) * (polePeriod p ((p - 1) / 2) - actualPoleTarget p)) +
      (p : ℚ) ^ 2 * ((-1 / 9) * actualResonanceDigit p (-1)) *
        (resonancePeriod p (-1) - 54 / 125) +
      (p : ℚ) ^ 2 * ((-1 / 9) * actualResonanceDigit p 1) *
        (resonancePeriod p 1 - 6102 / 4375) +
      (p : ℚ) ^ 2 * ((-1 / 9) * actualResonanceDigit p 2) *
        (resonancePeriod p 2 - 28809 / 8750) by
    rw [actual_NC64_short_moment p hp, actual_central_residue_exact_digit p,
      actual_resonance_exact_digit p (-1), actual_resonance_exact_digit p 1,
      actual_resonance_exact_digit p 2]
    unfold actualTruncation normalizedTruncation actualBaseTarget actualPoleTarget
      actualU poleFirstCoefficient poleSecondCoefficient
    norm_num only [baseNormalizer]
    ring]
  exact hsum

theorem actual_short_normalized_truncation_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      (actualShortMoment p (p - 1 - p / 6) / baseNormalizer) (actualTruncation p) := by
  have h := precision_mul_integral p 3 baseNormalizer⁻¹ _ _
    (baseNormalizer_inverse_integral p hp) (actual_short_truncation_precision p hp)
  rw [show baseNormalizer⁻¹ * actualShortMoment p (p - 1 - p / 6) =
      actualShortMoment p (p - 1 - p / 6) / baseNormalizer by
        rw [div_eq_mul_inv]
        ring,
    show baseNormalizer⁻¹ * (baseNormalizer * actualTruncation p) = actualTruncation p by
      norm_num [baseNormalizer]; ring] at h
  exact h

/-- Unconditional actual NC69 precision, with every source and precision input discharged. -/
theorem actual_short_moment_NC69_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      (actualShortMoment p (p - 1 - p / 6) / baseNormalizer -
        (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)
      ((p : ℚ) ^ 2 * (actualP p - actualR p + actualU p)) := by
  have hs := precision_add p 3 _ _ _ _ (actual_short_normalized_truncation_precision p hp)
    (Or.inl rfl : WPReview.RationalCongruent p 3
      (-((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3))
      (-((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)))
  have ht := normalizedTruncation_defect_precision p hp
    (fermatQ p 2) (fermatQ p 3) (fermatQ p 5) (actualAlpha p)
    (WPFirstResidue.actualRho p) (actualResonanceDigit p (-1))
    (actualResonanceDigit p 1) (actualResonanceDigit p 2) (actualU p)
    (fermatQ_integral p 2) (fermatQ_integral p 3) (fermatQ_integral p 5)
    (actualAlpha_integral p) (WPFirstResidue.actual_rho_integral p hp)
  rw [unitTarget_eq_actual_units p hp] at ht
  change WPReview.RationalCongruent p 3
    (actualTruncation p - (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)
    ((p : ℚ) ^ 2 * (actualP p - actualR p + actualU p)) at ht
  apply precision_trans p 3 _ _ _ _ ht
  simpa only [sub_eq_add_neg] using hs

/-- The literal full F_p cutoff retains the entire NC69 third digit. -/
theorem actual_full_native_moment_NC69_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) /
        baseNormalizer - (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)
      ((p : ℚ) ^ 2 * (actualP p - actualR p + actualU p)) := by
  have hc : WPReview.RationalCongruent p 3
      (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n)
      (actualShortMoment p (p - 1 - p / 6)) :=
    actual_full_literal_cutoff_moment_precision p (by omega)
  have hm := precision_mul_integral p 3 baseNormalizer⁻¹ _ _
    (baseNormalizer_inverse_integral p hp) hc
  have hd : WPReview.RationalCongruent p 3
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) /
        baseNormalizer) (actualShortMoment p (p - 1 - p / 6) / baseNormalizer) := by
    rw [show baseNormalizer⁻¹ *
          (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) =
        (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) /
          baseNormalizer by rw [div_eq_mul_inv]; ring,
      show baseNormalizer⁻¹ * actualShortMoment p (p - 1 - p / 6) =
        actualShortMoment p (p - 1 - p / 6) / baseNormalizer by
          rw [div_eq_mul_inv]
          ring] at hm
    exact hm
  have hs := precision_add p 3 _ _ _ _ hd
    (Or.inl rfl : WPReview.RationalCongruent p 3
      (-((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3))
      (-((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)))
  apply precision_trans p 3 _ _ _ _ (actual_short_moment_NC69_precision p hp)
  simpa only [sub_eq_add_neg] using hs

theorem actual_full_cutoff_NC69_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      (actualShortMoment p (p - 1) / baseNormalizer -
        (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3)
      ((p : ℚ) ^ 2 * (actualP p - actualR p + actualU p)) := by
  simpa only [actualShortMoment, Nat.sub_add_cancel (show 1 ≤ p by omega)] using
    actual_full_native_moment_NC69_precision p hp

/-- The rational lift reduces to the retained canonical NC77 object. -/
theorem actualU_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualU p : ZMod p) = WPMomentPrecision.ResonancePair.Up p := by
  rw [actualU, Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p _ (canonicalNormalizer_integral p hp))
    (integral_denominator_cast_ne_zero p _
      (WPActualCanonicalSource.literal_canonicalPeriod_integral p hp))]
  unfold WPMomentPrecision.ResonancePair.Up
  congr 1
  norm_num [Rat.cast_def]

theorem actual_first_positive_digit_eq (p : ℕ) [Fact p.Prime] :
    actualResonanceDigit p 1 = WPActualPositiveResidueCarry.positiveDigit p 1 := rfl

/-- Both endpoints and the original negative half remain in the NC77a pair. -/
theorem actualU_positive_pair (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualU p : ZMod p) =
      (113 / 28) * (actualResonanceDigit p 1 : ZMod p) +
        WPMomentPrecision.ResonancePair.Bpair p hp - WPMomentPrecision.ResonancePair.C0 p / 6 := by
  rw [actualU_residue p hp, actual_first_positive_digit_eq]
  exact WPMomentPrecision.ResonancePair.actual_Up_positive_pair p hp

/-- The positive source digit is removed only through the checked NC77b paired identity. -/
theorem actualU_minus_first_positive_pair (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualU p : ZMod p) - (113 / 28) * (actualResonanceDigit p 1 : ZMod p) =
      WPMomentPrecision.ResonancePair.Bpair p hp - WPMomentPrecision.ResonancePair.C0 p / 6 := by
  rw [actualU_residue p hp, actual_first_positive_digit_eq]
  exact WPMomentPrecision.ResonancePair.actual_Ubar_pair p hp

end WPMomentPrecision.MomentPrecision
