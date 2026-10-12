import WPMomentPrecision.ResonanceFieldReduction
import WPMomentPrecision.SecondLift.HJetYUAttachment

open scoped BigOperators
open WPPIntegralReduction WPNativeMomentIntegrality WPMomentPrecision.BasePole
  WPMomentPrecision.MomentPrecision WPMomentPrecision.ResonanceFieldReduction
  WPMomentPrecision.OriginalNegativeDigit WPMomentPrecision.OriginalCentralDigit
  WPMomentPrecision.NativeQSource WPMomentPrecision.HJetYUAttachment

namespace WPMomentPrecision.MomentToField

set_option maxHeartbeats 1200000

/- The final field scalar is retained for the sole Assembly owner to evaluate.
The reduction below is an unconditional equivalence for the actual full moment:
all source, cutoff, denominator, resonance and precision premises are discharged.
It is not an assertion of the scalar's value or of the literal W_p congruence. -/

noncomputable def actualNC77Scalar (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  2 * ((actualDeltaU p / (p : ℚ) : ℚ) : ZMod p) -
    12 * (originalI p 0 (actualU2Q p) : ZMod p) -
    (15 / 2) * (originalI p 1 (actualU2Q p) : ZMod p) -
    WPMomentPrecision.ResonancePair.Bpair p hp

/-- The same actual H_YU endpoint occurs on both sides and cancels with its
proved normalization C0=12 H_YU, rather than by an assigned endpoint value. -/
theorem actual_R_minus_U_NC77 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualR p : ZMod p) - (WPMomentPrecision.MomentPrecision.actualU p : ZMod p) =
      actualNC77Scalar p hp := by
  rw [actual_R_minus_U_NC72 p hp, actual_negative_group_source p hp,
    actual_HJet_YU_endpoint p hp]
  unfold actualNC77Scalar
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  field_simp [h6, h2]
  ring

theorem actualDefect_NC77_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualDefect p : ZMod p) = (actualP p : ZMod p) - actualNC77Scalar p hp := by
  rw [actualDefect_NC72_field p hp]
  have h := actual_R_minus_U_NC77 p hp
  rw [actual_R_minus_U_NC72 p hp] at h
  rw [h]

theorem precision_symm (p k : ℕ) (a b : ℚ)
    (h : WPReview.RationalCongruent p k a b) : WPReview.RationalCongruent p k b a := by
  rcases h with he | hv
  · exact Or.inl he.symm
  · apply Or.inr
    rw [show b - a = -(a - b) by ring, padicValRat.neg]
    exact hv

/-- Exact cancellation of the prime square in rational valuation, including
the zero case, is the bridge from three-digit precision to a field decision. -/
theorem prime_square_precision_iff (p : ℕ) [Fact p.Prime] (q : ℚ) :
    WPReview.RationalCongruent p 3 ((p : ℚ) ^ 2 * q) 0 ↔
      WPReview.RationalCongruent p 1 q 0 := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  by_cases hq : q = 0
  · simp [hq, WPReview.RationalCongruent]
  · have hm : (p : ℚ) ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero 2 hpq) hq
    simp only [WPReview.RationalCongruent, sub_zero, hm, hq, false_or]
    rw [padicValRat.mul (pow_ne_zero 2 hpq) hq, padicValRat.pow,
      padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
    omega

/-- The full original F_p moment has precision three exactly when its actual
integral NC69 defect vanishes in the field. No moment-value premise is used. -/
theorem actual_full_moment_defect_iff (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
          WPNativeMomentIntegrality.actualMonomialMoment p n) /
        WPMomentPrecision.MomentDigitAlgebra.baseNormalizer)
      ((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3) ↔
        (actualDefect p : ZMod p) = 0 := by
  change WPGammaArithmetic.RationalCongruent p 3 _ _ ↔ _
  rw [WPGammaArithmetic.rationalCongruent_iff_sub_zero]
  change WPReview.RationalCongruent p 3 _ 0 ↔ _
  have hN := actual_full_native_moment_NC69_precision p hp
  change WPReview.RationalCongruent p 3 _ ((p : ℚ) ^ 2 * actualDefect p) at hN
  have hD := integral_residue_zero_iff p (actualDefect p) (actualDefect_integral p hp)
  constructor
  · intro h
    have hterm := WPNativeMomentIntegrality.precision_trans p 3 _ _ _
      (precision_symm p 3 _ _ hN) h
    exact hD.mpr ((prime_square_precision_iff p (actualDefect p)).mp hterm)
  · intro h
    have hterm := (prime_square_precision_iff p (actualDefect p)).mpr (hD.mp h)
    exact WPNativeMomentIntegrality.precision_trans p 3 _ _ _ hN hterm

/-- Complete actual NC68--NC77 reduction: Assembly's only remaining decision
is the displayed exact field scalar equality, for every prime p>=19. -/
theorem actual_full_moment_NC77_iff (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
          WPNativeMomentIntegrality.actualMonomialMoment p n) /
        WPMomentPrecision.MomentDigitAlgebra.baseNormalizer)
      ((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3) ↔
        actualNC77Scalar p hp = (actualP p : ZMod p) := by
  rw [actual_full_moment_defect_iff p hp, actualDefect_NC77_field p hp, sub_eq_zero]
  exact eq_comm

/-- Exact normalization of the native target, using the original Fermat units. -/
theorem actual_native_target_normalization (p : ℕ) (hp : 1 ≤ p) :
    WPMomentPrecision.MomentDigitAlgebra.baseNormalizer *
      ((fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3) =
        (1728 : ℚ) ^ p / 45000 := by
  have hu : (fermatUnit p 2) ^ 6 * (fermatUnit p 3) ^ 3 =
      (1728 : ℚ) ^ (p - 1) := by
    unfold fermatUnit
    calc
      ((2 : ℚ) ^ (p - 1)) ^ 6 * ((3 : ℚ) ^ (p - 1)) ^ 3 =
          ((2 : ℚ) ^ 6) ^ (p - 1) * ((3 : ℚ) ^ 3) ^ (p - 1) := by
        congr 1 <;> rw [← pow_mul, ← pow_mul] <;> congr 1 <;> omega
      _ = ((2 : ℚ) ^ 6 * (3 : ℚ) ^ 3) ^ (p - 1) := (mul_pow _ _ _).symm
      _ = (1728 : ℚ) ^ (p - 1) := by norm_num
  have ht : (1728 : ℚ) ^ p = (1728 : ℚ) ^ (p - 1) * 1728 := by
    simpa only [Nat.sub_add_cancel hp] using (pow_succ (1728 : ℚ) (p - 1))
  rw [hu, ht]
  norm_num only [WPMomentPrecision.MomentDigitAlgebra.baseNormalizer]
  ring

theorem nativeNormalizer_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p WPMomentPrecision.MomentDigitAlgebra.baseNormalizer := by
  let R := integralRationals p
  let c5 : R := ⟨1 / 5, WPFiniteConductorPolynomial.small_inverse_integral p 5
    (by norm_num) (by omega)⟩
  have hv : (24 * c5 ^ 4).val =
      WPMomentPrecision.MomentDigitAlgebra.baseNormalizer := by
    change (24 : ℚ) * (1 / 5) ^ 4 = _
    norm_num [WPMomentPrecision.MomentDigitAlgebra.baseNormalizer]
  change WPMomentPrecision.MomentDigitAlgebra.baseNormalizer ∈ R
  rw [← hv]
  exact (24 * c5 ^ 4).property

/-- The exact native normalization is a unit, so it preserves all three digits. -/
theorem native_normalized_precision_iff (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (a b : ℚ) :
    WPReview.RationalCongruent p k
      (a / WPMomentPrecision.MomentDigitAlgebra.baseNormalizer) b ↔
    WPReview.RationalCongruent p k a
      (WPMomentPrecision.MomentDigitAlgebra.baseNormalizer * b) := by
  have h0 : WPMomentPrecision.MomentDigitAlgebra.baseNormalizer ≠ 0 := by
    norm_num [WPMomentPrecision.MomentDigitAlgebra.baseNormalizer]
  constructor
  · intro h
    have hc := precision_mul_integral p k
      WPMomentPrecision.MomentDigitAlgebra.baseNormalizer _ _
      (nativeNormalizer_integral p hp) h
    rw [show WPMomentPrecision.MomentDigitAlgebra.baseNormalizer *
      (a / WPMomentPrecision.MomentDigitAlgebra.baseNormalizer) = a by field_simp [h0]] at hc
    exact hc
  · intro h
    have hc := precision_mul_integral p k
      WPMomentPrecision.MomentDigitAlgebra.baseNormalizer⁻¹ _ _
      (baseNormalizer_inverse_integral p hp) h
    rw [show WPMomentPrecision.MomentDigitAlgebra.baseNormalizer⁻¹ * a =
        a / WPMomentPrecision.MomentDigitAlgebra.baseNormalizer by ring,
      show WPMomentPrecision.MomentDigitAlgebra.baseNormalizer⁻¹ *
        (WPMomentPrecision.MomentDigitAlgebra.baseNormalizer * b) = b by field_simp [h0]] at hc
    exact hc

/-- Assembly's native moment-value decision has precisely the same actual NC77 scalar. -/
theorem actual_full_native_value_NC77_iff (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 3
      (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
        WPNativeMomentIntegrality.actualMonomialMoment p n)
      ((1728 : ℚ) ^ p / 45000) ↔
        actualNC77Scalar p hp = (actualP p : ZMod p) := by
  rw [← actual_native_target_normalization p (by omega),
    ← native_normalized_precision_iff p 3 hp]
  exact actual_full_moment_NC77_iff p hp

end WPMomentPrecision.MomentToField
