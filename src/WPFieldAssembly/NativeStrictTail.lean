import WPFieldAssembly.NativeFullGreen
import WPFieldAssembly.ConicKernel

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualNativeSecondTaylor
  WPActualRankTwoParameter WPActualRankTwoDividedDifference
  WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPActualRankTwoHatLift WPActualRankTwoComparison WPActualRankTwoProper
  WPFieldAssembly.TerminatingSquare WPFieldAssembly.NativeDiscriminant
  WPFieldAssembly.NativePrecision WPFieldAssembly.NativePrecisionTwo
  WPFieldAssembly.NativeTerminal WPFieldAssembly.NativeSecondGreen
  WPFieldAssembly.NativeShiftedChi WPFieldAssembly.NativeFullGreen

namespace WPFieldAssembly.NativeStrictTail

set_option maxHeartbeats 1600000

private theorem field_prime_zero (p : ℕ) : (p : (ZMod p)[X]) = 0 := by
  change C (p : ZMod p) = 0
  rw [ZMod.natCast_self, C_0]

noncomputable def strictTailNative (p : ℕ) : ℚ[X] :=
  coefficientPolynomial (fullCutoff p)
    (fun n => if (p - 1) / 2 < n then
      WPReview.nativeCoefficient n / (p : ℚ) ^ 2 else 0)

theorem strictTailNative_coeff (p n : ℕ) :
    (strictTailNative p).coeff n =
      if n < fullCutoff p + 1 then
        if (p - 1) / 2 < n then
          WPReview.nativeCoefficient n / (p : ℚ) ^ 2 else 0
      else 0 := by
  rw [strictTailNative, coefficientPolynomial_coeff]

theorem strictTailNative_low_zero (p n : ℕ)
    (hn : n ≤ (p - 1) / 2) :
    (strictTailNative p).coeff n = 0 := by
  simp [strictTailNative_coeff, not_lt.mpr hn]

theorem strictTailNative_integral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((strictTailNative p).coeff n) := by
  rw [strictTailNative_coeff]
  split_ifs with hn hupper
  · obtain ⟨b, hb, _⟩ := actual_upper_native_divided_two_witness p n hp
      (by dsimp [fullCutoff] at hn; omega) hupper
    rw [← hb]
    exact b.property
  · simp
  · simp

noncomputable def strictTailNativeIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralPolynomialLift p (strictTailNative p) (strictTailNative_integral p hp)

theorem strictTailNativeIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (strictTailNativeIntegral p hp).map (integralRationals p).subtype =
      strictTailNative p :=
  integralPolynomialLift_rational _ _ _

noncomputable def BtailIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (strictTailNativeIntegral p hp).comp (1 - X ^ 2)

noncomputable def BtailField (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (BtailIntegral p hp).map (residueHom p)

theorem BtailIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (BtailIntegral p hp).map (integralRationals p).subtype =
      (strictTailNative p).comp (1 - X ^ 2) := by
  rw [BtailIntegral, Polynomial.map_comp, strictTailNativeIntegral_value]
  simp only [Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X]

theorem BtailField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (BtailField p hp).natDegree ≤ 2 * fullCutoff p := by
  apply natDegree_map_le.trans
  have hN : (strictTailNativeIntegral p hp).natDegree ≤ fullCutoff p := by
    rw [strictTailNativeIntegral, integralPolynomialLift_degree]
    exact coefficientPolynomial_degree _ _
  have hq : (1 - X ^ 2 : (integralRationals p)[X]).natDegree ≤ 2 := by
    compute_degree
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul hN hq).trans_eq (Nat.mul_comm _ _))

theorem actual_full_minus_half_native (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    fullNativeJacobi p - halfNativeJacobi p =
      C ((p : ℚ) ^ 2) *
        (BtailIntegral p hp).map (integralRationals p).subtype := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hN : (p - 1) / 2 ≤ fullCutoff p := by
    have hh := WPFiniteWSource.half_exponent p hp
    dsimp [fullCutoff]
    omega
  have hn :
      WPReview.nativePolynomial (fullCutoff p + 1) -
        WPReview.nativePolynomial ((p - 1) / 2 + 1) =
      C ((p : ℚ) ^ 2) * strictTailNative p := by
    ext n
    rw [coeff_sub, coeff_C_mul, WPReview.nativePolynomial_coeff,
      WPReview.nativePolynomial_coeff, strictTailNative_coeff]
    by_cases he : n < fullCutoff p + 1
    · rw [if_pos he, if_pos he]
      by_cases hl : n < (p - 1) / 2 + 1
      · rw [if_pos hl, if_neg (by omega)]
        ring
      · rw [if_neg hl, if_pos (by omega)]
        field_simp [hpq]
        ring
    · rw [if_neg he, if_neg he, if_neg (by omega)]
      ring
  have hc := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2)) hn
  simp only [sub_comp, mul_comp, C_comp] at hc
  rw [BtailIntegral_value]
  exact hc

noncomputable def halfDividedIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  Classical.choose (actual_native_discriminant_divided_two_witness p hp)

theorem halfDividedIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (halfDividedIntegral p hp).map (integralRationals p).subtype =
      C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p :=
  Classical.choose_spec (actual_native_discriminant_divided_two_witness p hp)

noncomputable def halfDividedField (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (halfDividedIntegral p hp).map (residueHom p)

/-- Exact polarization, before either coefficient reduction or derivative kernels. -/
theorem weighted_discriminant_scaled_difference (r : ℚ) (hr : r ≠ 0)
    (F B : ℚ[X]) :
    C (1 / r ^ 2) *
      ((1 - X ^ 2) * jacobiDiscriminant 0 (F + C (r ^ 2) * B) -
        (1 - X ^ 2) * jacobiDiscriminant 0 F) =
      2 * (1 - X ^ 2) * jacobiPolar F B +
        C (r ^ 2) * (1 - X ^ 2) * jacobiDiscriminant 0 B := by
  have hD :
      (1 - X ^ 2) * jacobiDiscriminant 0 (F + C (r ^ 2) * B) -
        (1 - X ^ 2) * jacobiDiscriminant 0 F =
      C (r ^ 2) *
        (2 * (1 - X ^ 2) * jacobiPolar F B +
          C (r ^ 2) * (1 - X ^ 2) * jacobiDiscriminant 0 B) := by
    rw [jacobiDiscriminant_add_scaled]
    simp only [_root_.map_pow]
    ring
  rw [hD, ← mul_assoc]
  have hc : C (1 / r ^ 2) * C (r ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    field_simp [hr]
    simp only [C_1]
  rw [hc, one_mul]

theorem actual_full_minus_half_divided_integral
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fullDividedDiscriminantIntegral p hp - halfDividedIntegral p hp =
      2 * (1 - X ^ 2) *
        jacobiPolar (integralNativeJacobi p hp) (BtailIntegral p hp) +
      C ((p : integralRationals p) ^ 2) * (1 - X ^ 2) *
        jacobiDiscriminant 0 (BtailIntegral p hp) := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [Polynomial.map_sub, actual_full_discriminant_divided_two_value,
    halfDividedIntegral_value]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_ofNat,
    Polynomial.map_C, jacobiPolar_map, jacobiDiscriminant_map,
    integralNativeJacobi_rational, Subring.subtype_apply, Subring.coe_pow,
    Subring.coe_natCast]
  norm_num only [Polynomial.map_pow, Polynomial.map_X, Nat.cast_zero, Subring.coe_zero]
  have hF :
      fullNativeJacobi p = halfNativeJacobi p +
        C ((p : ℚ) ^ 2) *
          (BtailIntegral p hp).map (integralRationals p).subtype := by
    linear_combination actual_full_minus_half_native p hp
  rw [fullWeightedDiscriminant, weightedNativeDiscriminant, hF]
  simpa only [mul_sub] using
    weighted_discriminant_scaled_difference (p : ℚ) (by positivity)
      (halfNativeJacobi p)
      ((BtailIntegral p hp).map (integralRationals p).subtype)

theorem actual_tail_Green_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullDividedDiscriminantIntegral p hp).map (residueHom p) -
      halfDividedField p hp =
      18 * quadraticGreen (actualLegendreJacobi p) (BtailField p hp) := by
  have hf := congrArg (Polynomial.map (residueHom p))
    (actual_full_minus_half_divided_integral p hp)
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_one, Polynomial.map_X, jacobiPolar_map,
    jacobiDiscriminant_map, integralNativeJacobi_field,
    _root_.map_pow, _root_.map_natCast, Polynomial.map_natCast, field_prime_zero,
    zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero] at hf
  change _ - halfDividedField p hp =
    2 * (1 - X ^ 2) * jacobiPolar (actualLegendreJacobi p ^ 2)
      (BtailField p hp) at hf
  have hg := quadraticGreen_polar
    (actualLegendreJacobi p) (BtailField p hp)
  rw [actual_rank_clear_zero p hp, mul_zero, add_zero] at hg
  change _ - halfDividedField p hp = _
  linear_combination hf + 2 * hg

theorem actual_gamma_four_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    4 * residueHom p (nativeHalfDivPrime p hp) ^ 2 = 1 := by
  let γ := residueHom p (nativeHalfDivPrime p hp)
  let η : ZMod p := nativeSixEta p
  let s : ZMod p := (-1) ^ ((p - 1) / 2)
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have ht : 2 * γ = -η * s := by
    dsimp only [γ, η, s]
    rw [actual_native_half_div_prime_residue p hp]
    field_simp [h2]
  have hη : η ^ 2 = 1 := by
    dsimp [η, nativeSixEta]
    split_ifs <;> norm_num
  have hs : s ^ 2 = 1 := by
    dsimp [s]
    rw [pow_two, ← mul_pow]
    norm_num
  have hc : (2 * γ) ^ 2 = (η * s) ^ 2 := by
    rw [ht]
    ring
  rw [mul_pow, mul_pow, hη, hs] at hc
  norm_num at hc
  exact hc

theorem actual_half_divided_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (halfDividedField p hp).coeff (2 * p) = -1 := by
  rw [halfDividedField, coeff_map,
    second_divided_discriminant_top p hp (halfDividedIntegral p hp)
      (halfDividedIntegral_value p hp)]
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_pow, _root_.map_ofNat, _root_.map_natCast,
    ZMod.natCast_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_sub]
  linear_combination -(actual_gamma_four_square p hp)

theorem actual_tail_Green_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (quadraticGreen (actualLegendreJacobi p) (BtailField p hp)).derivative =
      C (4 * residueHom p (nativeHalfDivPrime p hp) / 9) *
        X * (1 - X ^ 2) ^ ((p - 1) / 2) * actualLegendreJacobi p ^ 2 := by
  let γ := residueHom p (nativeHalfDivPrime p hp)
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 := by
    rw [show (9 : ZMod p) = 3 ^ 2 by ring]
    exact pow_ne_zero 2 h3
  have h18 : (18 : (ZMod p)[X]) ≠ 0 := by
    apply C_ne_zero.mpr
    change (18 : ZMod p) ≠ 0
    rw [show (18 : ZMod p) = 2 * 3 ^ 2 by ring]
    exact mul_ne_zero h2 (pow_ne_zero 2 h3)
  have hd := congrArg Polynomial.derivative (actual_tail_Green_attachment p hp)
  dsimp only [halfDividedField] at hd
  rw [actual_full_minus_half_derivative p hp (halfDividedIntegral p hp)
    (halfDividedIntegral_value p hp),
    show (18 : (ZMod p)[X]) = C (18 : ZMod p) by rfl, derivative_C_mul] at hd
  have hs : (18 : (ZMod p)[X]) * C (4 * γ / 9) = C (8 * γ) := by
    rw [show (18 : (ZMod p)[X]) = C (18 : ZMod p) by rfl, ← C_mul]
    congr 1
    field_simp [h9]
    ring
  apply mul_left_cancel₀ h18
  change 18 *
      (quadraticGreen (actualLegendreJacobi p) (BtailField p hp)).derivative =
    18 * (C (4 * γ / 9) * X *
      (1 - X ^ 2) ^ ((p - 1) / 2) * actualLegendreJacobi p ^ 2)
  calc
    _ = C (8 * γ) * X *
        (1 - X ^ 2) ^ ((p - 1) / 2) * actualLegendreJacobi p ^ 2 := hd.symm
    _ = _ := by rw [← hs]; ring

theorem actual_tail_Green_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (quadraticGreen (actualLegendreJacobi p) (BtailField p hp)).coeff (2 * p) =
      (1 / 3 : ZMod p) := by
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h18 : (18 : ZMod p) ≠ 0 := by
    rw [show (18 : ZMod p) = 2 * 3 ^ 2 by ring]
    exact mul_ne_zero h2 (pow_ne_zero 2 h3)
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff (2 * p))
    (actual_tail_Green_attachment p hp)
  rw [coeff_sub, coeff_ofNat_mul,
    (actual_full_divided_discriminant_degree_top p hp).2,
    actual_half_divided_top p hp] at hc
  apply mul_left_cancel₀ h18
  calc
    _ = 6 := by linear_combination -hc
    _ = 18 * (1 / 3 : ZMod p) := by field_simp [h3]; ring

noncomputable def seventyTwoFifth (p : ℕ) [Fact p.Prime]
    (_hp : 19 ≤ p) : integralRationals p :=
  72 * smallIntegralInverse p 5

theorem seventyTwoFifth_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (seventyTwoFifth p hp).val = (72 / 5 : ℚ) := by
  change (72 : ℚ) * (smallIntegralInverse p 5).val = 72 / 5
  rw [smallIntegralInverse_value p 5 (by omega) (by omega)]
  ring

theorem seventyTwoFifth_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (seventyTwoFifth p hp) = (72 / 5 : ZMod p) := by
  rw [seventyTwoFifth, _root_.map_mul, _root_.map_ofNat,
    smallIntegralInverse_field p 5 (by omega) (by omega)]
  norm_num only [div_eq_mul_inv, Nat.cast_ofNat]

noncomputable def halfQIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  fullQIntegral p hp - C (seventyTwoFifth p hp) * BtailIntegral p hp

noncomputable def halfQField (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (halfQIntegral p hp).map (residueHom p)

theorem halfQIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (halfQIntegral p hp).map (integralRationals p).subtype =
      fullQ p - C (72 / 5 : ℚ) *
        (BtailIntegral p hp).map (integralRationals p).subtype := by
  rw [halfQIntegral, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, fullQIntegral_value, Subring.subtype_apply, seventyTwoFifth_value]

theorem halfQField_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    halfQField p hp = fullQField p hp - C (72 / 5 : ZMod p) * BtailField p hp := by
  rw [halfQField, halfQIntegral, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, seventyTwoFifth_field]
  rfl

theorem actual_half_balanced_taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    halfNativeJacobi p = balancedRank p ^ 2 +
      C (5 * (p : ℚ) ^ 2 / 72) *
        (halfQIntegral p hp).map (integralRationals p).subtype +
      C ((p : ℚ) ^ 3) *
        (fullTaylorRemainder p hp).map (integralRationals p).subtype := by
  rw [halfQIntegral_value]
  have hcoef : C (5 * (p : ℚ) ^ 2 / 72) * C (72 / 5 : ℚ) = C ((p : ℚ) ^ 2) := by
    rw [← C_mul]
    congr 1
    ring
  rw [mul_sub, ← mul_assoc, hcoef]
  have hf := fullTaylorRemainder_value p hp
  have hb := actual_full_minus_half_native p hp
  linear_combination hf - hb

theorem quadraticGreen_sub {K : Type*} [CommRing K] (Y Q R : K[X]) :
    quadraticGreen Y (Q - R) = quadraticGreen Y Q - quadraticGreen Y R := by
  simp [quadraticGreen, derivative_sub]
  ring

theorem quadraticGreen_C_mul {K : Type*} [CommRing K] (Y Q : K[X]) (s : K) :
    quadraticGreen Y (C s * Q) = C s * quadraticGreen Y Q := by
  simp [quadraticGreen]
  ring

theorem quadraticGreen_nat_mul {K : Type*} [CommRing K]
    (Y Q : K[X]) (n : ℕ) :
    quadraticGreen Y ((n : K[X]) * Q) = (n : K[X]) * quadraticGreen Y Q := by
  rw [show (n : K[X]) = C (n : K) by simp]
  exact quadraticGreen_C_mul Y Q (n : K)

theorem actual_half_second_Green_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    quadraticGreen (actualLegendreJacobi p) (halfQField p hp) =
      4 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
        (actualLegendreJacobi p +
          2 * X * (actualRankDividedField p (by omega)).derivative +
          actualRankDividedField p (by omega)) +
      4 * (X ^ (2 * p) - 1) -
      C (72 / 5 : ZMod p) *
        quadraticGreen (actualLegendreJacobi p) (BtailField p hp) := by
  rw [halfQField_attachment, quadraticGreen_sub, quadraticGreen_C_mul,
    actual_full_second_Green_normalization p hp]

noncomputable def nativeTwoNodeU (p : ℕ) : ℚ[X] :=
  C (1 / (4 * (p : ℚ))) * (rankJacobiNode p 1 - rankJacobiNode p 5)

theorem nativeTwoNodeU_eq (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeTwoNodeU p = C (1 / 6 : ℚ) * rankDividedJacobi p := by
  rw [nativeTwoNodeU, actual_two_jacobi_node_difference p (by omega),
    ← mul_assoc, ← C_mul]
  congr 2
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp [hpq]
  ring

noncomputable def nativeUIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (sixth p hp) * rankDividedIntegralJacobi p (by omega)

theorem nativeUIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (nativeUIntegral p hp).map (integralRationals p).subtype = nativeTwoNodeU p := by
  rw [nativeUIntegral, Polynomial.map_mul, Polynomial.map_C,
    rankDividedIntegralJacobi_value, nativeTwoNodeU_eq p hp]
  rfl

noncomputable def nativeMixedSquareIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  nativeUIntegral p hp ^ 2

noncomputable def nativeSecondCorrectionFullIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  nativeMixedSquareIntegral p hp +
    C (fullScale p hp) * fullQIntegral p hp +
    C (p : integralRationals p) * fullTaylorRemainder p hp

noncomputable def nativeSecondCorrectionHalfIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (integralRationals p)[X] :=
  nativeSecondCorrectionFullIntegral p hp - BtailIntegral p hp

theorem actual_balanced_native_U (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    balancedRank p = rankJacobiNode p 1 + C (p : ℚ) * nativeTwoNodeU p := by
  rw [balancedRank, nativeTwoNodeU_eq p hp]
  rw [show (p : ℚ) / 6 = (p : ℚ) * (1 / 6) by ring]
  simp only [_root_.map_mul]
  ring

theorem nativeSecondCorrectionFullIntegral_value
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeSecondCorrectionFullIntegral p hp).map (integralRationals p).subtype =
      C (1 / (p : ℚ) ^ 2) *
        (fullNativeJacobi p - rankJacobiNode p 1 ^ 2 -
          2 * C (p : ℚ) * rankJacobiNode p 1 * nativeTwoNodeU p) := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hc :
      C ((p : ℚ) ^ 2) *
        (nativeSecondCorrectionFullIntegral p hp).map (integralRationals p).subtype =
      fullNativeJacobi p - rankJacobiNode p 1 ^ 2 -
        2 * C (p : ℚ) * rankJacobiNode p 1 * nativeTwoNodeU p := by
    simp only [nativeSecondCorrectionFullIntegral, nativeMixedSquareIntegral,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, nativeUIntegral_value, fullScale_value,
      fullQIntegral_value, Subring.subtype_apply, _root_.map_natCast,
      Polynomial.map_natCast]
    rw [fullTaylorRemainder_value p hp, actual_balanced_native_U p hp]
    rw [show 5 * (p : ℚ) ^ 2 / 72 = (p : ℚ) ^ 2 * (5 / 72) by ring]
    simp only [_root_.map_mul, _root_.map_pow, C_eq_natCast]
    ring
  have hunit : C (1 / (p : ℚ) ^ 2) * C ((p : ℚ) ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    field_simp [hpq]
    simp only [C_1]
  rw [← hc, ← mul_assoc, hunit, one_mul]

theorem nativeSecondCorrectionHalfIntegral_value
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeSecondCorrectionHalfIntegral p hp).map (integralRationals p).subtype =
      C (1 / (p : ℚ) ^ 2) *
        (halfNativeJacobi p - rankJacobiNode p 1 ^ 2 -
          2 * C (p : ℚ) * rankJacobiNode p 1 * nativeTwoNodeU p) := by
  rw [nativeSecondCorrectionHalfIntegral, Polynomial.map_sub,
    nativeSecondCorrectionFullIntegral_value]
  have hb := actual_full_minus_half_native p hp
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hunit : C (1 / (p : ℚ) ^ 2) * C ((p : ℚ) ^ 2) = (1 : ℚ[X]) := by
    rw [← C_mul]
    field_simp [hpq]
    simp only [C_1]
  have hc := congrArg (fun P : ℚ[X] => C (1 / (p : ℚ) ^ 2) * P) hb
  rw [← mul_assoc, hunit, one_mul] at hc
  linear_combination hc

noncomputable def nativeIR28DifferenceFull (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (nativeSecondCorrectionFullIntegral p hp -
    6 * nativeMixedSquareIntegral p hp).map (residueHom p)

noncomputable def nativeIR28DifferenceHalf (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  (nativeSecondCorrectionHalfIntegral p hp -
    6 * nativeMixedSquareIntegral p hp).map (residueHom p)

noncomputable def fullLogNumerator (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (ZMod p)[X] :=
  fullQField p hp - 2 * actualRankDividedField p (by omega) ^ 2

theorem actual_native_IR28_models (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    72 * nativeIR28DifferenceFull p hp = 5 * fullLogNumerator p hp := by
  have hi :
      72 * (nativeSecondCorrectionFullIntegral p hp -
        6 * nativeMixedSquareIntegral p hp) =
      5 * (fullQIntegral p hp -
        2 * rankDividedIntegralJacobi p (by omega) ^ 2) +
      72 * C (p : integralRationals p) * fullTaylorRemainder p hp := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    simp only [nativeSecondCorrectionFullIntegral, nativeMixedSquareIntegral,
      nativeUIntegral, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_ofNat, Subring.subtype_apply, fullScale_value]
    change
      72 * ((C (1 / 6 : ℚ) *
        (rankDividedIntegralJacobi p (by omega)).map
          (integralRationals p).subtype) ^ 2 +
        C (5 / 72 : ℚ) *
          (fullQIntegral p hp).map (integralRationals p).subtype +
        C (p : ℚ) *
          (fullTaylorRemainder p hp).map (integralRationals p).subtype -
        6 * (C (1 / 6 : ℚ) *
          (rankDividedIntegralJacobi p (by omega)).map
            (integralRationals p).subtype) ^ 2) = _
    have h36 : (36 : ℚ[X]) * C (1 / 6 : ℚ) ^ 2 = 1 := by
      change C (36 : ℚ) * C (1 / 6 : ℚ) ^ 2 = C (1 : ℚ)
      rw [← C_pow, ← C_mul]
      norm_num
    have h72 : (72 : ℚ[X]) * C (5 / 72 : ℚ) = 5 := by
      change C (72 : ℚ) * C (5 / 72 : ℚ) = C (5 : ℚ)
      rw [← C_mul]
      norm_num
    linear_combination
      ((fullQIntegral p hp).map (integralRationals p).subtype) * h72 -
        10 * ((rankDividedIntegralJacobi p (by omega)).map
          (integralRationals p).subtype) ^ 2 * h36
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_ofNat,
    _root_.map_natCast, Polynomial.map_natCast, field_prime_zero,
    mul_zero, zero_mul, add_zero] at hf
  simpa only [nativeIR28DifferenceFull, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_ofNat, fullLogNumerator,
    fullQField, actualRankDividedField] using hf

theorem actual_native_IR28_half_tail (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeIR28DifferenceHalf p hp =
      nativeIR28DifferenceFull p hp - BtailField p hp := by
  simp only [nativeIR28DifferenceHalf, nativeIR28DifferenceFull,
    nativeSecondCorrectionHalfIntegral, Polynomial.map_sub, BtailField]
  ring

theorem quadraticGreen_square_wronskian {K : Type*} [CommRing K]
    (Y R : K[X]) :
    let W := (1 - X ^ 2) * (Y * R.derivative - Y.derivative * R)
    quadraticGreen Y (R ^ 2) =
      2 * W ^ 2 + 2 * (1 - X ^ 2) * Y * R * W.derivative := by
  dsimp only
  simp [quadraticGreen, derivative_mul, derivative_pow_succ]
  ring

theorem actual_full_log_numerator_Green (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    quadraticGreen (actualLegendreJacobi p) (fullLogNumerator p hp) =
      4 * (actualLegendreJacobi p ^ 4 - 1) := by
  let Y := actualLegendreJacobi p
  let R := actualRankDividedField p (by omega)
  let W : (ZMod p)[X] :=
    (1 - X ^ 2) * (Y * R.derivative - Y.derivative * R)
  have hW : W = X * Y ^ 2 - X ^ p :=
    actual_first_rank_wronskian p hp
  have hd := congrArg Polynomial.derivative hW
  have hxp : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by
    simp [derivative_X_pow]
  have hWd : W.derivative = Y ^ 2 + 2 * X * Y * Y.derivative := by
    simp only [derivative_sub, derivative_mul, derivative_X,
      derivative_pow_succ, hxp, one_mul, pow_one,
      _root_.map_add, _root_.map_one, Nat.cast_one] at hd
    linear_combination hd
  have hsquare :
      quadraticGreen Y (R ^ 2) =
        2 * W ^ 2 + 2 * (1 - X ^ 2) * Y * R * W.derivative :=
    quadraticGreen_square_wronskian Y R
  have hpow : (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 := by
    rw [show 2 * p = p * 2 by omega, pow_mul]
  have htwo := quadraticGreen_nat_mul Y (R ^ 2) 2
  norm_num only [Nat.cast_ofNat] at htwo
  change quadraticGreen Y (fullQField p hp - 2 * R ^ 2) = 4 * (Y ^ 4 - 1)
  rw [quadraticGreen_sub, htwo,
    actual_full_second_Green_normalization p hp, hsquare, hWd, hW, hpow]
  dsimp only [W] at hW
  linear_combination 8 * X * Y ^ 2 * hW

theorem actual_native_IR28_difference_Green
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    72 * quadraticGreen (actualLegendreJacobi p) (nativeIR28DifferenceFull p hp) =
      20 * (actualLegendreJacobi p ^ 4 - 1) := by
  have h := congrArg (quadraticGreen (actualLegendreJacobi p))
    (actual_native_IR28_models p hp)
  have h72 := quadraticGreen_nat_mul (actualLegendreJacobi p)
    (nativeIR28DifferenceFull p hp) 72
  have h5 := quadraticGreen_nat_mul (actualLegendreJacobi p) (fullLogNumerator p hp) 5
  norm_num only [Nat.cast_ofNat] at h72 h5
  rw [h72, h5,
    actual_full_log_numerator_Green p hp] at h
  linear_combination h

theorem actual_native_IR28_half_difference_Green
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    72 * quadraticGreen (actualLegendreJacobi p) (nativeIR28DifferenceHalf p hp) =
      20 * (actualLegendreJacobi p ^ 4 - 1) -
        72 * quadraticGreen (actualLegendreJacobi p) (BtailField p hp) := by
  rw [actual_native_IR28_half_tail, quadraticGreen_sub]
  linear_combination actual_native_IR28_difference_Green p hp

end WPFieldAssembly.NativeStrictTail
