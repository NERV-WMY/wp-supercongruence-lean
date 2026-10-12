import WPFieldAssembly.ActualR0Node
import WPActualRankTwoCarryField

open scoped Polynomial
open Polynomial WPPIntegralReduction
  WPActualRankTwoParameter WPActualRankTwoFirstLift
  WPActualRankTwoDividedDifference WPActualRankTwoLowTaylor
  WPActualRankTwoComparison
  WPActualRankTwoHatLift WPActualRankTwoCarryField
  WPActualRankTwoResidueSource WPActualRankTwoLegendreField
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ActualNC77Chart
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.ResidualProjection
  WPFieldAssembly.OriginalLaurentDensity WPFieldAssembly.ActualR0Node
  WPMomentPrecision.NativeSecondLift

namespace WPFieldAssembly.ActualDeltaUNextSource
set_option maxHeartbeats 1200000

noncomputable def QO {K : Type*} [Field K] (p : ℕ) (P : K[X]) : K :=
  Ij p 0 (quadraticInverse P)
noncomputable def QH {K : Type*} [Field K] (p : ℕ) (P : K[X]) : K :=
  (unitEuler p (quadraticInverse P)).eval (4 / 125 : K)

theorem QO_add {K : Type*} [Field K] (p : ℕ) (P Q : K[X]) :
    QO p (P + Q) = QO p P + QO p Q := by
  rw [QO, quadraticInverse_add_local, Ij_add]; rfl

theorem QO_C_mul {K : Type*} [Field K] (p : ℕ) (a : K) (P : K[X]) :
    QO p (C a * P) = a * QO p P := by
  rw [QO, quadraticInverse_C_mul, Ij_C_mul]; rfl

theorem QH_add {K : Type*} [Field K] (p : ℕ) (P Q : K[X]) :
    QH p (P + Q) = QH p P + QH p Q := by
  rw [QH, quadraticInverse_add_local, unitEuler_add, eval_add]; rfl

theorem QH_C_mul {K : Type*} [Field K] (p : ℕ) (a : K) (P : K[X]) :
    QH p (C a * P) = a * QH p P := by
  rw [QH, quadraticInverse_C_mul, unitEuler_C_mul, eval_mul, eval_C]; rfl

-- Whole rational expansion; the p² contribution is retained before reduction.
theorem next_residual_expansion (p : ℕ) (Y L H S : ℚ[X]) (r : ℚ) :
    -QO p ((Y + C (p : ℚ) * L) * (H + C (p : ℚ) * S)) / 3 -
      QH p ((Y + C (p : ℚ) * L) ^ 2) / 2 - r =
    (-QO p (Y * H) / 3 - QH p (Y ^ 2) / 2 - r) +
      (p : ℚ) * (-(QO p (Y * S) + QO p (L * H)) / 3 - QH p (Y * L)) +
      (p : ℚ) ^ 2 * (-QO p (L * S) / 3 - QH p (L ^ 2) / 2) := by
  have hmul : (Y + C (p : ℚ) * L) * (H + C (p : ℚ) * S) =
      Y * H + C (p : ℚ) * (Y * S + L * H) + C ((p : ℚ) ^ 2) * (L * S) := by
    simp only [_root_.map_pow]; ring
  have hsq : (Y + C (p : ℚ) * L) ^ 2 =
      Y ^ 2 + C (p : ℚ) * (C (2 : ℚ) * (Y * L)) + C ((p : ℚ) ^ 2) * L ^ 2 := by
    simp only [_root_.map_pow, _root_.map_ofNat]; ring
  rw [hmul, hsq]
  simp only [QO_add, QO_C_mul, QH_add, QH_C_mul]
  ring

variable (p : ℕ) [Fact p.Prime]

noncomputable def hatNumerator : ℚ :=
  -QO p (rationalLegendre (p / 6) * rationalRankHat p) / 3 -
    QH p (rationalLegendre (p / 6) ^ 2) / 2 -
    WPFirstResidue.LiteralNormalization.literalR0 p

noncomputable def nextCorrection : ℚ :=
  -(QO p (rationalLegendre (p / 6) * actualSecondCarryPolynomial p) +
      QO p (lowCarryPolynomial p * rationalRankHat p)) / 3 -
    QH p (rationalLegendre (p / 6) * lowCarryPolynomial p)

noncomputable def nextHigher : ℚ :=
  -QO p (lowCarryPolynomial p * actualSecondCarryPolynomial p) / 3 -
    QH p (lowCarryPolynomial p ^ 2) / 2

theorem actual_deltaU_next_source (hp : 19 ≤ p) :
    actualDeltaU p = hatNumerator p + (p : ℚ) * nextCorrection p +
      (p : ℚ) ^ 2 * nextHigher p := by
  have hY : rankJacobiNode p 1 = rationalLegendre (p / 6) +
      C (p : ℚ) * lowCarryPolynomial p := by
    linear_combination actual_lowCarryPolynomial_source p (by omega : 7 ≤ p)
  have hR : rankDividedJacobi p = rationalRankHat p +
      C (p : ℚ) * actualSecondCarryPolynomial p := by
    linear_combination actualSecondCarryPolynomial_source p hp
  have hU : rankJacobiNode p 1 * actualU p =
      C (1 / 6 : ℚ) * (rankJacobiNode p 1 * rankDividedJacobi p) := by
    rw [actualU]; ring
  have hb : actualDeltaU p =
      -QO p (rankJacobiNode p 1 * rankDividedJacobi p) / 3 -
        QH p (rankJacobiNode p 1 ^ 2) / 2 -
        WPFirstResidue.LiteralNormalization.literalR0 p := by
    unfold actualDeltaU r0NodeBaseline mixedQ squareQ
    rw [hU, quadraticInverse_C_mul, O_eq_Ij, Ij_C_mul]
    unfold QO QH
    ring
  rw [hb, hY, hR]
  exact next_residual_expansion p (rationalLegendre (p / 6))
    (lowCarryPolynomial p) (rationalRankHat p) (actualSecondCarryPolynomial p)
    (WPFirstResidue.LiteralNormalization.literalR0 p)

noncomputable def QOi (hp : 19 ≤ p) (P : (integralRationals p)[X]) : integralRationals p :=
  projectionIntegral p hp 0 (quadraticInverse P)
noncomputable def QHi (hp : 19 ≤ p) (P : (integralRationals p)[X]) : integralRationals p :=
  eulerValueIntegral p hp (quadraticInverse P)

theorem QOi_value (hp : 19 ≤ p) (P : (integralRationals p)[X]) :
    (QOi p hp P).val = QO p (P.map (integralRationals p).subtype) := by
  rw [QOi, projectionIntegral_value, quadraticInverse_map]; rfl

theorem QHi_value (hp : 19 ≤ p) (P : (integralRationals p)[X]) :
    (QHi p hp P).val = QH p (P.map (integralRationals p).subtype) := by
  rw [QHi, eulerValueIntegral_value, quadraticInverse_map]; rfl

theorem QOi_field (hp : 19 ≤ p) (P : (integralRationals p)[X]) :
    residueHom p (QOi p hp P) = QO p (P.map (residueHom p)) := by
  rw [QOi, projectionIntegral_field, quadraticInverse_map]; rfl

theorem QHi_field (hp : 19 ≤ p) (P : (integralRationals p)[X]) :
    residueHom p (QHi p hp P) = QH p (P.map (residueHom p)) := by
  rw [QHi, eulerValueIntegral_field, quadraticInverse_map]; rfl

noncomputable def nextCorrectionIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(2 * integralSixth p (by omega)) *
    (QOi p hp (integralLegendre p (p / 6) (by omega) * integralSecondCarry p hp) +
     QOi p hp (lowCarryIntegral p (by omega) * integralRankHat p (by omega))) -
    QHi p hp (integralLegendre p (p / 6) (by omega) * lowCarryIntegral p (by omega))

noncomputable def nextHigherIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(2 * integralSixth p (by omega)) *
    QOi p hp (lowCarryIntegral p (by omega) * integralSecondCarry p hp) -
    WPActualRankTwoLegendreField.integralHalf p (by omega) *
      QHi p hp (lowCarryIntegral p (by omega) ^ 2)

theorem nextCorrectionIntegral_value (hp : 19 ≤ p) :
    (nextCorrectionIntegral p hp).val = nextCorrection p := by
  change -(2 * (1 / 6 : ℚ)) *
    ((QOi p hp (integralLegendre p (p / 6) (by omega) * integralSecondCarry p hp)).val +
     (QOi p hp (lowCarryIntegral p (by omega) * integralRankHat p (by omega))).val) -
    (QHi p hp (integralLegendre p (p / 6) (by omega) * lowCarryIntegral p (by omega))).val = _
  simp only [QOi_value, QHi_value, Polynomial.map_mul,
    integralLegendre_value, integralSecondCarry_value,
    lowCarryIntegral_value, integralRankHat_value]
  unfold nextCorrection
  ring

theorem nextHigherIntegral_value (hp : 19 ≤ p) :
    (nextHigherIntegral p hp).val = nextHigher p := by
  change -(2 * (1 / 6 : ℚ)) *
    (QOi p hp (lowCarryIntegral p (by omega) * integralSecondCarry p hp)).val -
    (1 / 2 : ℚ) * (QHi p hp (lowCarryIntegral p (by omega) ^ 2)).val = _
  simp only [QOi_value, QHi_value, Polynomial.map_mul, Polynomial.map_pow,
    lowCarryIntegral_value, integralSecondCarry_value]
  unfold nextHigher
  ring

-- This witness's value is the fixed rational Dhat/p, not a freely chosen carry.
noncomputable def hatDigitIntegral (hp : 19 ≤ p) : integralRationals p :=
  integralDeltaUDigit p hp - nextCorrectionIntegral p hp -
    (p : integralRationals p) * nextHigherIntegral p hp

theorem hatDigitIntegral_value (hp : 19 ≤ p) :
    (hatDigitIntegral p hp).val = hatNumerator p / (p : ℚ) := by
  change actualDeltaUDigit p - (nextCorrectionIntegral p hp).val -
    (p : ℚ) * (nextHigherIntegral p hp).val = _
  rw [nextCorrectionIntegral_value, nextHigherIntegral_value]
  unfold actualDeltaUDigit
  rw [actual_deltaU_next_source p hp]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp [hpq]
  ring

theorem actual_hat_digit_integral (hp : 19 ≤ p) :
    hatNumerator p / (p : ℚ) ∈ integralRationals p := by
  rw [← hatDigitIntegral_value p hp]
  exact (hatDigitIntegral p hp).property

-- The endpoint is fixed over Q before the coefficient reduction.
noncomputable def endpointCarryIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(integralSecondCarry p hp).eval 1

theorem endpointCarryIntegral_value (hp : 19 ≤ p) :
    (endpointCarryIntegral p hp).val =
      ((rationalEvenLog p).eval 1 +
        (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)) / (p : ℚ) := by
  change -(integralRationals p).subtype ((integralSecondCarry p hp).eval 1) = _
  rw [← eval_map_apply, integralSecondCarry_value, _root_.map_one,
    actualSecondCarryPolynomial_endpoint_one p hp]
  ring

theorem actual_next_endpoint (hp : 19 ≤ p) :
    (actualSecondCarryField p hp).eval 1 = -residueHom p (endpointCarryIntegral p hp) := by
  simp only [actualSecondCarryField, endpointCarryIntegral, _root_.map_neg, neg_neg]
  simpa only [_root_.map_one] using
      (Polynomial.eval_map_apply (p := integralSecondCarry p hp) (residueHom p) 1)

theorem actual_next_legendre_source (hp : 19 ≤ p) :
    WPActualRankTwoGaussODE.legendreJacobi (p / 6) (actualSecondCarryField p hp) =
      actualCarryFieldSource p (by omega) :=
  actualSecondCarryField_source p hp

theorem nextCorrectionIntegral_field (hp : 19 ≤ p) :
    residueHom p (nextCorrectionIntegral p hp) =
      -QO p (actualLegendreJacobi p * actualSecondCarryField p hp) / 3 +
        QO p (actualVariationField p (by omega) * actualRankDividedField p (by omega)) / 18 +
        QH p (actualLegendreJacobi p * actualVariationField p (by omega)) / 6 := by
  have hL : (lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p) =
      C (-(1 / 6 : ZMod p)) * actualVariationField p (by omega) := by
    have h := actual_lowCarry_variation_field p (by omega : 7 ≤ p)
    change (lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p) +
      C (1 / 6 : ZMod p) * actualVariationField p (by omega) = 0 at h
    rw [_root_.map_neg]
    linear_combination h
  have hLR :
      ((lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p)) *
        ((integralRankHat p (by omega : 7 ≤ p)).map (residueHom p)) =
      C (-(1 / 6 : ZMod p)) *
        (actualVariationField p (by omega) * actualRankDividedField p (by omega)) := by
    rw [hL, integralRankHat_field, ← actual_rankDividedField_eq_hat p hp]
    ring
  have hYL : actualLegendreJacobi p *
      ((lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p)) =
      C (-(1 / 6 : ZMod p)) *
        (actualLegendreJacobi p * actualVariationField p (by omega)) := by
    rw [hL]; ring
  rw [nextCorrectionIntegral, _root_.map_sub, _root_.map_mul, _root_.map_neg, _root_.map_mul, _root_.map_ofNat,
    integralSixth_field, _root_.map_add, QOi_field, QOi_field, QHi_field]
  simp only [Polynomial.map_mul, integralLegendre_field]
  change -(2 * (1 / 6 : ZMod p)) *
    (QO p (actualLegendreJacobi p * actualSecondCarryField p hp) +
     QO p (((lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p)) *
       ((integralRankHat p (by omega : 7 ≤ p)).map (residueHom p)))) -
    QH p (actualLegendreJacobi p *
      ((lowCarryIntegral p (by omega : 7 ≤ p)).map (residueHom p))) = _
  rw [hLR, hYL, QO_C_mul, QH_C_mul]
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h18 : (18 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 18 (by omega) (by omega)
  field_simp [h3, h6, h18]
  ring

-- The original actual NC79c. No Dhat, S, endpoint, or comparison premise.
theorem actual_deltaU_digit_next_source (hp : 19 ≤ p) :
    residueHom p (integralDeltaUDigit p hp) =
      residueHom p (hatDigitIntegral p hp) -
        QO p (actualLegendreJacobi p * actualSecondCarryField p hp) / 3 +
        QO p (actualVariationField p (by omega) * actualRankDividedField p (by omega)) / 18 +
        QH p (actualLegendreJacobi p * actualVariationField p (by omega)) / 6 := by
  have h := congrArg (residueHom p)
    (show hatDigitIntegral p hp = integralDeltaUDigit p hp -
      nextCorrectionIntegral p hp - (p : integralRationals p) * nextHigherIntegral p hp from rfl)
  simp only [_root_.map_sub, _root_.map_mul, _root_.map_natCast, ZMod.natCast_self,
    zero_mul, sub_zero] at h
  rw [nextCorrectionIntegral_field p hp] at h
  linear_combination -h

omit [Fact p.Prime] in
theorem actual_wronskian_endpoint_one [Fact p.Prime] : (actualW p).eval 1 = 0 := by
  simp [actualW, eval_mul, eval_sub, eval_one, eval_X, eval_pow]

theorem actual_variation_primitive (hp : 19 ≤ p) :
    QH p (actualLegendreJacobi p * actualVariationField p (by omega)) =
      (WPActualPositivePair.eulerPrimitive p
        (quadraticInverse (actualLegendreJacobi p * actualVariationField p (by omega)))).eval
          (4 / 125 : ZMod p) := by
  have hprod :
      (actualLegendreJacobi p * actualVariationField p (by omega : 7 ≤ p)).natDegree ≤
        2 * (p / 6) := by
    exact Polynomial.natDegree_mul_le.trans
      (by have hY := actualLegendreJacobi_degree p
          have hA := actualVariationField_degree p (by omega : 7 ≤ p)
          omega)
  have hdeg := quadraticInverse_degree_of_le
    (actualLegendreJacobi p * actualVariationField p (by omega : 7 ≤ p)) (p / 6) hprod
  unfold QH
  rw [unitEuler_field_eq p _ (by omega)]

end WPFieldAssembly.ActualDeltaUNextSource
