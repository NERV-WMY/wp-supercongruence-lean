import WPFieldAssembly.ActualResidualAssembly
import WPFiniteCarry.EndpointTransport
import WPFiniteLVSource

open scoped Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPFiniteCarry
  WPActualRankTwoParameter WPActualRankTwoLegendreField
  WPActualRankTwoFirstLift WPActualRankTwoComparison
  WPActualRankTwoProper WPActualRankTwoHatLift
  WPActualRankTwoLowTaylor WPActualRankTwoResidueSource
  WPActualGaussBottom WPActualGaussProper
  WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.ActualR0Node
  WPFieldAssembly.ActualDeltaUNextSource
  WPFieldAssembly.ActualNextHermite
  WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.ActualResidualAssembly
  WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.ResidualProjection

namespace WPFieldAssembly.ActualJointGreen

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The actual evaluated first polynomial, rather than its central reduction. -/
noncomputable def balancedLogPairIntegral (hp : 19 ≤ p) : integralRationals p :=
  QOi p hp (balancedFirstIntegral p hp ^ 2 *
    (integralSecondLog p).comp (1 - X ^ 2))

noncomputable def balancedLogRemainderPairIntegral (hp : 19 ≤ p) :
    integralRationals p :=
  QOi p hp (balancedFirstIntegral p hp ^ 2 *
    (integralLogRemainder p).comp (1 - X ^ 2))

theorem balancedLogPairIntegral_value (hp : 19 ≤ p) :
    (balancedLogPairIntegral p hp).val =
      QO p (rankJacobiNode p 1 ^ 2 *
        (rationalSecondLog p).comp (1 - X ^ 2)) := by
  simp only [balancedLogPairIntegral, QOi_value,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    balancedFirstIntegral_value, integralSecondLog_value p hp]

theorem balancedLogRemainderPairIntegral_value (hp : 19 ≤ p) :
    (balancedLogRemainderPairIntegral p hp).val =
      QO p (rankJacobiNode p 1 ^ 2 *
        ((integralLogRemainder p).map
          (integralRationals p).subtype).comp (1 - X ^ 2)) := by
  simp only [balancedLogRemainderPairIntegral, QOi_value,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    balancedFirstIntegral_value]

theorem balancedLogPairIntegral_field (hp : 19 ≤ p) :
    residueHom p (balancedLogPairIntegral p hp) =
      QO p (actualLegendreJacobi p ^ 2 *
        (actualSecondLogField p).comp (1 - X ^ 2)) := by
  simp only [balancedLogPairIntegral, QOi_field,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    balancedFirstIntegral_field]
  rfl

/-- Only the logarithm changes; the evaluated proper endpoint is retained. -/
noncomputable def finiteGreenJ (hp : 19 ≤ p) : ℚ[X] :=
  2 * rankJacobiNode p 1 ^ 2 *
    ((rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) +
      C ((balancedProperQ p hp).eval 1)) -
  2 * X ^ p * rankJacobiNode p 1 * balancedProperQ p hp

noncomputable def finiteGreenNumerator (hp : 19 ≤ p) : ℚ :=
  -QO p (finiteGreenJ p hp) / 6 - QH p (rankJacobiNode p 1 ^ 2) / 2 -
    WPFirstResidue.LiteralNormalization.literalR0 p

theorem actual_balanced_finite_log_polynomial (hp : 19 ≤ p) :
    balancedGreenJ p hp = finiteGreenJ p hp +
      C (2 * (p : ℚ)) * (rankJacobiNode p 1 ^ 2 *
        (rationalSecondLog p).comp (1 - X ^ 2)) -
      C (2 * (p : ℚ) ^ 2) * (rankJacobiNode p 1 ^ 2 *
        ((integralLogRemainder p).map
          (integralRationals p).subtype).comp (1 - X ^ 2)) := by
  have hL : rationalCentralLog p = rationalBinomialLog ((p - 1) / 2) +
      C (p : ℚ) * rationalSecondLog p -
      C ((p : ℚ) ^ 2) *
        (integralLogRemainder p).map (integralRationals p).subtype := by
    linear_combination -rationalBinomialLog_firstTaylor p hp
  rw [balancedGreenJ, finiteGreenJ, hL]
  simp only [add_comp, sub_comp, mul_comp, C_comp, map_mul, C_ofNat]
  ring

/-- Exact characteristic-zero identity, before the leading division. -/
theorem actual_balanced_finite_log_numerator (hp : 19 ≤ p) :
    balancedGreenNumerator p hp = finiteGreenNumerator p hp -
      (p : ℚ) / 3 * (balancedLogPairIntegral p hp).val +
      (p : ℚ) ^ 2 / 3 * (balancedLogRemainderPairIntegral p hp).val := by
  rw [balancedLogPairIntegral_value, balancedLogRemainderPairIntegral_value,
    balancedGreenNumerator, finiteGreenNumerator,
    actual_balanced_finite_log_polynomial p hp]
  simp only [QO_sub_local, QO_add, QO_C_mul]
  ring

/-- An actual integral witness for the specified finite-log numerator / p. -/
noncomputable def finiteGreenDigitIntegral (hp : 19 ≤ p) : integralRationals p :=
  balancedGreenDigitIntegral p hp +
    (2 * integralSixth p (by omega)) * balancedLogPairIntegral p hp -
    (p : integralRationals p) * (2 * integralSixth p (by omega)) *
      balancedLogRemainderPairIntegral p hp

theorem finiteGreenDigitIntegral_value (hp : 19 ≤ p) :
    (finiteGreenDigitIntegral p hp).val = finiteGreenNumerator p hp / (p : ℚ) := by
  change (balancedGreenDigitIntegral p hp).val +
    (2 * (1 / 6 : ℚ)) * (balancedLogPairIntegral p hp).val -
    (p : ℚ) * (2 * (1 / 6 : ℚ)) *
      (balancedLogRemainderPairIntegral p hp).val = _
  rw [balancedGreenDigitIntegral_value, actual_balanced_finite_log_numerator p hp]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp [hpq]
  ring

theorem finiteGreenDigitIntegral_field (hp : 19 ≤ p) :
    residueHom p (finiteGreenDigitIntegral p hp) =
      residueHom p (balancedGreenDigitIntegral p hp) +
        QO p (actualLegendreJacobi p ^ 2 *
          (actualSecondLogField p).comp (1 - X ^ 2)) / 3 := by
  simp only [finiteGreenDigitIntegral, map_add, map_sub, map_mul,
    map_natCast, map_ofNat, integralSixth_field,
    balancedLogPairIntegral_field, ZMod.natCast_self, zero_mul, sub_zero]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h3, h6]
  ring

/-- NC87 cancels the actual second-log source and its original-origin value. -/
theorem actual_finite_green_NC87 (hp : 19 ≤ p) :
    2 * residueHom p (balancedGreenDigitIntegral p hp) +
      (2 / 3 : ZMod p) * actualLowPair p +
      2 * (actualSecondLogField p).eval (4 / 125) =
      2 * residueHom p (finiteGreenDigitIntegral p hp) := by
  have he := actual_second_log_QO_NC87 p hp
  change QO p (actualLegendreJacobi p ^ 2 *
      (actualSecondLogField p).comp (1 - X ^ 2)) =
      actualLowPair p + 3 * (actualSecondLogField p).eval (4 / 125) at he
  rw [finiteGreenDigitIntegral_field, he]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  field_simp [h3]
  ring

/-- The full original norm, including j = 1, remains in this actual reduction. -/
theorem actual_residual_finite_log_source (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
      (originalNorm p : ZMod p) - nativeBpair p hp =
      2 * residueHom p (finiteGreenDigitIntegral p hp) +
        QO p (actualResidualPolynomial p hp) / 3 -
        (5 / 24 : ZMod p) * Ij p 1 (quadraticInverse
          (actualRankDividedField p (by omega) ^ 2)) - nativeBpair p hp := by
  rw [actual_residual_balanced_source p hp]
  linear_combination actual_finite_green_NC87 p hp

section UniversalPolynomials

variable {K : Type*} [Field K]

noncomputable def universalTbarP (p : ℕ) (h : K) : K[X] :=
  C ((2 : K)⁻¹) * (WPFiniteKSource.RP p +
    (WPFiniteKSource.RP p).comp (-X)) -
    C ((6 : K)⁻¹) * WPFiniteKSource.S2P p -
    C (h / 3) * WPFiniteKSource.LPsrc p

noncomputable def universalDunivP (p : ℕ) : K[X] :=
  C ((2 : K)⁻¹) * (WPFiniteKSource.RP p +
    (WPFiniteKSource.RP p).comp (-X) -
    (WPFiniteKSource.RP p).comp (1 - X) -
    (WPFiniteKSource.RP p).comp (1 + X) - WPFiniteKSource.EP p ^ 2)

theorem universalTbar_source_six (p : ℕ) (h : K)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    6 * universalTbarP p h = 6 * WPFiniteKSource.KsrcP p h +
      3 * (WPFiniteKSource.LPsrc p - C h) ^ 2 - 3 * C (h ^ 2) +
      6 * universalDunivP p := by
  have hu2 : (2 : K[X]) * C ((2 : K)⁻¹) = 1 := by
    change C (2 : K) * C ((2 : K)⁻¹) = C 1
    rw [← C_mul, mul_inv_cancel₀ h2]
  have hu3 : (3 : K[X]) * C ((3 : K)⁻¹) = 1 := by
    change C (3 : K) * C ((3 : K)⁻¹) = C 1
    rw [← C_mul, mul_inv_cancel₀ h3]
  unfold universalTbarP universalDunivP WPFiniteKSource.KsrcP WPFiniteKSource.LPsrc
  simp only [div_eq_mul_inv, map_sub, map_mul, map_pow, map_ofNat]
  linear_combination
    3 * (WPFiniteKSource.EP p ^ 2 -
      (C (WPFiniteNC122.q p : K)) ^ 2) * hu2 -
    6 * C h * (C (WPFiniteNC122.q p : K) + WPFiniteKSource.EP p) * hu3

end UniversalPolynomials

noncomputable def actualTbarP : (ZMod p)[X] :=
  universalTbarP p (fieldHarmonic p (p / 6))

/-- Whole polynomial contraction; the 2p proper band is still present. -/
theorem actual_Tbar_residual_polynomial (hp : 19 ≤ p) :
    C (2 : ZMod p) * (actualLegendreJacobi p ^ 2 * actualTbarP p) +
      actualResidualPolynomial p hp =
      C (2 : ZMod p) * (actualLegendreJacobi p ^ 2 * universalDunivP p) -
        C (fieldHarmonic p (p / 6) ^ 2) * actualLegendreJacobi p ^ 2 +
        C (2 : ZMod p) * (actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
        X ^ (2 * p) * properLegendreJacobi p ^ 2 := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let h := fieldHarmonic p (p / 6)
  let L : (ZMod p)[X] := WPFiniteKSource.LPsrc p
  let R := actualRankDividedField p (by omega : 7 ≤ p)
  have hr : R = Y * (L - C h) - X ^ p * n := by
    dsimp only [R]
    rw [WPActualRankTwoComparison.actual_rankDividedField_eq_hat p hp]
    dsimp only [rankHatField, Y, n, L, h,
      WPFiniteKSource.LPsrc, WPFiniteKSource.EP, WPFiniteNC122.q,
      evenLogPolynomial]
    simp only [map_sub]
    ring
  dsimp only [R] at hr
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have ht := universalTbar_source_six (K := ZMod p) p h h2 h3
  have hc : actualLowConstant p = (WPFiniteNC122.q p : ZMod p) - h := by rfl
  have hx : (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 := by
    rw [show 2 * p = p * 2 by omega, pow_mul]
  apply mul_left_cancel₀ (show (3 : (ZMod p)[X]) ≠ 0 from C_ne_zero.mpr h3)
  dsimp only [actualResidualPolynomial]
  rw [hr, hc, hx]
  change 3 * (C (2 : ZMod p) * (Y ^ 2 * actualTbarP p) +
      (C (-2 * ((WPFiniteNC122.q p : ZMod p) - h)) * (X ^ p * Y * n) -
        C (2 : ZMod p) * (Y ^ 2 * WPFiniteKSource.KsrcP p h) +
        C (2 : ZMod p) * (Y * n * WPFiniteKSource.OP p) -
        (Y * (L - C h) - X ^ p * n) ^ 2)) =
      3 * (C (2 : ZMod p) * (Y ^ 2 * universalDunivP p) - C (h ^ 2) * Y ^ 2 +
        C (2 : ZMod p) * (Y * n *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
        (X ^ p) ^ 2 * n ^ 2)
  dsimp only [actualTbarP, L, WPFiniteKSource.LPsrc] at *
  simp only [map_sub, map_mul, map_neg, map_ofNat] at *
  linear_combination Y ^ 2 * ht

/-- The h² term vanishes by its proved low degree; the full proper band survives. -/
theorem actual_Tbar_residual_QO (hp : 19 ≤ p) :
    2 * QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) +
      QO p (actualResidualPolynomial p hp) =
      2 * QO p (actualLegendreJacobi p ^ 2 * universalDunivP p +
        actualLegendreJacobi p * properLegendreJacobi p *
          (WPFiniteKSource.OP p + X ^ p * WPFiniteKSource.EP p)) -
        QO p (X ^ (2 * p) * properLegendreJacobi p ^ 2) := by
  have hF : QO p (actualLegendreJacobi p ^ 2) = 0 := by
    change Ij p 0 (ActualLowEuler.actualF p) = 0
    exact low_correction_both_projections_zero p hp _
      (ActualLowEuler.actualF_degree p hp) 0
  have he := congrArg (QO p) (actual_Tbar_residual_polynomial p hp)
  simp only [QO_add, QO_sub_local, QO_C_mul] at he
  rw [hF] at he
  simpa only [QO_add, mul_zero, sub_zero, mul_add] using he

/-- SB101's nonzero-end finite logarithm, with its original zero at T = 0. -/
noncomputable def finiteEvenLogQ : ℚ[X] :=
  (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) -
    C ((rationalBinomialLog ((p - 1) / 2)).eval 1)

noncomputable def finiteEvenLogIntegral : (integralRationals p)[X] :=
  (integralBinomialLog p).comp (1 - X ^ 2) - C ((integralBinomialLog p).eval 1)

theorem finiteEvenLogIntegral_value (hp : 19 ≤ p) :
    (finiteEvenLogIntegral p).map (integralRationals p).subtype = finiteEvenLogQ p := by
  unfold finiteEvenLogIntegral finiteEvenLogQ
  simp only [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
  rw [← eval_map_apply, integralBinomialLog_value p hp]
  simp only [map_one]

omit [Fact p.Prime] in
theorem finiteEvenLogQ_origin : (finiteEvenLogQ p).eval 0 = 0 := by
  simp [finiteEvenLogQ, eval_comp]

/-- Characteristic-zero finite-log differentiation, before any p-division. -/
theorem finiteEvenLogQ_source (hp : 19 ≤ p) :
    (1 - X ^ 2) * (finiteEvenLogQ p).derivative = (X - X ^ p : ℚ[X]) := by
  simp only [finiteEvenLogQ, derivative_sub, derivative_C, sub_zero]
  exact rationalBinomialLog_pullback_source p (by omega)

/-- Rejected SB101 attachment: this computes e_N(V), not e_N(T_t). -/
noncomputable def rejectedEvenAtVLogCIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(((p - 1) / 2 : ℕ) : integralRationals p) *
    ((finiteEvenLogIntegral p).comp
      (WPHasseIntegralTransport.integralV p (by omega))).coeff ((p - 1) / 2)

theorem rejectedEvenAtVLogCIntegral_value (hp : 19 ≤ p) :
    (rejectedEvenAtVLogCIntegral p hp).val = -(((p - 1) / 2 : ℕ) : ℚ) *
      ((finiteEvenLogQ p).comp
        WPActualPullbackSource.Vpolynomial).coeff ((p - 1) / 2) := by
  change -(((p - 1) / 2 : ℕ) : ℚ) *
    (integralRationals p).subtype
      (((finiteEvenLogIntegral p).comp
        (WPHasseIntegralTransport.integralV p (by omega))).coeff ((p - 1) / 2)) = _
  rw [← coeff_map, Polynomial.map_comp, finiteEvenLogIntegral_value p hp,
    WPHasseIntegralTransport.integralV_map_rational]

noncomputable def resInfinity (L : ℚ[T;T⁻¹]) : ℚ := -L.coeff (-1)

theorem shifted_derivative_resInfinity (N : ℕ) (P : ℚ[X]) :
    resInfinity (LaurentPolynomial.T (-(N : ℤ)) *
      WPFiniteLaurentDifferential.D P.toLaurent) = -(N : ℚ) * P.coeff N := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-(N : ℤ)) (-1)
    (WPFiniteLaurentDifferential.D P.toLaurent)
  simp only [map_one, one_mul] at hs
  rw [resInfinity, hs, WPFiniteLaurentDifferential.D_coeff]
  rw [show (-1 : ℤ) - -(N : ℤ) + 1 = (N : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]
  simp

/-- Valid only for the rejected e_N(V) display; it is not SB101f. -/
theorem rejectedEvenAtVLogC_residue (hp : 19 ≤ p) :
    resInfinity (LaurentPolynomial.T (-(((p - 1) / 2 : ℕ) : ℤ)) *
      WPFiniteLaurentDifferential.D (((finiteEvenLogQ p).comp
        WPActualPullbackSource.Vpolynomial).toLaurent)) =
      (rejectedEvenAtVLogCIntegral p hp).val := by
  rw [shifted_derivative_resInfinity, rejectedEvenAtVLogCIntegral_value p hp]

theorem resInfinity_add (L M : ℚ[T;T⁻¹]) :
    resInfinity (L + M) = resInfinity L + resInfinity M := by
  simp only [resInfinity, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  ring

theorem resInfinity_D (L : ℚ[T;T⁻¹]) :
    resInfinity (WPFiniteLaurentDifferential.D L) = 0 := by
  rw [resInfinity, WPFiniteLaurentDifferential.D_coeff]
  norm_num

theorem resInfinity_IBP (L M : ℚ[T;T⁻¹]) :
    resInfinity (L * WPFiniteLaurentDifferential.D M) =
      -resInfinity (M * WPFiniteLaurentDifferential.D L) := by
  have he := resInfinity_D (L * M)
  rw [WPFiniteLaurentDifferential.D_mul, resInfinity_add] at he
  rw [mul_comm (WPFiniteLaurentDifferential.D L) M] at he
  linear_combination he

theorem resInfinity_inversion (L : ℚ[T;T⁻¹]) :
    resInfinity L = (-LaurentPolynomial.T (-2) * LaurentPolynomial.invert L).coeff (-1) := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-2) (-1)
    (LaurentPolynomial.invert L)
  simp only [map_one, one_mul, LaurentPolynomial.invert_apply] at hs
  norm_num at hs
  rw [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, resInfinity,
    mul_comm (LaurentPolynomial.T (-2)) (LaurentPolynomial.invert L), hs]

private theorem rationalLog_origin (p : ℕ) :
    (WPActualRankTwoHatLift.rationalLogPolynomial p).eval 0 = 0 := by
  unfold WPActualRankTwoHatLift.rationalLogPolynomial
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).1
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by omega : j ≠ 0), mul_zero]

private theorem rationalEvenLog_origin (p : ℕ) :
    (WPActualRankTwoHatLift.rationalEvenLog p).eval 0 = 0 := by
  simp only [WPActualRankTwoHatLift.rationalEvenLog, eval_mul, eval_C,
    eval_add, eval_comp, eval_neg, eval_X, neg_zero, rationalLog_origin, zero_add, mul_zero]

theorem finiteEvenLogQ_eq_actual (hp : 19 ≤ p) :
    finiteEvenLogQ p = WPActualRankTwoHatLift.rationalEvenLog p := by
  have he := WPFiniteCarry.actual_rational_evenLog_binomial p (by omega)
  have hc := congrArg (fun P : ℚ[X] => P.eval 0) he
  simp only [rationalEvenLog_origin, eval_add, eval_C, eval_comp,
    eval_sub, eval_one, eval_pow, eval_X, zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero] at hc
  have hcP := congrArg (C : ℚ → ℚ[X]) hc
  simp only [map_zero, map_add] at hcP
  unfold finiteEvenLogQ
  linear_combination -he + hcP

theorem finiteEvenLogIntegral_eq_actual (hp : 19 ≤ p) :
    finiteEvenLogIntegral p = WPActualRankTwoHatLift.integralEvenLog p (by omega) := by
  apply Polynomial.map_injective (integralRationals p).subtype Subtype.val_injective
  rw [finiteEvenLogIntegral_value p hp,
    WPActualRankTwoHatLift.integralEvenLog_value, finiteEvenLogQ_eq_actual p hp]

theorem finiteEvenLogIntegral_field (hp : 19 ≤ p) :
    (finiteEvenLogIntegral p).map (residueHom p) = (WPFiniteKSource.EP p : (ZMod p)[X]) := by
  rw [finiteEvenLogIntegral_eq_actual p hp, WPActualRankTwoHatLift.integralEvenLog_field]
  rfl

noncomputable def finiteEvenSquaredIntegral : (integralRationals p)[X] :=
  contract 2 (finiteEvenLogIntegral p)

theorem finiteEvenSquaredIntegral_field (hp : 19 ≤ p) :
    (finiteEvenSquaredIntegral p).map (residueHom p) =
      (WPFiniteLVSource.evenSquared p : (ZMod p)[X]) := by
  rw [finiteEvenSquaredIntegral, Polynomial.map_contract (by norm_num : (2:ℕ) ≠ 0),
    finiteEvenLogIntegral_field p hp]
  have he := WPFiniteLVSource.evenSquared_square (K := ZMod p) p hp
  rw [← Polynomial.expand_eq_comp_X_pow] at he
  rw [← he, Polynomial.contract_expand 2 (by norm_num : (2:ℕ) ≠ 0)]

end WPFieldAssembly.ActualJointGreen
