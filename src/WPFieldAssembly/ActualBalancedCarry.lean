import WPFieldAssembly.ActualDeltaUNextSource
import WPFiniteCarry.NextLog

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeHasse
  WPActualRankTwoFirstLift WPActualRankTwoLegendreField
  WPActualRankTwoLowTaylor WPActualRankTwoHatLift
  WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.ResidualProjection
  WPFieldAssembly.ActualDeltaUNextSource WPFiniteCarry

namespace WPFieldAssembly.ActualBalancedCarry
set_option maxHeartbeats 1200000

private theorem field_prime_zero (p : ℕ) : (p : (ZMod p)[X]) = 0 := by
  change C (p : ZMod p) = 0
  rw [ZMod.natCast_self, C_0]

theorem QO_neg_local {K : Type*} [Field K] (p : ℕ) (P : K[X]) :
    QO p (-P) = -QO p P := by
  rw [show -P = C (-1 : K) * P by simp, QO_C_mul]
  ring


theorem QO_sub_local {K : Type*} [Field K] (p : ℕ) (P Q : K[X]) :
    QO p (P - Q) = QO p P - QO p Q := by
  rw [sub_eq_add_neg, QO_add, QO_neg_local]
  ring

theorem theta_add_local {K : Type*} [CommRing K] (P Q : K[X]) :
    theta (P + Q) = theta P + theta Q := by
  simp [theta, mul_add]

theorem theta_sub_local {K : Type*} [CommRing K] (P Q : K[X]) :
    theta (P - Q) = theta P - theta Q := by
  simp [theta, mul_sub]

theorem theta_C_mul_local {K : Type*} [CommRing K] (a : K) (P : K[X]) :
    theta (C a * P) = C a * theta P := by
  simp [theta, derivative_mul]
  ring

theorem theta_map_local {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : K[X]) :
    (theta P).map f = theta (P.map f) := by
  simp [theta, Polynomial.derivative_map]

variable (p : ℕ) [Fact p.Prime]

/-- The literal central-log version of the actual rational rank hat. -/
noncomputable def centralRankHat : ℚ[X] :=
  rationalLegendre (p / 6) *
    ((rationalCentralLog p).comp (1 - X ^ 2) -
      C (rationalHarmonic (p / 6))) -
    X ^ p * rationalProperJacobi (p / 6)

/-- The full central Green polynomial; its X^p term is retained. -/
noncomputable def centralGreenJ : ℚ[X] :=
  C (2 : ℚ) * (rationalLegendre (p / 6) * centralRankHat p)

/-- The specified rational central Green numerator. -/
noncomputable def centralGreenNumerator : ℚ :=
  -QO p (rationalLegendre (p / 6) * centralRankHat p) / 3 -
    QH p (rationalLegendre (p / 6) ^ 2) / 2 -
    WPFirstResidue.LiteralNormalization.literalR0 p

omit [Fact p.Prime] in
theorem centralGreenNumerator_eq_J :
    centralGreenNumerator p =
      -QO p (centralGreenJ p) / 6 -
        QH p (rationalLegendre (p / 6) ^ 2) / 2 -
        WPFirstResidue.LiteralNormalization.literalR0 p := by
  rw [centralGreenJ, QO_C_mul]
  unfold centralGreenNumerator
  ring

omit [Fact p.Prime] in
theorem centralRankHat_endpoint_one : (centralRankHat p).eval 1 = 0 := by
  simp only [centralRankHat, eval_sub, eval_mul, eval_comp,
    eval_C, eval_pow, eval_X, eval_one, one_pow,
    sub_self, rationalCentralLog_origin,
    rationalLegendre_endpoint_one, rationalProperJacobi_endpoint_one]
  ring

omit [Fact p.Prime] in
theorem centralGreenJ_endpoint_one : (centralGreenJ p).eval 1 = 0 := by
  simp [centralGreenJ, centralRankHat_endpoint_one]

theorem legendre_square_projection_zero (hp : 19 ≤ p) :
    QO p (rationalLegendre (p / 6) ^ 2) = 0 := by
  unfold QO
  apply low_correction_both_projections_zero p hp
  apply quadraticInverse_degree_of_le
  simpa only [pow_two, two_mul] using natDegree_mul_le_of_le
    (rationalLegendre_degree (p / 6)) (rationalLegendre_degree (p / 6))

/-- Exact rank-hat transport, with both logarithmic carry orders. -/
theorem actual_central_rank_hat_source (hp : 19 ≤ p) :
    rationalRankHat p = centralRankHat p +
      C (p : ℚ) * (rationalLegendre (p / 6) *
        (C (actualEvenLogEndpointCarry p) -
          (rationalSecondLog p).comp (1 - X ^ 2))) +
      C ((p : ℚ) ^ 2) * (rationalLegendre (p / 6) *
        ((integralLogRemainder p).map
          (integralRationals p).subtype).comp (1 - X ^ 2)) := by
  have h := actual_rational_evenLog_nextCarry p hp
  unfold rationalRankHat centralRankHat
  simp only [_root_.map_sub]
  linear_combination rationalLegendre (p / 6) * h

noncomputable def logPair : ℚ :=
  QO p (rationalLegendre (p / 6) ^ 2 *
    (rationalSecondLog p).comp (1 - X ^ 2))

noncomputable def logRemainderPair : ℚ :=
  QO p (rationalLegendre (p / 6) ^ 2 *
    ((integralLogRemainder p).map
      (integralRationals p).subtype).comp (1 - X ^ 2))

/-- The actual rational first line of SB71d, before division by p. -/
theorem actual_hat_central_green_source (hp : 19 ≤ p) :
    hatNumerator p = centralGreenNumerator p +
      (p : ℚ) * logPair p / 3 -
      (p : ℚ) ^ 2 * logRemainderPair p / 3 := by
  have hm : rationalLegendre (p / 6) * rationalRankHat p =
      rationalLegendre (p / 6) * centralRankHat p +
        C (p : ℚ) *
          (C (actualEvenLogEndpointCarry p) * rationalLegendre (p / 6) ^ 2 -
            rationalLegendre (p / 6) ^ 2 *
              (rationalSecondLog p).comp (1 - X ^ 2)) +
        C ((p : ℚ) ^ 2) * (rationalLegendre (p / 6) ^ 2 *
          ((integralLogRemainder p).map
            (integralRationals p).subtype).comp (1 - X ^ 2)) := by
    linear_combination rationalLegendre (p / 6) * actual_central_rank_hat_source p hp
  have hs := congrArg (QO p) hm
  simp only [QO_add, QO_sub_local, QO_C_mul,
    legendre_square_projection_zero p hp, mul_zero, zero_sub] at hs
  unfold hatNumerator centralGreenNumerator logPair logRemainderPair
  linear_combination -(1 / 3 : ℚ) * hs

noncomputable def logPairIntegral (hp : 19 ≤ p) : integralRationals p :=
  QOi p hp (integralLegendre p (p / 6) (by omega) ^ 2 *
    (integralSecondLog p).comp (1 - X ^ 2))

noncomputable def logRemainderPairIntegral (hp : 19 ≤ p) : integralRationals p :=
  QOi p hp (integralLegendre p (p / 6) (by omega) ^ 2 *
    (integralLogRemainder p).comp (1 - X ^ 2))

theorem logPairIntegral_value (hp : 19 ≤ p) :
    (logPairIntegral p hp).val = logPair p := by
  simp only [logPairIntegral, QOi_value,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    integralLegendre_value, integralSecondLog_value p hp]
  rfl

theorem logRemainderPairIntegral_value (hp : 19 ≤ p) :
    (logRemainderPairIntegral p hp).val = logRemainderPair p := by
  simp only [logRemainderPairIntegral, QOi_value,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, integralLegendre_value]
  rfl

theorem logPairIntegral_field (hp : 19 ≤ p) :
    residueHom p (logPairIntegral p hp) =
      QO p (actualLegendreJacobi p ^ 2 *
        (actualSecondLogField p).comp (1 - X ^ 2)) := by
  simp only [logPairIntegral, QOi_field,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_comp,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, integralLegendre_field]
  rfl

/-- The exact G_0/p witness obtained from the actual hat digit. -/
noncomputable def centralGreenDigitIntegral (hp : 19 ≤ p) : integralRationals p :=
  hatDigitIntegral p hp -
    (2 * integralSixth p (by omega)) * logPairIntegral p hp +
    (p : integralRationals p) * (2 * integralSixth p (by omega)) *
      logRemainderPairIntegral p hp

theorem centralGreenDigitIntegral_value (hp : 19 ≤ p) :
    (centralGreenDigitIntegral p hp).val = centralGreenNumerator p / (p : ℚ) := by
  change (hatDigitIntegral p hp).val -
    (2 * (1 / 6 : ℚ)) * (logPairIntegral p hp).val +
    (p : ℚ) * (2 * (1 / 6 : ℚ)) * (logRemainderPairIntegral p hp).val = _
  rw [hatDigitIntegral_value, logPairIntegral_value,
    logRemainderPairIntegral_value, actual_hat_central_green_source p hp]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp [hpq]
  ring

theorem actual_central_green_digit_integral (hp : 19 ≤ p) :
    centralGreenNumerator p / (p : ℚ) ∈ integralRationals p := by
  rw [← centralGreenDigitIntegral_value p hp]
  exact (centralGreenDigitIntegral p hp).property

/-- Actual first line of SB71d; the integral p² error is consumed exactly. -/
theorem actual_hat_central_green_digit (hp : 19 ≤ p) :
    residueHom p (hatDigitIntegral p hp) =
      residueHom p (centralGreenDigitIntegral p hp) +
        QO p (actualLegendreJacobi p ^ 2 *
          (actualSecondLogField p).comp (1 - X ^ 2)) / 3 := by
  have hi : hatDigitIntegral p hp = centralGreenDigitIntegral p hp +
      (2 * integralSixth p (by omega)) * logPairIntegral p hp -
      (p : integralRationals p) * (2 * integralSixth p (by omega)) *
        logRemainderPairIntegral p hp := by
    unfold centralGreenDigitIntegral
    ring
  rw [hi]
  simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_natCast, _root_.map_ofNat,
    integralSixth_field, logPairIntegral_field, ZMod.natCast_self,
    zero_mul, sub_zero]
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h3, h6]
  ring

/-- C_half is the complete central-binomial polynomial. -/
noncomputable def rationalCentralHalf : ℚ[X] :=
  1 + 2 * theta (rationalCentralLog p)

/-- The actual divided terminal forcing, including its integral p remainder. -/
noncomputable def terminalCarryIntegral : (integralRationals p)[X] :=
  2 * theta (integralSecondLog p) -
    2 * C (p : integralRationals p) * theta (integralLogRemainder p)

/-- Exact terminal source; no T^p derivative has been discarded. -/
theorem actual_terminal_carry_source (hp : 19 ≤ p) :
    C (p : ℚ) * (terminalCarryIntegral p).map (integralRationals p).subtype =
      rationalCentralHalf p - (1 - X) ^ ((p - 1) / 2) := by
  have ht := congrArg theta (rationalBinomialLog_firstTaylor p hp)
  simp only [theta_add_local, theta_sub_local, theta_C_mul_local] at ht
  simp only [_root_.map_pow, _root_.map_natCast] at ht
  have hb := rationalBinomialLog_source ((p - 1) / 2)
  simp only [terminalCarryIntegral,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
    _root_.map_natCast, Polynomial.map_natCast,
    theta_map_local, integralSecondLog_value p hp]
  unfold rationalCentralHalf
  linear_combination 2 * ht - hb

theorem actual_terminal_carry_value (hp : 19 ≤ p) :
    (terminalCarryIntegral p).map (integralRationals p).subtype =
      C (1 / (p : ℚ)) *
        (rationalCentralHalf p - (1 - X) ^ ((p - 1) / 2)) := by
  rw [← actual_terminal_carry_source p hp, ← mul_assoc, ← C_mul,
    one_div_mul_cancel (by positivity : (p : ℚ) ≠ 0), C_1, one_mul]

theorem actual_terminal_carry_pullback (hp : 19 ≤ p) :
    C (p : ℚ) * ((terminalCarryIntegral p).map
      (integralRationals p).subtype).comp (1 - X ^ 2) =
      (rationalCentralHalf p).comp (1 - X ^ 2) - X ^ (p - 1) := by
  have h := congrArg (fun P : ℚ[X] => P.comp (1 - X ^ 2))
    (actual_terminal_carry_source p hp)
  have hn : 2 * ((p - 1) / 2) = p - 1 := by
    have hh := WPActualEvenLogCarry.prime_half_identity p (by omega : 7 ≤ p)
    omega
  simp only [mul_comp, C_comp, sub_comp, pow_comp, one_comp, X_comp] at h
  rw [show (1 - (1 - X ^ 2) : ℚ[X]) = X ^ 2 by ring, ← pow_mul, hn] at h
  exact h

theorem actual_terminal_carry_field :
    (terminalCarryIntegral p).map (residueHom p) =
      2 * theta (actualSecondLogField p) := by
  simp only [terminalCarryIntegral, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_ofNat,
    _root_.map_natCast, Polynomial.map_natCast, field_prime_zero, theta_map_local,
    mul_zero, zero_mul, sub_zero, actualSecondLogField]

theorem actual_second_log_origin : (actualSecondLogField p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, actualSecondLogField, coeff_map,
    integralSecondLog, rankCoefficientPolynomial_coeff]
  simp

/-- Literal TC1 proper family, with all small denominators lifted integrally. -/
noncomputable def properEtaIntegral : ℕ → ((integralRationals p)[X])[X]
  | 0 => 0
  | 1 => -1
  | j + 2 =>
      C (C (smallIntegralInverse p (j + 2))) *
        ((C (C ((2 * j + 3 : ℕ) : integralRationals p)) - X) *
            C (X : (integralRationals p)[X]) * properEtaIntegral (j + 1) -
          (C (C ((j + 1 : ℕ) : integralRationals p)) - X) * properEtaIntegral j)

theorem polynomial_two_term_eval {R : Type*} [CommRing R] (P : R[X]) (t : R) :
    P.eval t = P.coeff 0 + t * P.coeff 1 + t ^ 2 * (P.divX.divX).eval t := by
  have h0 := congrArg (fun Q : R[X] => Q.eval t) (X_mul_divX_add P)
  have h1 := congrArg (fun Q : R[X] => Q.eval t) (X_mul_divX_add P.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX, Nat.zero_add] at h0 h1
  linear_combination -h0 - t * h1

noncomputable def properEtaOrigin : (integralRationals p)[X] :=
  (properEtaIntegral p (p / 6)).coeff 0

noncomputable def properEtaJet : (integralRationals p)[X] :=
  (properEtaIntegral p (p / 6)).coeff 1

noncomputable def balancedProperIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (properEtaIntegral p (p / 6)).eval
    (C ((p : integralRationals p) * (2 * integralSixth p (by omega))))

noncomputable def balancedProperRemainder (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C ((2 * integralSixth p (by omega)) ^ 2) *
    (properEtaIntegral p (p / 6)).divX.divX.eval
      (C ((p : integralRationals p) * (2 * integralSixth p (by omega))))

/-- Exact p² Taylor remainder of the literal normalized proper family. -/
theorem actual_balanced_proper_taylor (hp : 19 ≤ p) :
    balancedProperIntegral p hp = properEtaOrigin p +
      C (p : integralRationals p) *
        (C (2 * integralSixth p (by omega)) * properEtaJet p) +
      C ((p : integralRationals p) ^ 2) * balancedProperRemainder p hp := by
  have h := polynomial_two_term_eval (properEtaIntegral p (p / 6))
    (C ((p : integralRationals p) * (2 * integralSixth p (by omega))))
  dsimp only [balancedProperIntegral, properEtaOrigin,
    properEtaJet, balancedProperRemainder]
  simp only [_root_.map_mul, _root_.map_pow] at h ⊢
  linear_combination h

end WPFieldAssembly.ActualBalancedCarry
