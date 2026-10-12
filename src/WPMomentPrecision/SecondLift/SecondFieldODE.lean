import WPMomentPrecision.SecondLift.SecondCutoff

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeParameter WPActualNativeSecondTaylor
  WPActualNativeJetODE WPActualNativeJetRecurrence
  WPMomentPrecision.FullNativeTaylor WPMomentPrecision.SecondRecurrence
  WPMomentPrecision.SecondCutoff

namespace WPMomentPrecision.SecondFieldODE

set_option maxHeartbeats 1200000

noncomputable def fullSecondField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] :=
  (integralFullSecondJetAt p (p - 1 - p / 6) (by omega) (by omega)).map
    (WPPIntegralReduction.residueHom p)

theorem fullSecondField_coeff (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullSecondField p hp).coeff n = if n < p - 1 - p / 6 + 1 then
      (nativeFullSecondJetCoefficient p n : ZMod p) else 0 := by
  rw [fullSecondField, Polynomial.coeff_map]
  have hv := congrArg (fun P : ℚ[X] => P.coeff n)
    (integralFullSecondJetAt_value p (p - 1 - p / 6) (by omega) (by omega))
  rw [Polynomial.coeff_map] at hv
  change ((integralFullSecondJetAt p (p - 1 - p / 6)
    (by omega) (by omega)).coeff n).val =
      (fullSecondJetAt p (p - 1 - p / 6)).coeff n at hv
  change (((integralFullSecondJetAt p (p - 1 - p / 6)
    (by omega) (by omega)).coeff n).val : ZMod p) = _
  rw [hv, fullSecondJetAt, coefficientPolynomial_coeff]
  split_ifs
  · rfl
  · exact Rat.cast_zero

theorem fullSecondField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fullSecondField p hp).natDegree ≤ p - 1 - p / 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [fullSecondField_coeff, if_neg (by omega)]

noncomputable def secondForcedOperator {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  288 * theta F - X * (432 * theta F + 216 * F)

theorem secondForcedOperator_coeff_zero {K : Type*} [CommRing K] (F : K[X]) :
    (secondForcedOperator F).coeff 0 = 0 := by
  simp [secondForcedOperator, theta_coeff]

theorem secondForcedOperator_coeff_succ {K : Type*} [CommRing K]
    (F : K[X]) (n : ℕ) :
    (secondForcedOperator F).coeff (n + 1) =
      288 * ((n : K) + 1) * F.coeff (n + 1) -
        (432 * (n : K) + 216) * F.coeff n := by
  simp only [secondForcedOperator, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
    coeff_add, theta_coeff, Nat.cast_add, Nat.cast_one]
  ring

/-- The full K cutoff has the whole forced second source; its terminal row is proved. -/
theorem actual_full_second_field_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    clearedOperator (fullSecondField p hp) =
      -(2 * forcedOperator (nativeJetField p)) -
        secondForcedOperator (nativeField p (p / 6)) := by
  have hd := Nat.div_mul_le_self p 6
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hF (n : ℕ) (hn : n < p) : (nativeField p (p / 6)).coeff n =
      (WPReview.nativeCoefficient n : ZMod p) := by
    rw [nativeField_coeff]
    split_ifs with hnd
    · rfl
    · exact (actual_native_coefficient_field_tail p n (by omega) hn (by omega)).symm
  have hJ (n : ℕ) (hn : n < p) : (nativeJetField p).coeff n =
      (parameterJet n (-(p : ℚ) / 6) : ZMod p) := by
    rw [nativeJetField_coeff]
    split_ifs with hnd
    · rfl
    · exact (actual_firstJet_field_tail p hp n hn (by omega)).symm
  ext k
  cases k with
  | zero =>
    rw [clearedOperator_coeff_zero, coeff_sub, coeff_neg, coeff_ofNat_mul,
      forcedOperator_coeff_zero, secondForcedOperator_coeff_zero]
    ring
  | succ n =>
    rw [clearedOperator_coeff_succ, coeff_sub, coeff_neg, coeff_ofNat_mul,
      forcedOperator_coeff_succ, secondForcedOperator_coeff_succ,
      fullSecondField_coeff, fullSecondField_coeff]
    by_cases hn : n + 1 < p - 1 - p / 6 + 1
    · rw [if_pos hn, if_pos (by omega), hF (n + 1) (by omega), hF n (by omega),
        hJ (n + 1) (by omega), hJ n (by omega)]
      have h := actual_native_full_second_field_recurrence p n (by omega) (by omega)
      linear_combination h
    · rw [if_neg hn]
      by_cases hn0 : n < p - 1 - p / 6 + 1
      · rw [if_pos hn0, hF (n + 1) (by omega), hF n (by omega),
          hJ (n + 1) (by omega), hJ n (by omega)]
        have h := actual_native_full_second_field_recurrence p n (by omega) (by omega)
        rw [actual_full_second_field_tail p (n + 1) hp (by omega) (by omega)] at h
        linear_combination h
      · rw [if_neg hn0, nativeField_coeff, nativeField_coeff,
          nativeJetField_coeff, nativeJetField_coeff, if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        ring

end WPMomentPrecision.SecondFieldODE
