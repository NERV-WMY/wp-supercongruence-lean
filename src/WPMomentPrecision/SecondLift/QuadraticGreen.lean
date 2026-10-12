import WPMomentPrecision.NativeSecondLift

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPActualRankTwoComparison WPActualNativeJacobiJet WPMomentPrecision.NativeSecondLift

namespace WPMomentPrecision.QuadraticGreen

set_option maxHeartbeats 1200000

/-- The complete polynomial numerator of qY² D[q(G'-2Y'G/Y)]. -/
noncomputable def green {K : Type*} [CommRing K] (Y G : K[X]) : K[X] :=
  (1 - X ^ 2) ^ 2 *
      (Y ^ 2 * G.derivative.derivative - 2 * Y * Y.derivative * G.derivative +
        (2 * Y.derivative ^ 2 - 2 * Y * Y.derivative.derivative) * G) -
    2 * X * (1 - X ^ 2) * (Y ^ 2 * G.derivative - 2 * Y * Y.derivative * G)

theorem green_sub {K : Type*} [CommRing K] (Y G H : K[X]) :
    green Y (G - H) = green Y G - green Y H := by
  simp only [green, derivative_sub]
  ring

theorem green_natCast_mul {K : Type*} [CommRing K] (n : ℕ) (Y G : K[X]) :
    green Y ((n : K[X]) * G) = (n : K[X]) * green Y G := by
  simp only [green, derivative_mul, derivative_natCast, zero_mul, zero_add]
  ring

/-- This product identity uses the whole polynomial Wronskian, without a rational primitive. -/
theorem green_square_wronskian {K : Type*} [CommRing K] (Y R : K[X]) :
    green Y (R ^ 2) =
      2 * ((1 - X ^ 2) * (Y * R.derivative - Y.derivative * R)) ^ 2 +
      2 * (1 - X ^ 2) * Y * R *
        ((1 - X ^ 2) * (Y * R.derivative - Y.derivative * R)).derivative := by
  simp only [green, derivative_mul, derivative_sub, derivative_sq, derivative_one,
    derivative_X, derivative_ofNat, zero_sub, C_ofNat]
  ring

/-- The actual divided rank-two polynomial retains the T^p part of NC55. -/
theorem actual_rank_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      (actualLegendreJacobi p * (actualRankDividedField p (by omega)).derivative -
        (actualLegendreJacobi p).derivative * actualRankDividedField p (by omega)) =
      X * actualLegendreJacobi p ^ 2 - X ^ p := by
  rw [actual_rankDividedField_eq_hat p hp]
  exact rankHatField_wronskian p hp

/-- The complete square contribution contains +2T^(2p); it cannot be projected away. -/
theorem actual_rank_square_green (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    green (actualLegendreJacobi p) (actualRankDividedField p (by omega) ^ 2) =
      4 * (1 - X ^ 2) * X * actualLegendreJacobi p ^ 3 *
        (actualRankDividedField p (by omega)).derivative +
      2 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
        actualRankDividedField p (by omega) -
      2 * X ^ 2 * actualLegendreJacobi p ^ 4 + 2 * X ^ (2 * p) := by
  have hW := actual_rank_wronskian p hp
  have hD := congrArg Polynomial.derivative hW
  have hF : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by
    simp [derivative_X_pow]
  have hXY : (X * actualLegendreJacobi p ^ 2).derivative =
      actualLegendreJacobi p ^ 2 +
        X * (2 * actualLegendreJacobi p * (actualLegendreJacobi p).derivative) := by
    simp only [derivative_mul, derivative_X, derivative_sq, C_ofNat, one_mul]
  rw [derivative_sub, hF, sub_zero, hXY] at hD
  rw [green_square_wronskian, hD, hW,
    show (X : (ZMod p)[X]) ^ (2 * p) = (X ^ p) ^ 2 by
      rw [Nat.mul_comm 2 p, pow_mul]]
  linear_combination -4 * X * actualLegendreJacobi p ^ 2 * hW

/-- The literal Qjet includes all of K through e and the original full R. -/
noncomputable def actualQuadraticJet (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] :=
  (integralFullSecondJacobi p hp).map (WPPIntegralReduction.residueHom p) -
    2 * actualRankDividedField p (by omega) ^ 2

/-- The full Green source before the logarithmic subtraction, including the forced +4 row. -/
noncomputable def actualQuadraticGreenSource (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] :=
  2 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
    (4 * X * (actualRankDividedField p (by omega)).derivative +
      2 * actualRankDividedField p (by omega) + 2 * actualLegendreJacobi p) +
    4 * (X ^ (2 * p) - 1)

/-- The actual logarithmic numerator is obtained by subtracting twice the full R square. -/
theorem actual_logarithmic_numerator_split (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualLogSecondNumeratorField p hp = actualQuadraticJet p hp -
      2 * actualRankDividedField p (by omega) ^ 2 := by
  rw [actual_log_second_numerator_field]
  unfold actualQuadraticJet
  ring

/-- Exact transport of the full Green defect to the logarithmic defect.
This equality displays why the +4(T^(2p)-1) source is mandatory. -/
theorem actual_logarithmic_green_defect (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    green (actualLegendreJacobi p) (actualLogSecondNumeratorField p hp) -
        4 * (actualLegendreJacobi p ^ 4 - 1) =
      green (actualLegendreJacobi p) (actualQuadraticJet p hp) -
        actualQuadraticGreenSource p hp := by
  have htwo : green (actualLegendreJacobi p)
      (2 * actualRankDividedField p (by omega) ^ 2) =
      2 * green (actualLegendreJacobi p) (actualRankDividedField p (by omega) ^ 2) :=
    green_natCast_mul 2 _ _
  rw [actual_logarithmic_numerator_split, green_sub, htwo,
    actual_rank_square_green p hp]
  unfold actualQuadraticGreenSource
  ring

/- GreenComplete.lean supplies the downstream actual source attachment
     green (actualLegendreJacobi p) (actualQuadraticJet p hp) =
       actualQuadraticGreenSource p hp.
   Its +4 coefficient comes from the actual full second native cutoff in
   GreenTop.lean. The defect equality above transports that source to IR28a
   for the literal logarithmic numerator. The subsequent Legendre/telescoping
   and derivative-kernel arguments are recorded in LogQuadraticRepresentation.lean,
   followed by the original-coordinate IR29 residue extraction. Each affected
   source cone remains subject to the root's strict check. No small-degree
   claim is made here for K itself; the separate NC75 y2/P2 attachment remains
   explicitly open in HJetYUAttachment.lean. -/

end WPMomentPrecision.QuadraticGreen
