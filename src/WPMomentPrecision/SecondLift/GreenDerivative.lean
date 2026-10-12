import WPMomentPrecision.SecondLift.GreenTop
import WPMomentPrecision.SecondLift.SecondFieldODE

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeJetODE WPActualNativeQuadraticSquare
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPActualRankTwoComparison WPActualNativeJacobiJet WPActualTerminatingSquare
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.QuadraticGreen WPMomentPrecision.SecondFieldODE

namespace WPMomentPrecision.GreenDerivative

set_option maxHeartbeats 2400000

noncomputable def forcedRegular {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  216 * X * (1 - X) * F.derivative.derivative +
    (216 - 432 * X) * F.derivative - 46 * F

noncomputable def secondForcedRegular {K : Type*} [CommRing K] (F : K[X]) : K[X] :=
  (288 - 432 * X) * F.derivative - 216 * F

noncomputable def jacobiLinear {K : Type*} [CommRing K] (G : K[X]) : K[X] :=
  -216 * X * (1 - X ^ 2) * G.derivative.derivative +
    (432 * X ^ 2 - 216 * (1 - X ^ 2)) * G.derivative + 184 * X * G

noncomputable def jacobiSecond {K : Type*} [CommRing K] (G : K[X]) : K[X] :=
  (576 * X ^ 2 - 288 * (1 - X ^ 2)) * G.derivative + 864 * X * G

theorem clearedOperator_regular {K : Type*} [CommRing K] (F : K[X]) :
    clearedOperator F = X * termRegular 0 F := by
  simp only [clearedOperator, termRegular, integerShift, theta, derivative_mul,
    derivative_add, derivative_one, derivative_X, map_zero,
    mul_zero, add_zero, C_1, map_ofNat, derivative_ofNat]
  have h5 : C (5 : K) = (5 : K[X]) := C_ofNat 5
  have h72 : C (72 : K) = (72 : K[X]) := C_ofNat 72
  have h226 : C (226 : K) = (226 : K[X]) := C_ofNat 226
  ring_nf
  rw [h72, h5, h226]

theorem forcedOperator_regular {K : Type*} [CommRing K] (F : K[X]) :
    forcedOperator F = X * forcedRegular F := by
  simp only [forcedOperator, forcedRegular, theta, derivative_mul, derivative_X]
  ring

theorem secondForcedOperator_regular {K : Type*} [CommRing K] (F : K[X]) :
    secondForcedOperator F = X * secondForcedRegular F := by
  simp only [secondForcedOperator, secondForcedRegular, theta]
  ring

theorem jacobiLinear_comp {K : Type*} [CommRing K] (F : K[X]) :
    jacobiLinear (F.comp (1 - X ^ 2)) =
      -4 * X * (forcedRegular F).comp (1 - X ^ 2) := by
  simp only [jacobiLinear, forcedRegular, derivative_comp, derivative_mul,
    derivative_sub, derivative_neg, derivative_C, derivative_one,
    derivative_X_pow, zero_sub, zero_mul, zero_add,
    mul_comp, add_comp, sub_comp, ofNat_comp, one_comp, X_comp]
  simp only [C_eq_natCast]
  ring

theorem jacobiSecond_comp {K : Type*} [CommRing K] (F : K[X]) :
    jacobiSecond (F.comp (1 - X ^ 2)) =
      -4 * X * (secondForcedRegular F).comp (1 - X ^ 2) := by
  simp only [jacobiSecond, secondForcedRegular, derivative_comp,
    derivative_sub, derivative_one, derivative_X_pow, zero_sub,
    mul_comp, sub_comp, ofNat_comp, X_comp]
  simp only [C_eq_natCast]
  ring

theorem actual_full_second_regular_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    termRegular 0 (fullSecondField p hp) + 2 * forcedRegular (nativeJetField p) +
      secondForcedRegular (nativeField p (p / 6)) = 0 := by
  have h := actual_full_second_field_ODE p hp
  rw [clearedOperator_regular, forcedOperator_regular, secondForcedOperator_regular] at h
  have hz : X * (termRegular 0 (fullSecondField p hp) +
      2 * forcedRegular (nativeJetField p) +
      secondForcedRegular (nativeField p (p / 6))) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left Polynomial.X_ne_zero

theorem actual_full_second_Jacobi_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    jacobiSquare 0 ((integralFullSecondJacobi p hp).map (WPPIntegralReduction.residueHom p)) +
      2 * jacobiLinear (2 * actualLegendreJacobi p * actualRankDividedField p (by omega)) +
      jacobiSecond (actualLegendreJacobi p ^ 2) = 0 := by
  have h := congrArg (fun P : (ZMod p)[X] => P.comp (1 - X ^ 2))
    (actual_full_second_regular_ODE p hp)
  simp only [add_comp, mul_comp, ofNat_comp, zero_comp] at h
  have hK : ((integralFullSecondJacobi p hp).map (WPPIntegralReduction.residueHom p)) =
      (fullSecondField p hp).comp (1 - X ^ 2) := by
    rw [integralFullSecondJacobi, Polynomial.map_comp]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    rfl
  rw [hK, termRegular_jacobi_source, ← actual_native_Jacobi_jet p hp,
    nativeJacobiJet, jacobiLinear_comp, ← actual_native_Jacobi_square p hp,
    jacobiSecond_comp]
  linear_combination -4 * X * h

theorem actual_rankClear_zero_operator (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) : rankJacobiClear 0 P = 36 * legendreJacobi (p / 6) P := by
  have hc := congrArg (C : ZMod p → (ZMod p)[X]) (rankField_eigenvalue p (by omega))
  simp only [map_mul, map_add, map_neg, map_ofNat, map_one] at hc
  simp only [rankJacobiClear, legendreJacobi, mul_zero, add_zero, C_1, C_mul]
  simp only [map_add, map_one, map_ofNat]
  linear_combination -P * hc

theorem actual_Y_rankClear_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankJacobiClear 0 (actualLegendreJacobi p) = 0 := by
  rw [actual_rankClear_zero_operator p hp,
    actualLegendreJacobi_source_zero p (by omega), mul_zero]

theorem actual_R_rankClear_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankJacobiClear 0 (actualRankDividedField p (by omega)) =
      36 * (2 * X * (actualLegendreJacobi p).derivative + actualLegendreJacobi p) := by
  rw [actual_rankClear_zero_operator p hp, actualRankDividedField_source p (by omega)]

/- The rejected incomplete generic identity omitted the R-source defect below.
Its six residual terms are exactly 16XY times
  36(1-X²)R'' - 72XR' - 5R - 36(2XY'+Y).
Over Q, Y=R=1 gives LHS=-1312X and the former RHS=-656X;
the missing defect is 16X(-5-36)=-656X.
Both actual source equations are used only after this complete identity. -/
/-- This identity keeps both rank-two defects before their actual source attachment. -/
theorem quadratic_forced_square_identity {K : Type*} [CommRing K] (Y R : K[X]) :
    -2 * jacobiLinear (2 * Y * R) - jacobiSecond (Y ^ 2) -
      2 * (2 * (1 - X ^ 2) * R * (36 * (2 * X * Y.derivative + Y)).derivative +
        (6 * (1 - X ^ 2) * R.derivative - 4 * X * R) *
          (36 * (2 * X * Y.derivative + Y))) =
      36 * (2 * (1 - X ^ 2) * Y *
          (4 * X * R.derivative + 2 * R + 2 * Y).derivative +
        (6 * (1 - X ^ 2) * Y.derivative - 4 * X * Y) *
          (4 * X * R.derivative + 2 * R + 2 * Y)) +
      16 * X * R * rankJacobiClear 0 Y +
      16 * X * Y * (rankJacobiClear 0 R - 36 * (2 * X * Y.derivative + Y)) := by
  simp only [jacobiLinear, jacobiSecond, rankJacobiClear, derivative_mul, derivative_add,
    derivative_sq, derivative_X, derivative_ofNat, C_ofNat, C_1,
    zero_mul, zero_add, mul_zero, add_zero, one_mul]
  ring

theorem jacobiSquare_natCast_mul {K : Type*} [CommRing K] (n : ℕ) (G : K[X]) :
    jacobiSquare 0 ((n : K[X]) * G) = (n : K[X]) * jacobiSquare 0 G := by
  simp only [jacobiSquare, derivative_mul, derivative_natCast, zero_mul, zero_add]
  ring

/-- The complete second native equation is attached to the actual divided rank polynomial. -/
theorem actual_quadratic_Jacobi_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    jacobiSquare 0 (actualQuadraticJet p hp) =
      36 * (2 * (1 - X ^ 2) * actualLegendreJacobi p *
          (4 * X * (actualRankDividedField p (by omega)).derivative +
            2 * actualRankDividedField p (by omega) + 2 * actualLegendreJacobi p).derivative +
        (6 * (1 - X ^ 2) * (actualLegendreJacobi p).derivative -
          4 * X * actualLegendreJacobi p) *
          (4 * X * (actualRankDividedField p (by omega)).derivative +
            2 * actualRankDividedField p (by omega) + 2 * actualLegendreJacobi p)) := by
  have hK := actual_full_second_Jacobi_source p hp
  have hS := quadratic_forced_square_identity (actualLegendreJacobi p)
    (actualRankDividedField p (by omega))
  rw [actual_Y_rankClear_zero p hp, actual_R_rankClear_source p hp,
    sub_self, mul_zero, add_zero] at hS
  have hR : jacobiSquare 0 (actualRankDividedField p (by omega) ^ 2) =
      2 * (1 - X ^ 2) * actualRankDividedField p (by omega) *
        (36 * (2 * X * (actualLegendreJacobi p).derivative + actualLegendreJacobi p)).derivative +
      (6 * (1 - X ^ 2) * (actualRankDividedField p (by omega)).derivative -
        4 * X * actualRankDividedField p (by omega)) *
        (36 * (2 * X * (actualLegendreJacobi p).derivative + actualLegendreJacobi p)) := by
    rw [jacobiSquare_source, actual_R_rankClear_source p hp]
    simp only [mul_zero, add_zero, C_1, mul_one]
  have htwo : jacobiSquare 0 (2 * actualRankDividedField p (by omega) ^ 2) =
      2 * jacobiSquare 0 (actualRankDividedField p (by omega) ^ 2) :=
    jacobiSquare_natCast_mul 2 _
  rw [actualQuadraticJet, jacobiSquare_sub, htwo, hR]
  linear_combination hK + hS

/-- The derivative of the complete cleared density has an explicit homogeneous defect. -/
theorem green_derivative_identity {K : Type*} [CommRing K] (Y G : K[X]) :
    36 * (green Y G).derivative = Y ^ 2 * jacobiSquare 0 G -
      4 * (1 - X ^ 2) * Y * G.derivative * rankJacobiClear 0 Y -
      2 * (1 - X ^ 2) * Y * G * (rankJacobiClear 0 Y).derivative +
      (2 * (1 - X ^ 2) * Y.derivative + 4 * X * Y) * G * rankJacobiClear 0 Y := by
  simp only [green, jacobiSquare, rankJacobiClear, derivative_mul, derivative_add,
    derivative_sub, derivative_sq, derivative_X, derivative_ofNat,
    derivative_one, C_ofNat, C_1, zero_mul, zero_add, mul_zero, add_zero, one_mul,
    zero_sub]
  have h5 : C (5 : K) = (5 : K[X]) := C_ofNat 5
  ring_nf
  rw [h5]
  ring

/-- Only the actual degree-2p Frobenius row can remain in the complete Green defect. -/
theorem actual_quadratic_green_defect_derivative_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (green (actualLegendreJacobi p) (actualQuadraticJet p hp) -
      actualQuadraticGreenSource p hp).derivative = 0 := by
  have hg := green_derivative_identity (actualLegendreJacobi p) (actualQuadraticJet p hp)
  rw [actual_Y_rankClear_zero p hp, derivative_zero] at hg
  simp only [mul_zero, sub_zero, add_zero] at hg
  rw [actual_quadratic_Jacobi_source p hp] at hg
  simp only [derivative_add, derivative_mul, derivative_X, derivative_ofNat,
    zero_mul, zero_add] at hg
  have hF : ((X : (ZMod p)[X]) ^ (2 * p)).derivative = 0 := by
    simp [derivative_X_pow, Nat.cast_mul]
  have hD : (36 : (ZMod p)[X]) *
      (green (actualLegendreJacobi p) (actualQuadraticJet p hp) -
        actualQuadraticGreenSource p hp).derivative = 0 := by
    simp only [actualQuadraticGreenSource, derivative_sub, derivative_add, derivative_mul,
      derivative_pow_succ, derivative_one, derivative_X,
      derivative_ofNat, hF, zero_sub, zero_mul, zero_add,
      mul_zero, add_zero, sub_zero]
    simp only [Nat.cast_ofNat, Nat.cast_one, map_add, map_one, map_ofNat]
    linear_combination hg
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 6)
      ((ZMod.natCast_eq_zero_iff 6 p).mp hz)
    omega
  have h36 : (36 : (ZMod p)[X]) ≠ 0 := by
    have h := pow_ne_zero 2 h6
    norm_num only [show (6 : ZMod p) ^ 2 = 36 by norm_num] at h
    exact Polynomial.C_ne_zero.mpr h
  exact (mul_eq_zero.mp hD).resolve_left h36

end WPMomentPrecision.GreenDerivative
