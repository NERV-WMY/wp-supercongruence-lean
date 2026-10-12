import WPMomentPrecision.SecondLift.LogReflection

open scoped Polynomial
open Polynomial WPActualNativeDegree WPActualNativeJacobiJet WPActualRankTwoProper
  WPActualRankTwoComparison WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.QuadraticGreen
  WPMomentPrecision.GreenTop WPMomentPrecision.GreenComplete
  WPMomentPrecision.SecondPolynomialKernel WPMomentPrecision.LegendrePrimitive
  WPMomentPrecision.LogReflection

namespace WPMomentPrecision.LogDegree

set_option maxHeartbeats 2200000

/-- The ordinary proper numerator and the finite primitive clear the full first-order source. -/
theorem logarithmic_firstOrder_defect {K : Type*} [CommRing K] (Y L B n : K[X]) :
    firstOrder 1 Y (firstOrder 2 Y L - 4 * (B * Y - n)) = green Y L -
      4 * (Y ^ 2 * ((1 - X ^ 2) * B.derivative) -
        (1 - X ^ 2) * (Y * n.derivative - Y.derivative * n)) := by
  rw [green_firstOrder]
  simp only [firstOrder, derivative_sub, derivative_mul, derivative_C,
    derivative_ofNat, C_1, one_mul, zero_mul, zero_add]
  ring

theorem actual_logarithmic_degree_prebound (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogSecondNumeratorField p hp).natDegree ≤ 2 * (p - 1 - p / 6) := by
  rw [actual_logarithmic_numerator_split]
  have hR : (2 * actualRankDividedField p (by omega) ^ 2).natDegree ≤
      2 * (p - 1 - p / 6) := by
    exact (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_pow_le_of_le 2 (actualRankDividedField_degree p (by omega)))).trans (by omega)
  exact (natDegree_sub_le_of_le (actual_quadratic_jet_degree p hp) hR).trans (by omega)

theorem actual_logarithmic_firstOrder_identity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      (actualLegendreJacobi p * (actualLogSecondNumeratorField p hp).derivative -
        2 * (actualLegendreJacobi p).derivative * actualLogSecondNumeratorField p hp) =
      4 * (legendreLogPrimitive p (p / 6) * actualLegendreJacobi p - properLegendreJacobi p) := by
  let d := p / 6
  let e := p - 1 - p / 6
  let Y := actualLegendreJacobi p
  let L := actualLogSecondNumeratorField p hp
  let B := legendreLogPrimitive p d
  let n := properLegendreJacobi p
  let P := firstOrder 2 Y L - 4 * (B * Y - n)
  have hd := Nat.div_mul_le_self p 6
  have hY : Y ≠ 0 := actualLegendreJacobi_nonzero p
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro he
    have hz := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) he
    norm_num at hz
  have hB := actual_legendreLogPrimitive p hp
  have hY1 : Y.eval 1 = 1 := actualLegendreJacobi_endpoint_one p
  have hB1 : B.eval 1 = n.eval 1 := hB.2.1
  have hw := properLegendreJacobi_wronskian p (by omega)
  have hfirst : firstOrder 1 Y P = 0 := by
    dsimp only [P]
    rw [logarithmic_firstOrder_defect, actual_logarithmic_green_identity p hp,
      hB.1, hw]
    ring
  have hP : Y * P.derivative - Y.derivative * P = 0 := by
    change (1 - X ^ 2) * (Y * P.derivative - C 1 * Y.derivative * P) = 0 at hfirst
    rw [C_1, one_mul] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left hq
  obtain ⟨H, hH, hHD⟩ := proper_wronskian_kernel_division (1 - X ^ 2) Y n P hY hw hP
  have hPdegree : P.natDegree ≤ d + 2 * e + 1 := by
    have hfirstdeg := firstOrder_degree 2 Y L d (2 * e)
      (by dsimp [d]; omega) (by dsimp [e]; omega)
      (actualLegendreJacobi_degree p) (actual_logarithmic_degree_prebound p hp)
    have hBY := natDegree_mul_le_of_le hB.2.2 (actualLegendreJacobi_degree p)
    have hn := properLegendreJacobi_degree p (by omega)
    have hsource := natDegree_mul_le_of_le
      (show (4 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_sub_le_of_le hBY (Nat.le_of_lt hn))
    exact (natDegree_sub_le_of_le hfirstdeg hsource).trans
      (by dsimp [d, e] at *; omega)
  have hHdegree : H.natDegree < 2 * p := by
    by_cases hz : H = 0
    · simp only [hz, natDegree_zero]
      omega
    · rw [hH, natDegree_mul hY hz, actualLegendreJacobi_exact_degree p hp] at hPdegree
      dsimp only [d, e] at hPdegree
      omega
  have hP1 : P.eval 1 = 0 := by
    simp only [P, firstOrder, eval_sub, eval_mul, eval_pow, eval_X, eval_one,
      eval_ofNat, eval_C, one_pow, sub_self, zero_mul]
    rw [hY1, hB1]
    ring
  have hYm1 : Y.eval (-1) = (-1 : ZMod p) ^ d := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) (actual_Y_reflection p hp)
    simp only [eval_comp, eval_neg, eval_X, eval_mul, eval_pow, eval_one,
      actualLegendreJacobi_endpoint_one, mul_one] at h
    exact h
  have hBm1 : B.eval (-1) = -B.eval 1 := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) (legendreLogPrimitive_reflection p d hp)
    simpa only [eval_comp, eval_neg, eval_X] using h
  have hnm1 : n.eval (-1) = -((-1 : ZMod p) ^ d * n.eval 1) := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) (actual_proper_reflection p hp)
    simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_pow, eval_one] using h
  have hPm1 : P.eval (-1) = 0 := by
    simp only [P, firstOrder, eval_sub, eval_mul, eval_pow, eval_X, eval_one,
      eval_ofNat, eval_C, neg_one_sq, sub_self, zero_mul, hYm1, hBm1, hnm1]
    rw [hB1]
    ring
  have hH1 : H.eval 1 = 0 := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hH
    simpa only [eval_mul, hY1, one_mul, hP1] using h.symm
  have hHm1 : H.eval (-1) = 0 := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval (-1)) hH
    rw [hPm1, eval_mul, hYm1] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero d (neg_ne_zero.mpr one_ne_zero))
  have hHzero := derivative_kernel_two_endpoints_zero p (by omega) H hHdegree hHD hH1 hHm1
  have hPzero : P = 0 := by rw [hH, hHzero, mul_zero]
  exact sub_eq_zero.mp hPzero

theorem reflection_even_natDegree (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (P : (ZMod p)[X]) (hP : P.comp (-X) = P) : Even P.natDegree := by
  by_cases hz : P = 0
  · simp [hz]
  by_contra he
  have hodd := Nat.not_even_iff_odd.mp he
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff P.natDegree) hP
  rw [show (-X : (ZMod p)[X]) = C (-1) * X by simp,
    comp_C_mul_X_coeff, hodd.neg_one_pow] at hc
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have := Nat.le_of_dvd (by norm_num : 0 < 2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hzero)
    omega
  have hh : (2 : ZMod p) * P.coeff P.natDegree = 0 := by linear_combination -hc
  exact (leadingCoeff_ne_zero.mpr hz) ((mul_eq_zero.mp hh).resolve_left h2)

/-- IR28's small degree belongs to the logarithmic subtraction, never to the full K. -/
theorem actual_logarithmic_second_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogSecondNumeratorField p hp).natDegree ≤ 2 * (p / 6) := by
  let S := 4 * (legendreLogPrimitive p (p / 6) * actualLegendreJacobi p - properLegendreJacobi p)
  have hd := Nat.div_mul_le_self p 6
  have hS : S.natDegree ≤ 3 * (p / 6) - 1 := by
    have hBY := natDegree_mul_le_of_le (actual_legendreLogPrimitive p hp).2.2
      (actualLegendreJacobi_degree p)
    have hn := properLegendreJacobi_degree p (by omega)
    exact (natDegree_mul_le_of_le (show (4 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_sub_le_of_le hBY (Nat.le_of_lt hn))).trans (by omega)
  exact logarithmic_operator_degree_bound p (p / 6) (by omega)
    (actualLegendreJacobi p) (actualLogSecondNumeratorField p hp) S (by omega)
    (actualLegendreJacobi_nonzero p) (actualLegendreJacobi_exact_degree p hp)
    ((actual_logarithmic_degree_prebound p hp).trans_lt (by omega))
    (reflection_even_natDegree p (by omega) _ (actual_logarithmic_numerator_even p hp))
    hS (actual_logarithmic_firstOrder_identity p hp)

end WPMomentPrecision.LogDegree
