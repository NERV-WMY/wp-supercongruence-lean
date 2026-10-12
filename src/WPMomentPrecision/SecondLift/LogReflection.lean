import WPMomentPrecision.SecondLift.LegendrePrimitive
import WPMomentPrecision.SecondLift.GreenComplete
import WPActualNativeDegree

open scoped Polynomial
open Polynomial WPActualNativeDegree WPActualNativeJacobiJet WPActualRankTwoProper
  WPActualRankTwoComparison WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPMomentPrecision.LegendrePrimitive WPMomentPrecision.NativeSecondLift
  WPMomentPrecision.SecondPolynomialKernel

namespace WPMomentPrecision.LogReflection

set_option maxHeartbeats 1800000

theorem neg_one_power_square {K : Type*} [CommRing K] (n : ℕ) :
    ((-1 : K) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, neg_one_sq, one_pow]

theorem quadratic_composition_reflection {K : Type*} [CommRing K] (P : K[X]) :
    (P.comp (1 - X ^ 2)).comp (-X) = P.comp (1 - X ^ 2) := by
  rw [comp_assoc]
  simp only [sub_comp, one_comp, pow_comp, X_comp, neg_sq]

theorem integerJacobiField_reflection (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integerJacobiField p n).comp (-X) = (-1 : (ZMod p)[X]) ^ n * integerJacobiField p n := by
  let a : (ZMod p)[X] := C (1 / 2 : ZMod p) * (1 - X)
  have ha : 2 * C (1 / 2 : ZMod p) = (1 : (ZMod p)[X]) := by
    have h := congrArg (C : ZMod p → (ZMod p)[X]) (field_half_identity p (by omega))
    simpa only [map_mul, map_ofNat, map_one] using h
  have hcoord : (1 - X : (ZMod p)[X]).comp a = a.comp (-X) := by
    simp only [sub_comp, one_comp, X_comp, a, mul_comp, C_comp]
    linear_combination -ha
  have h := congrArg (fun P : ℤ[X] =>
    (P.map (Int.castRingHom (ZMod p))).comp a)
    (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n)
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_one, Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_X,
    mul_comp, pow_comp, neg_comp, one_comp, comp_assoc, hcoord] at h
  rw [← comp_assoc] at h
  change (-1 : (ZMod p)[X]) ^ n * ((integerJacobiField p n).comp (-X)) =
    integerJacobiField p n at h
  have hs := neg_one_power_square (K := (ZMod p)[X]) n
  linear_combination (-1 : (ZMod p)[X]) ^ n * h -
    (integerJacobiField p n).comp (-X) * hs

theorem actual_Y_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLegendreJacobi p).comp (-X) =
      (-1 : (ZMod p)[X]) ^ (p / 6) * actualLegendreJacobi p := by
  rw [← integerJacobiField_actual]
  exact integerJacobiField_reflection p (p / 6) hp

theorem legendreLogPrimitive_reflection (p d : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (legendreLogPrimitive p d).comp (-X) = -legendreLogPrimitive p d := by
  induction d with
  | zero => simp [legendreLogPrimitive_zero]
  | succ d ih =>
    rw [legendreLogPrimitive_succ, sub_comp, mul_comp, mul_comp, C_comp, ih,
      integerJacobiField_reflection p (d + 1) hp, integerJacobiField_reflection p d hp]
    have hs : (-1 : (ZMod p)[X]) ^ (d + 1) * (-1 : (ZMod p)[X]) ^ d = -1 := by
      rw [pow_succ]
      have h := neg_one_power_square (K := (ZMod p)[X]) d
      linear_combination -h
    linear_combination -C (((d : ZMod p) + 1)⁻¹) * integerJacobiField p (d + 1) *
      integerJacobiField p d * hs

theorem derivative_comp_neg_X {K : Type*} [CommRing K] (P : K[X]) :
    (P.comp (-X)).derivative = -(P.derivative.comp (-X)) := by
  simp only [derivative_comp, derivative_neg, derivative_X, neg_one_mul]

theorem actual_R_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualRankDividedField p (by omega)).comp (-X) =
      (-1 : (ZMod p)[X]) ^ (p / 6) * actualRankDividedField p (by omega) := by
  let s := (-1 : (ZMod p)[X]) ^ (p / 6)
  have h := congrArg (fun P : (ZMod p)[X] => P.comp (-X))
    (actual_native_Jacobi_jet p hp)
  rw [nativeJacobiJet, quadratic_composition_reflection, ← nativeJacobiJet,
    actual_native_Jacobi_jet p hp] at h
  simp only [mul_comp, ofNat_comp, actual_Y_reflection p hp] at h
  have hs := neg_one_power_square (K := (ZMod p)[X]) (p / 6)
  have hz : 2 * actualLegendreJacobi p *
      ((actualRankDividedField p (by omega)).comp (-X) - s * actualRankDividedField p (by omega)) = 0 := by
    linear_combination -s * h -
      2 * actualLegendreJacobi p * (actualRankDividedField p (by omega)).comp (-X) * hs
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd (by norm_num : 0 < 2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp he)
    omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (Polynomial.C_ne_zero.mpr h2) (actualLegendreJacobi_nonzero p)))

theorem actual_logarithmic_numerator_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogSecondNumeratorField p hp).comp (-X) = actualLogSecondNumeratorField p hp := by
  rw [actual_log_second_numerator_field, sub_comp, mul_comp, ofNat_comp, pow_comp,
    actual_R_reflection p hp, mul_pow, neg_one_power_square, one_mul]
  have hK : (integralFullSecondJacobi p hp).map (WPPIntegralReduction.residueHom p) =
      ((WPMomentPrecision.FullNativeTaylor.integralFullSecondJetAt p
        (p - 1 - p / 6) (by omega) (by omega)).map (WPPIntegralReduction.residueHom p)).comp
          (1 - X ^ 2) := by
    rw [integralFullSecondJacobi, Polynomial.map_comp]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
  rw [hK, quadratic_composition_reflection]
  simp only [Nat.cast_ofNat]

/-- The proper numerator has the opposite integer parity, by the actual Wronskian and degree. -/
theorem actual_proper_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properLegendreJacobi p).comp (-X) =
      -((-1 : (ZMod p)[X]) ^ (p / 6) * properLegendreJacobi p) := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let s := (-1 : (ZMod p)[X]) ^ (p / 6)
  let P := n.comp (-X) + s * n
  have hw := properLegendreJacobi_wronskian p (by omega)
  have hc := congrArg (fun Q : (ZMod p)[X] => Q.comp (-X)) hw
  simp only [mul_comp, sub_comp, pow_comp, one_comp, X_comp,
    actual_Y_reflection p hp, neg_sq, mul_pow, neg_one_power_square, one_mul] at hc
  have hYd := congrArg Polynomial.derivative (actual_Y_reflection p hp)
  rw [derivative_comp_neg_X] at hYd
  have hsC : s = C ((-1 : ZMod p) ^ (p / 6)) := by
    dsimp only [s]
    simp only [map_pow, map_neg, map_one]
  have hsD : s.derivative = 0 := by rw [hsC, derivative_C]
  change -(Y.derivative.comp (-X)) = (s * Y).derivative at hYd
  simp only [derivative_mul, hsD, zero_mul, zero_add] at hYd
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro he
    have hz := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) he
    norm_num at hz
  have hP : Y * P.derivative - Y.derivative * P = 0 := by
    have hz : (1 - X ^ 2) * (Y * P.derivative - Y.derivative * P) = 0 := by
      simp only [P, derivative_add, derivative_mul, derivative_comp_neg_X,
        hsD, zero_mul, zero_add]
      have hs := neg_one_power_square (K := (ZMod p)[X]) (p / 6)
      linear_combination -s * hc + s * hw +
        (1 - X ^ 2) * ((n.derivative.comp (-X)) * Y + Y.derivative * (n.comp (-X))) * hs +
        (1 - X ^ 2) * s * (n.comp (-X)) * hYd
    exact (mul_eq_zero.mp hz).resolve_left hq
  obtain ⟨H, hH, _⟩ := proper_wronskian_kernel_division (1 - X ^ 2) Y n P
    (actualLegendreJacobi_nonzero p) hw hP
  have hn : n.natDegree < p / 6 := properLegendreJacobi_degree p (by omega)
  have hPdegree : P.natDegree < p / 6 := by
    have hnc : (n.comp (-X)).natDegree ≤ n.natDegree := by
      exact natDegree_comp_le.trans (by simp)
    have hsdeg : s.natDegree ≤ 0 := by simp [s]
    exact (natDegree_add_le_of_le hnc (natDegree_mul_le_of_le hsdeg (le_refl n.natDegree))).trans_lt
      (by omega)
  have hz : P = 0 := by
    by_cases hH0 : H = 0
    · rw [hH, hH0, mul_zero]
    · rw [hH, natDegree_mul (actualLegendreJacobi_nonzero p) hH0,
        actualLegendreJacobi_exact_degree p hp] at hPdegree
      omega
  exact eq_neg_of_add_eq_zero_left hz

end WPMomentPrecision.LogReflection
