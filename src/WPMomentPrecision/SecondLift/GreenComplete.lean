import WPMomentPrecision.SecondLift.GreenDerivative
import WPMomentPrecision.SecondLift.PolynomialKernel

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPActualRankTwoComparison WPMomentPrecision.NativeSecondLift
  WPMomentPrecision.QuadraticGreen WPMomentPrecision.GreenTop
  WPMomentPrecision.GreenDerivative WPMomentPrecision.SecondPolynomialKernel

namespace WPMomentPrecision.GreenComplete

set_option maxHeartbeats 1600000

theorem derivative_kernel_two_endpoints_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (P : (ZMod p)[X]) (hdeg : P.natDegree < 2 * p) (hD : P.derivative = 0)
    (h1 : P.eval 1 = 0) (hm1 : P.eval (-1) = 0) : P = 0 := by
  have hs := derivative_kernel_shape p P hdeg hD
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hp1 : (-1 : ZMod p) ^ p = -1 := hodd.neg_one_pow
  have hplus := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hs
  have hminus := congrArg (fun Q : (ZMod p)[X] => Q.eval (-1)) hs
  simp only [eval_add, eval_C, eval_mul, eval_pow, eval_X, one_pow, mul_one,
    h1, hm1, hp1, mul_neg_one] at hplus hminus
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
    omega
  have hc0 : P.coeff 0 = 0 := by
    apply mul_left_cancel₀ h2
    linear_combination -hplus - hminus
  have hcp : P.coeff p = 0 := by linear_combination -hplus - hc0
  rw [hs, hc0, hcp, C_0, zero_mul, zero_add]

noncomputable def ordinaryGreenSource (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] :=
  2 * (1 - X ^ 2) * actualLegendreJacobi p ^ 3 *
    (4 * X * (actualRankDividedField p (by omega)).derivative +
      2 * actualRankDividedField p (by omega) + 2 * actualLegendreJacobi p)

theorem ordinaryGreenSource_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ordinaryGreenSource p hp).natDegree < 2 * p := by
  let d := p / 6
  let e := p - 1 - p / 6
  have hd := Nat.div_mul_le_self p 6
  have hsum : d + e + 1 = p := by dsimp [d, e]; omega
  have hY := actualLegendreJacobi_degree p
  have hR := actualRankDividedField_degree p (by omega)
  have hRD : (actualRankDividedField p (by omega)).derivative.natDegree ≤ e - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right hR 1)
  have hXR : (4 * X * (actualRankDividedField p (by omega)).derivative).natDegree ≤ e := by
    exact (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (4 : (ZMod p)[X]).natDegree ≤ 0 by simp)
        (show (X : (ZMod p)[X]).natDegree ≤ 1 by simp)) hRD).trans
      (by dsimp [e]; omega)
  have h2R : (2 * actualRankDividedField p (by omega)).natDegree ≤ e := by
    exact (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp) hR).trans
      (by omega)
  have h2Y : (2 * actualLegendreJacobi p).natDegree ≤ e := by
    exact (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp) hY).trans
      (by dsimp [d, e]; omega)
  have hW : (4 * X * (actualRankDividedField p (by omega)).derivative +
      2 * actualRankDividedField p (by omega) + 2 * actualLegendreJacobi p).natDegree ≤ e := by
    exact (natDegree_add_le_of_le (natDegree_add_le_of_le hXR h2R) h2Y).trans (by omega)
  have hq : (2 * (1 - X ^ 2) : (ZMod p)[X]).natDegree ≤ 2 := by
    exact (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_sub_le_of_le
        (show (1 : (ZMod p)[X]).natDegree ≤ 0 by simp)
        (natDegree_X_pow_le 2))).trans (by omega)
  have hbound : (ordinaryGreenSource p hp).natDegree ≤ 2 + 3 * d + e := by
    exact (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le hq (natDegree_pow_le_of_le 3 hY))
      hW).trans (by omega)
  exact hbound.trans_lt (by dsimp [d, e]; omega)

theorem actual_quadratic_green_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (green (actualLegendreJacobi p) (actualQuadraticJet p hp)).natDegree ≤ 2 * p := by
  let d := p / 6
  let e := p - 1 - p / 6
  have hd := Nat.div_mul_le_self p 6
  rw [green_firstOrder]
  have h := firstOrder_degree 1 (actualLegendreJacobi p)
    (firstOrder 2 (actualLegendreJacobi p) (actualQuadraticJet p hp)) d (d + 2 * e + 1)
    (by dsimp [d]; omega) (by omega) (actualLegendreJacobi_degree p)
    (firstOrder_degree 2 _ _ d (2 * e) (by dsimp [d]; omega)
      (by dsimp [e]; omega) (actualLegendreJacobi_degree p) (actual_quadratic_jet_degree p hp))
  exact h.trans (by dsimp [d, e]; omega)

theorem actual_quadratic_green_source_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualQuadraticGreenSource p hp).natDegree ≤ 2 * p := by
  have hF : (4 * (X ^ (2 * p) - 1) : (ZMod p)[X]).natDegree ≤ 2 * p := by
    exact (natDegree_mul_le_of_le (show (4 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_sub_le_of_le (natDegree_X_pow_le (2 * p))
        (show (1 : (ZMod p)[X]).natDegree ≤ 0 by simp))).trans (by omega)
  exact (natDegree_add_le_of_le (Nat.le_of_lt (ordinaryGreenSource_degree p hp)) hF).trans
    (by omega)

theorem actual_quadratic_green_source_top_four (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualQuadraticGreenSource p hp).coeff (2 * p) = 4 := by
  change (ordinaryGreenSource p hp + 4 * (X ^ (2 * p) - 1)).coeff (2 * p) = _
  rw [coeff_add, coeff_eq_zero_of_natDegree_lt (ordinaryGreenSource_degree p hp),
    coeff_ofNat_mul, coeff_sub, coeff_X_pow_self, coeff_one,
    if_neg (by omega : 2 * p ≠ 0)]
  ring

/-- The two geometric endpoints remove the possible constant and T^p kernel terms. -/
theorem actual_quadratic_green_identity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    green (actualLegendreJacobi p) (actualQuadraticJet p hp) =
      actualQuadraticGreenSource p hp := by
  let D := green (actualLegendreJacobi p) (actualQuadraticJet p hp) -
    actualQuadraticGreenSource p hp
  have hdeg : D.natDegree ≤ 2 * p :=
    (natDegree_sub_le_of_le (actual_quadratic_green_degree p hp)
      (actual_quadratic_green_source_degree p hp)).trans (by omega)
  have htop : D.coeff (2 * p) = 0 := by
    dsimp only [D]
    rw [coeff_sub, actual_quadratic_green_top_four p hp,
      actual_quadratic_green_source_top_four p hp, sub_self]
  have hlt : D.natDegree < 2 * p := by
    have hb : D.natDegree ≤ 2 * p - 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      by_cases he : n = 2 * p
      · simpa only [he] using htop
      · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))
    omega
  have h1 : D.eval 1 = 0 := by
    simp only [D, green, actualQuadraticGreenSource, eval_sub, eval_add, eval_mul,
      eval_pow, eval_X, eval_one, eval_ofNat, one_pow, sub_self, zero_pow
        (by norm_num : 2 ≠ 0), zero_mul, mul_zero, add_zero]
  have hm1 : D.eval (-1) = 0 := by
    have heven : (-1 : ZMod p) ^ (2 * p) = 1 := (even_two_mul p).neg_one_pow
    simp only [D, green, actualQuadraticGreenSource, eval_sub, eval_add, eval_mul,
      eval_pow, eval_X, eval_one, eval_ofNat, neg_one_sq, heven, sub_self, zero_pow
        (by norm_num : 2 ≠ 0), zero_mul, mul_zero, add_zero]
  have hz := derivative_kernel_two_endpoints_zero p (by omega) D hlt
    (actual_quadratic_green_defect_derivative_zero p hp) h1 hm1
  exact sub_eq_zero.mp hz

/-- Whole IR28a for the literal L2=K(q)-4R², retaining the full original cutoff. -/
theorem actual_logarithmic_green_identity (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    green (actualLegendreJacobi p) (actualLogSecondNumeratorField p hp) =
      4 * (actualLegendreJacobi p ^ 4 - 1) := by
  have h := actual_logarithmic_green_defect p hp
  rw [actual_quadratic_green_identity p hp, sub_self] at h
  exact sub_eq_zero.mp h

end WPMomentPrecision.GreenComplete
