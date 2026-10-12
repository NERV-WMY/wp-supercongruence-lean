import WPMomentPrecision.SecondLift.TopCoefficients

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoLegendreField
  WPActualRankTwoResidueSource WPActualRankTwoComparison
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.QuadraticGreen WPMomentPrecision.TopCoefficients

namespace WPMomentPrecision.GreenTop

set_option maxHeartbeats 1200000

noncomputable def firstOrder {K : Type*} [CommRing K]
    (c : K) (Y G : K[X]) : K[X] :=
  (1 - X ^ 2) * (Y * G.derivative - C c * Y.derivative * G)

theorem firstOrder_degree {K : Type*} [CommRing K]
    (c : K) (Y G : K[X]) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hY : Y.natDegree ≤ d) (hG : G.natDegree ≤ m) :
    (firstOrder c Y G).natDegree ≤ d + m + 1 := by
  have hYD := (natDegree_derivative_le Y).trans (Nat.sub_le_sub_right hY 1)
  have hGD := (natDegree_derivative_le G).trans (Nat.sub_le_sub_right hG 1)
  have hA := natDegree_mul_le_of_le hY hGD
  have hB : (C c * Y.derivative * G).natDegree ≤ d - 1 + m := by
    exact (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (C c).natDegree ≤ 0 by simp) hYD) hG).trans (by omega)
  have hW := natDegree_sub_le_of_le hA hB
  have hq : (1 - X ^ 2 : K[X]).natDegree ≤ 2 :=
    natDegree_sub_le_of_le
      (show (1 : K[X]).natDegree ≤ 0 by simp) (natDegree_X_pow_le 2)
  exact (natDegree_mul_le_of_le hq hW).trans (by omega)

theorem firstOrder_top {K : Type*} [CommRing K]
    (c : K) (Y G : K[X]) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hY : Y.natDegree ≤ d) (hG : G.natDegree ≤ m) :
    (firstOrder c Y G).coeff (d + m + 1) =
      -(Y.coeff d * G.coeff m * ((m : K) - c * (d : K))) := by
  let W := Y * G.derivative - C c * Y.derivative * G
  have hYD := (natDegree_derivative_le Y).trans (Nat.sub_le_sub_right hY 1)
  have hGD := (natDegree_derivative_le G).trans (Nat.sub_le_sub_right hG 1)
  have hA := natDegree_mul_le_of_le hY hGD
  have hB : (C c * Y.derivative * G).natDegree ≤ d - 1 + m := by
    exact (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (C c).natDegree ≤ 0 by simp) hYD) hG).trans (by omega)
  have hW : W.natDegree ≤ d + m - 1 :=
    (natDegree_sub_le_of_le hA hB).trans (by omega)
  have hAC : (Y * G.derivative).coeff (d + m - 1) =
      Y.coeff d * G.coeff m * (m : K) := by
    rw [show d + m - 1 = d + (m - 1) by omega,
      coeff_mul_add_eq_of_natDegree_le hY hGD, coeff_derivative,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    ring
  have hBC : (Y.derivative * G).coeff (d + m - 1) =
      Y.coeff d * (d : K) * G.coeff m := by
    rw [show d + m - 1 = (d - 1) + m by omega,
      coeff_mul_add_eq_of_natDegree_le hYD hG, coeff_derivative,
      Nat.sub_add_cancel (by omega : 1 ≤ d)]
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  have hWC : W.coeff (d + m - 1) =
      Y.coeff d * G.coeff m * ((m : K) - c * (d : K)) := by
    dsimp only [W]
    rw [coeff_sub, mul_assoc, coeff_C_mul, hAC, hBC]
    ring
  have hzero : W.coeff (d + m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hW.trans_lt (by omega))
  change ((1 - X ^ 2) * W).coeff (d + m + 1) = _
  rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul',
    if_pos (by omega : 2 ≤ d + m + 1), hzero,
    show d + m + 1 - 2 = d + m - 1 by omega, hWC]
  ring

/-- Clearing the logarithmic density is the composition of these two first-order operators. -/
theorem green_firstOrder {K : Type*} [CommRing K] (Y G : K[X]) :
    green Y G = firstOrder 1 Y (firstOrder 2 Y G) := by
  simp only [firstOrder, green, derivative_mul, derivative_sub,
    derivative_one, derivative_ofNat, derivative_X_pow, C_ofNat,
    zero_mul, zero_sub, C_1, one_mul]
  simp only [C_eq_natCast]
  ring

theorem green_top {K : Type*} [CommRing K]
    (Y G : K[X]) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hY : Y.natDegree ≤ d) (hG : G.natDegree ≤ m) :
    (green Y G).coeff (2 * d + m + 2) =
      Y.coeff d ^ 2 * G.coeff m * ((m : K) + 1) * ((m : K) - 2 * (d : K)) := by
  rw [green_firstOrder,
    show 2 * d + m + 2 = d + (d + m + 1) + 1 by omega,
    firstOrder_top 1 Y (firstOrder 2 Y G) d (d + m + 1) hd (by omega) hY
      (firstOrder_degree 2 Y G d m hd hm hY hG),
    firstOrder_top 2 Y G d m hd hm hY hG]
  push_cast
  ring

theorem wronskian_top_normalization (p d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hde : d + e + 1 = p) (hsmall : 2 * d < p - 1)
    (Y R : (ZMod p)[X]) (hY : Y.natDegree ≤ d) (hR : R.natDegree ≤ e)
    (hW : firstOrder 1 Y R = X * Y ^ 2 - X ^ p) :
    Y.coeff d * R.coeff e * (1 + 2 * (d : ZMod p)) = -1 := by
  have h := congrArg (fun P : (ZMod p)[X] => P.coeff (d + e + 1))
    hW
  have hXY : (X * Y ^ 2).coeff p = (Y ^ 2).coeff (p - 1) := by
    simpa only [pow_one, if_pos (by omega : 1 ≤ p)] using coeff_X_pow_mul' (Y ^ 2) 1 p
  rw [firstOrder_top 1 Y R d e hd he hY hR, hde, coeff_sub, hXY,
    coeff_eq_zero_of_natDegree_lt
      ((natDegree_pow_le_of_le 2 hY).trans_lt hsmall),
    coeff_X_pow_self, zero_sub] at h
  have hcast : (d : ZMod p) + (e : ZMod p) + 1 = 0 := by
    have hn := congrArg (fun n : ℕ => (n : ZMod p)) hde
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hn
  linear_combination h + Y.coeff d * R.coeff e * hcast

/-- The actual T^p Wronskian fixes the product of the original leading coefficients. -/
theorem actual_rank_top_normalization (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLegendreJacobi p).coeff (p / 6) *
      (actualRankDividedField p (by omega)).coeff (p - 1 - p / 6) *
        (1 + 2 * ((p / 6 : ℕ) : ZMod p)) = -1 := by
  have hd := Nat.div_mul_le_self p 6
  apply wronskian_top_normalization p (p / 6) (p - 1 - p / 6)
    (by omega) (by omega) (by omega) (by omega)
    (actualLegendreJacobi p) (actualRankDividedField p (by omega))
    (actualLegendreJacobi_degree p) (actualRankDividedField_degree p (by omega))
  simpa only [firstOrder, C_1, one_mul] using actual_rank_wronskian p hp

theorem actual_quadratic_jet_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualQuadraticJet p hp).natDegree ≤ 2 * (p - 1 - p / 6) := by
  have hq : (1 - X ^ 2 : (integralRationals p)[X]).natDegree ≤ 2 :=
    natDegree_sub_le_of_le
      (show (1 : (integralRationals p)[X]).natDegree ≤ 0 by simp)
      (natDegree_X_pow_le 2)
  have hK := natDegree_map_le (p := integralFullSecondJacobi p hp)
    (f := residueHom p)
  have hcomp := natDegree_comp_le
    (p := integralFullSecondJetAt p (p - 1 - p / 6) (by omega) (by omega))
    (q := 1 - X ^ 2)
  have hKbound : ((integralFullSecondJacobi p hp).map (residueHom p)).natDegree ≤
      2 * (p - 1 - p / 6) := by
    apply hK.trans
    change ((integralFullSecondJetAt p (p - 1 - p / 6) (by omega) (by omega)).comp
      (1 - X ^ 2)).natDegree ≤ _
    exact hcomp.trans ((Nat.mul_le_mul (integral_full_second_degree p hp) hq).trans
      (by omega))
  have hRbound : (2 * actualRankDividedField p (by omega) ^ 2).natDegree ≤
      2 * (p - 1 - p / 6) := by
    exact (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp)
      (natDegree_pow_le_of_le 2 (actualRankDividedField_degree p (by omega)))).trans (by omega)
  simpa only [actualQuadraticJet, max_self] using natDegree_sub_le_of_le hKbound hRbound

/-- The full actual native source forces the coefficient +4 at the complete 2p endpoint. -/
theorem actual_quadratic_green_top_four (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (green (actualLegendreJacobi p) (actualQuadraticJet p hp)).coeff (2 * p) = 4 := by
  let d := p / 6
  let e := p - 1 - p / 6
  let y := (actualLegendreJacobi p).coeff d
  let r := (actualRankDividedField p (by omega)).coeff e
  have hd := Nat.div_mul_le_self p 6
  have hsum : d + e + 1 = p := by dsimp [d, e]; omega
  have hcast : (d : ZMod p) + (e : ZMod p) + 1 = 0 := by
    have hn := congrArg (fun n : ℕ => (n : ZMod p)) hsum
    simpa only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] using hn
  have hnorm := actual_rank_top_normalization p hp
  change y * r * (1 + 2 * (d : ZMod p)) = -1 at hnorm
  have htop := green_top (actualLegendreJacobi p) (actualQuadraticJet p hp) d (2 * e)
    (by dsimp [d]; omega) (by dsimp [e]; omega)
    (actualLegendreJacobi_degree p) (actual_quadratic_jet_degree p hp)
  rw [show 2 * d + 2 * e + 2 = 2 * p by omega,
    actual_quadratic_jet_top_square p hp] at htop
  change _ = y ^ 2 * (2 * r ^ 2) * (((2 * e : ℕ) : ZMod p) + 1) *
    (((2 * e : ℕ) : ZMod p) - 2 * (d : ZMod p)) at htop
  push_cast at htop
  rw [show (e : ZMod p) = -(d : ZMod p) - 1 by linear_combination hcast] at htop
  have hs := congrArg (fun x : ZMod p => x ^ 2) hnorm
  linear_combination htop + 4 * hs

end WPMomentPrecision.GreenTop
