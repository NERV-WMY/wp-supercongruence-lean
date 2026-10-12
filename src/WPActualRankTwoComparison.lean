import WPActualRankTwoFiniteLegendre
import WPFiniteAffineLog

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualGaussBottom WPActualGaussProper
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualRankTwoFiniteLegendre WPActualRankTwoResidueSource WPFiniteAffineLog
  WPActualRankTwoFirstLift

namespace WPActualRankTwoComparison

set_option maxHeartbeats 800000

/-- The literal complete even finite logarithm, retaining all exponents through p-1. -/
noncomputable def evenLogPolynomial (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C (2 : ZMod p)⁻¹ * ((LP p) + (LP p).comp (-X))

theorem evenLogPolynomial_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (evenLogPolynomial p).derivative =
      C (2 : ZMod p)⁻¹ * ((1 - X) ^ (p - 1) - (1 + X) ^ (p - 1)) := by
  have hpred : Even (p - 1) := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n, by omega⟩
  rw [evenLogPolynomial, derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
    derivative_comp, derivative_neg, derivative_X, LP_derivative_closed_eq]
  simp only [sub_comp, pow_comp, one_comp, X_comp, sub_neg_eq_add]
  rw [hpred.neg_pow]
  ring

theorem evenLogPolynomial_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (evenLogPolynomial p).derivative = X - X ^ p := by
  have hminus : (1 - X ^ 2 : (ZMod p)[X]) * (1 - X) ^ (p - 1) =
      (1 + X) * (1 - X ^ p) := by
    calc
      _ = (1 + X) * (((1 : (ZMod p)[X]) - X) * (1 - X) ^ (p - 1)) := by ring
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), sub_pow_char (1 : (ZMod p)[X]) X, one_pow]
  have hplus : (1 - X ^ 2 : (ZMod p)[X]) * (1 + X) ^ (p - 1) =
      (1 - X) * (1 + X ^ p) := by
    calc
      _ = (1 - X) * (((1 : (ZMod p)[X]) + X) * (1 + X) ^ (p - 1)) := by ring
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), add_pow_char (1 : (ZMod p)[X]) X, one_pow]
  have haP : (2 : (ZMod p)[X]) * C (2 : ZMod p)⁻¹ = 1 := by
    have h := congrArg (C : ZMod p → (ZMod p)[X]) (field_half_identity p (by omega))
    simpa only [one_div, map_mul, map_ofNat, map_one] using h
  rw [evenLogPolynomial_derivative p hp]
  linear_combination C (2 : ZMod p)⁻¹ * hminus - C (2 : ZMod p)⁻¹ * hplus + (X - X ^ p) * haP

theorem evenLogPolynomial_degree (p : ℕ) [Fact p.Prime] :
    (evenLogPolynomial p).natDegree ≤ p - 1 := by
  have hc : (-X : (ZMod p)[X]).natDegree ≤ 1 := by simp
  have hn : ((LP p : (ZMod p)[X]).comp (-X)).natDegree ≤ p - 1 :=
    (Polynomial.natDegree_comp_le (p := (LP p : (ZMod p)[X])) (q := (-X : (ZMod p)[X]))).trans
      ((Nat.mul_le_mul (LP_natDegree_le p) hc).trans (by simp))
  unfold evenLogPolynomial
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa only [Nat.max_self] using Polynomial.natDegree_add_le_of_le (LP_natDegree_le p) hn)

theorem evenLogPolynomial_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (evenLogPolynomial p).eval 1 = -(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hi : (2 : ZMod p)⁻¹ * (1 + 1) = 1 := by
    convert inv_mul_cancel₀ h2 using 1; ring
  have hL : (LP p : (ZMod p)[X]).eval 1 = 0 := by
    rw [LP_eval_eq]
    change WPFiniteInversion.ell p 1 = 0
    exact WPFiniteInversion.ell_one_eq_zero p (by omega)
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) (affine_log_polynomial (K := ZMod p) p hp)
  have he : (LP p : (ZMod p)[X]).eval ((2 : ZMod p)⁻¹ * (1 + 1)) =
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) + (evenLogPolynomial p).eval 1 := by
    simpa only [evenLogPolynomial, eval_comp, eval_mul, eval_C, eval_add, eval_one, eval_X] using h
  rw [hi, hL] at he
  exact eq_neg_of_add_eq_zero_right he.symm

theorem legendreJacobi_sub {K : Type*} [CommRing K] (d : ℕ) (P Q : K[X]) :
    legendreJacobi d (P - Q) = legendreJacobi d P - legendreJacobi d Q := by
  simp [legendreJacobi, derivative_sub]
  ring

theorem legendreJacobi_product {K : Type*} [CommRing K] (d : ℕ) (P Q : K[X]) :
    legendreJacobi d (P * Q) = Q * legendreJacobi d P +
      P * ((1 - X ^ 2) * Q.derivative.derivative - 2 * X * Q.derivative) +
        2 * (1 - X ^ 2) * P.derivative * Q.derivative := by
  simp [legendreJacobi, derivative_mul]
  ring

theorem legendreJacobi_flat_product {K : Type*} [CommRing K] (d : ℕ) (P Q : K[X])
    (hP : P.derivative = 0) : legendreJacobi d (P * Q) = P * legendreJacobi d Q := by
  simp [legendreJacobi, derivative_mul, hP]
  ring

theorem actualLegendreJacobi_degree (p : ℕ) [Fact p.Prime] :
    (actualLegendreJacobi p).natDegree ≤ p / 6 := by
  have hc : (C (1 / 2 : ZMod p) * (1 - X)).natDegree ≤ 1 := by compute_degree
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul (actualLegendreGauss_degree p) hc).trans (by simp))

theorem actualLegendreJacobi_endpoint_one (p : ℕ) [Fact p.Prime] :
    (actualLegendreJacobi p).eval 1 = 1 := by
  simp [actualLegendreJacobi, eval_comp, actualLegendreGauss_origin]

theorem actualLegendreJacobi_source_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi (p / 6) (actualLegendreJacobi p) = 0 := by
  rw [actualLegendreJacobi, ← legendre_coordinate (p / 6) (1 / 2 : ZMod p)
    (field_half_identity p hp), actualLegendreGauss_regular, zero_comp]

theorem evenLogPolynomial_second_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (evenLogPolynomial p).derivative.derivative -
      2 * X * (evenLogPolynomial p).derivative = 1 := by
  have h := congrArg Polynomial.derivative (evenLogPolynomial_source p hp)
  simp only [derivative_mul, derivative_sub, derivative_one, derivative_X_pow,
    derivative_X] at h
  norm_num [map_ofNat] at h
  linear_combination h

/-- The complete NC79 field polynomial, with its literal finite logarithm and endpoint. -/
noncomputable def rankHatField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  actualLegendreJacobi p * (evenLogPolynomial p +
    C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) - fieldHarmonic p (p / 6))) -
    X ^ p * properLegendreJacobi p

theorem rankHatField_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (rankHatField p) =
      2 * X * (actualLegendreJacobi p).derivative + actualLegendreJacobi p := by
  have hz : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by simp [derivative_X_pow]
  rw [rankHatField, legendreJacobi_sub, legendreJacobi_product,
    legendreJacobi_flat_product _ _ _ hz, actualLegendreJacobi_source_zero p (by omega),
    properLegendreJacobi_source p (by omega)]
  simp only [mul_zero, zero_add, derivative_add, derivative_C, add_zero]
  linear_combination actualLegendreJacobi p * evenLogPolynomial_second_source p hp +
    2 * (actualLegendreJacobi p).derivative * evenLogPolynomial_source p hp

theorem rankHatField_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankHatField p).eval 1 = 0 := by
  simp only [rankHatField, eval_sub, eval_mul, eval_add, eval_C, eval_pow, eval_X,
    one_pow, one_mul, actualLegendreJacobi_endpoint_one,
    evenLogPolynomial_endpoint_one p hp, properLegendreJacobi_endpoint_one]
  ring

theorem rankHatField_predegree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankHatField p).natDegree ≤ p + p / 6 - 1 := by
  have hc : (C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
      fieldHarmonic p (p / 6))).natDegree ≤ p - 1 := by rw [natDegree_C]; exact Nat.zero_le _
  have hH : (evenLogPolynomial p +
      C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) - fieldHarmonic p (p / 6))).natDegree ≤ p - 1 :=
    by simpa only [Nat.max_self] using Polynomial.natDegree_add_le_of_le (evenLogPolynomial_degree p) hc
  have hY := Polynomial.natDegree_mul_le (p := actualLegendreJacobi p)
    (q := evenLogPolynomial p +
      C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) - fieldHarmonic p (p / 6)))
  have hn := Polynomial.natDegree_mul_le (p := (X : (ZMod p)[X]) ^ p)
    (q := properLegendreJacobi p)
  have hxp : ((X : (ZMod p)[X]) ^ p).natDegree = p := by simp
  have hnp := properLegendreJacobi_degree p (by omega : 7 ≤ p)
  have hYb : (actualLegendreJacobi p * (evenLogPolynomial p +
      C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) - fieldHarmonic p (p / 6)))).natDegree ≤
      p + p / 6 - 1 := hY.trans (by have hy := actualLegendreJacobi_degree p; omega)
  have hnb : ((X : (ZMod p)[X]) ^ p * properLegendreJacobi p).natDegree ≤ p + p / 6 - 1 :=
    hn.trans (by rw [hxp]; omega)
  unfold rankHatField
  simpa only [Nat.max_self] using Polynomial.natDegree_sub_le_of_le hYb hnb

theorem theta_degree_le {K : Type*} [CommRing K] (P : K[X]) :
    (theta P).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [theta_coeff, coeff_eq_zero_of_natDegree_lt hn, mul_zero]

theorem rankHatField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankHatField p).natDegree ≤ p - 1 - p / 6 := by
  apply forced_legendre_degree_bound p (by omega) _ (rankHatField_predegree p hp)
  rw [rankHatField_source p hp]
  rw [show 2 * X * (actualLegendreJacobi p).derivative = 2 * theta (actualLegendreJacobi p) by
    simp only [theta, mul_assoc]]
  have htheta : (2 * theta (actualLegendreJacobi p)).natDegree ≤ p / 6 :=
    (Polynomial.natDegree_C_mul_le _ _).trans
      ((theta_degree_le _).trans (actualLegendreJacobi_degree p))
  simpa only [Nat.max_self] using
    Polynomial.natDegree_add_le_of_le htheta (actualLegendreJacobi_degree p)

/-- This identifies the actual Q-divided native polynomial; no source or value is assumed. -/
theorem actual_rankDividedField_eq_hat (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualRankDividedField p (by omega) = rankHatField p := by
  apply sub_eq_zero.mp
  apply legendre_jacobi_kernel_zero p (p / 6) (by omega)
  · exact (Polynomial.natDegree_sub_le_of_le
      (actualRankDividedField_degree p (by omega)) (rankHatField_degree p hp)).trans_lt (by omega)
  · simp only [eval_sub, actualRankDividedField_endpoint_one,
      rankHatField_endpoint_one p hp, sub_self]
  · rw [legendreJacobi_sub, actualRankDividedField_source p (by omega),
      rankHatField_source p hp, sub_self]

end WPActualRankTwoComparison
