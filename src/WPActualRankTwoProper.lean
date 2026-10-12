import WPActualRankTwoLowTaylor
import WPActualGaussProper

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualCMGauss WPActualGaussBottom WPActualGaussProper
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoLowTaylor

namespace WPActualRankTwoProper

set_option maxHeartbeats 800000

theorem actualLegendreGauss_degree (p : ℕ) : (actualLegendreGauss p).natDegree ≤ p / 6 := by
  unfold actualLegendreGauss
  exact Polynomial.natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])

theorem actualLegendreGauss_origin (p : ℕ) : (actualLegendreGauss p).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero]
  simp [actualLegendreGauss, coeff_map, coeff_shiftedLegendre]

/-- The literal bottom-parameter derivative at the actual degree d=p/6. -/
noncomputable def degreeBottom (p : ℕ) : (ZMod p)[X] :=
  rankCoefficientPolynomial (p / 6)
    (fun n => -fieldHarmonic p n * (actualLegendreGauss p).coeff n)

theorem degreeBottom_coeff (p n : ℕ) :
    (degreeBottom p).coeff n = -fieldHarmonic p n * (actualLegendreGauss p).coeff n := by
  rw [degreeBottom, rankCoefficientPolynomial_coeff]
  split_ifs with hn
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt ((actualLegendreGauss_degree p).trans_lt (by omega))]
    ring

theorem degreeBottom_origin (p : ℕ) : (degreeBottom p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, degreeBottom_coeff, fieldHarmonic_zero]
  ring

theorem degreeBottom_degree (p : ℕ) : (degreeBottom p).natDegree ≤ p / 6 :=
  rankCoefficientPolynomial_degree _ _

theorem degreeBottom_recurrence (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((n : ZMod p) + 1) ^ 2 * (degreeBottom p).coeff (n + 1) -
      ((n : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
        ((n : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1) * (degreeBottom p).coeff n =
      -((n : ZMod p) + 1) * (actualLegendreGauss p).coeff (n + 1) := by
  rw [degreeBottom_coeff, degreeBottom_coeff]
  have he := actualLegendreGauss_recurrence p n
  by_cases hn : n < p / 6
  · have hu : ((n : ZMod p) + 1) ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        small_cast_ne_zero p (n + 1) (by omega) (by omega)
    have hi := mul_inv_cancel₀ hu
    rw [fieldHarmonic_succ]
    simp only [Nat.cast_add, Nat.cast_one] at *
    linear_combination -fieldHarmonic p n * he -
      (((n : ZMod p) + 1) * (actualLegendreGauss p).coeff (n + 1)) * hi
  · have hy : (actualLegendreGauss p).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((actualLegendreGauss_degree p).trans_lt (by omega))
    rw [hy] at he ⊢
    linear_combination -fieldHarmonic p n * he

theorem degreeBottom_euler_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreEuler (p / 6) (degreeBottom p) = -theta (actualLegendreGauss p) := by
  ext n
  cases n with
  | zero => simp [legendreEuler_coeff_zero, theta_coeff]
  | succ n =>
    rw [legendreEuler_coeff_succ, coeff_neg, theta_coeff]
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using degreeBottom_recurrence p n hp

theorem degreeBottom_regular_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreRegular (p / 6) (degreeBottom p) = -(actualLegendreGauss p).derivative := by
  have he := degreeBottom_euler_source p hp
  rw [legendreEuler_eq_X_regular, theta] at he
  have hz : X * (legendreRegular (p / 6) (degreeBottom p) +
      (actualLegendreGauss p).derivative) = 0 := by linear_combination he
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left X_ne_zero)

noncomputable def degreeProperGauss (p : ℕ) : (ZMod p)[X] :=
  degreeBottom p + C (fieldHarmonic p (p / 6)) * actualLegendreGauss p

theorem degreeProperGauss_coeff (p n : ℕ) : (degreeProperGauss p).coeff n =
    (fieldHarmonic p (p / 6) - fieldHarmonic p n) * (actualLegendreGauss p).coeff n := by
  simp only [degreeProperGauss, coeff_add, coeff_C_mul, degreeBottom_coeff]
  ring

theorem degreeProperGauss_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (degreeProperGauss p).natDegree ≤ p / 6 - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [degreeProperGauss_coeff]
  by_cases he : n = p / 6
  · rw [he, sub_self, zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt ((actualLegendreGauss_degree p).trans_lt (by omega)), mul_zero]

theorem degreeProperGauss_origin (p : ℕ) :
    (degreeProperGauss p).eval 0 = fieldHarmonic p (p / 6) := by
  simp [degreeProperGauss, degreeBottom_origin, actualLegendreGauss_origin]

theorem actualLegendreGauss_regular (p : ℕ) : legendreRegular (p / 6) (actualLegendreGauss p) = 0 := by
  rw [actualLegendreGauss, ← legendreRegular_map, actual_integer_legendre_ODE, Polynomial.map_zero]

theorem degreeProperGauss_regular_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreRegular (p / 6) (degreeProperGauss p) = -(actualLegendreGauss p).derivative := by
  rw [degreeProperGauss, legendreRegular_add_C_mul, degreeBottom_regular_source p hp,
    actualLegendreGauss_regular, mul_zero, add_zero]

theorem degreeProperGauss_wronskian (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * X * (1 - X) * (actualLegendreGauss p * (degreeProperGauss p).derivative -
      (actualLegendreGauss p).derivative * degreeProperGauss p) = 1 - actualLegendreGauss p ^ 2 := by
  have hd := wronskianPolynomial_degree (actualLegendreGauss p) (degreeProperGauss p) (p / 6)
    (actualLegendreGauss_degree p) (degreeProperGauss_degree p hp)
  have hz : wronskianPolynomial (actualLegendreGauss p) (degreeProperGauss p) = 0 := by
    apply finite_derivative_zero p _ (hd.trans_lt (by omega))
    · simp [wronskianPolynomial, actualLegendreGauss_origin]
    · rw [wronskianPolynomial_source (p / 6), degreeProperGauss_regular_source p hp,
        actualLegendreGauss_regular]
      ring
  unfold wronskianPolynomial at hz
  linear_combination hz

theorem legendreJacobi_neg {K : Type*} [CommRing K] (d : ℕ) (P : K[X]) :
    legendreJacobi d (-P) = -legendreJacobi d P := by
  simp only [legendreJacobi, Polynomial.derivative_neg]
  ring

/-- Exact affine coordinate transport, with the sole scalar identity made explicit. -/
theorem legendre_coordinate {K : Type*} [CommRing K] (d : ℕ) (a : K)
    (ha : 2 * a = 1) (P : K[X]) :
    (legendreRegular d P).comp (C a * (1 - X)) =
      legendreJacobi d (P.comp (C a * (1 - X))) := by
  have haP : 2 * C a = (1 : K[X]) := by
    have h := congrArg (C : K → K[X]) ha
    simpa only [map_mul, map_ofNat, map_one] using h
  simp [legendreRegular, legendreJacobi, derivative_comp]
  linear_combination -(C a * (1 - X) *
      P.derivative.derivative.comp (C a * (1 - X)) +
      P.derivative.comp (C a * (1 - X))) * haP

noncomputable def properLegendreJacobi (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  -(degreeProperGauss p).comp (C (1 / 2 : ZMod p) * (1 - X))

theorem properLegendreJacobi_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (properLegendreJacobi p).natDegree < p / 6 := by
  have hc : (C (1 / 2 : ZMod p) * (1 - X)).natDegree ≤ 1 := by compute_degree
  have hd := Polynomial.natDegree_comp_le (p := degreeProperGauss p)
    (q := C (1 / 2 : ZMod p) * (1 - X))
  rw [properLegendreJacobi, Polynomial.natDegree_neg]
  exact hd.trans_lt ((Nat.mul_le_mul (degreeProperGauss_degree p hp) hc).trans_lt (by omega))

theorem properLegendreJacobi_endpoint_one (p : ℕ) [Fact p.Prime] :
    (properLegendreJacobi p).eval 1 = -fieldHarmonic p (p / 6) := by
  simp [properLegendreJacobi, Polynomial.eval_comp, degreeProperGauss_origin]

theorem field_half_identity (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (2 : ZMod p) * (1 / 2) = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using small_cast_ne_zero p 2 (by norm_num) (by omega)
  simpa only [one_div] using mul_inv_cancel₀ h2

theorem properLegendreJacobi_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi (p / 6) (properLegendreJacobi p) = -2 * (actualLegendreJacobi p).derivative := by
  have hc := legendre_coordinate (p / 6) (1 / 2 : ZMod p) (field_half_identity p hp)
    (degreeProperGauss p)
  have hL : legendreJacobi (p / 6) (properLegendreJacobi p) =
      (actualLegendreGauss p).derivative.comp (C (1 / 2 : ZMod p) * (1 - X)) := by
    rw [properLegendreJacobi, legendreJacobi_neg, ← hc, degreeProperGauss_regular_source p hp]
    simp
  have haP : (2 : (ZMod p)[X]) * C (1 / 2 : ZMod p) = 1 := by
    have h := congrArg (C : ZMod p → (ZMod p)[X]) (field_half_identity p hp)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hD : (actualLegendreJacobi p).derivative =
      -C (1 / 2 : ZMod p) * (actualLegendreGauss p).derivative.comp
        (C (1 / 2 : ZMod p) * (1 - X)) := by
    simp [actualLegendreJacobi, derivative_comp]
  rw [hL, hD]
  linear_combination -(actualLegendreGauss p).derivative.comp
    (C (1 / 2 : ZMod p) * (1 - X)) * haP

theorem properLegendreJacobi_wronskian (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (1 - X ^ 2) * (actualLegendreJacobi p * (properLegendreJacobi p).derivative -
      (actualLegendreJacobi p).derivative * properLegendreJacobi p) =
      1 - actualLegendreJacobi p ^ 2 := by
  let q : (ZMod p)[X] := C (1 / 2 : ZMod p) * (1 - X)
  have haP : (2 : (ZMod p)[X]) * C (1 / 2 : ZMod p) = 1 := by
    have h := congrArg (C : ZMod p → (ZMod p)[X]) (field_half_identity p hp)
    simpa only [map_mul, map_ofNat, map_one] using h
  have hn : (properLegendreJacobi p).derivative =
      C (1 / 2 : ZMod p) * (degreeProperGauss p).derivative.comp q := by
    simp [properLegendreJacobi, q, derivative_comp]
  have hY : (actualLegendreJacobi p).derivative =
      -C (1 / 2 : ZMod p) * (actualLegendreGauss p).derivative.comp q := by
    simp [actualLegendreJacobi, q, derivative_comp]
  have hw := congrArg (fun P : (ZMod p)[X] => P.comp q) (degreeProperGauss_wronskian p hp)
  rw [show (2 : (ZMod p)[X]) = C (2 : ZMod p) by rfl] at hw
  simp only [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.pow_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.one_comp] at hw
  simp only [map_ofNat] at hw
  rw [hn, hY, properLegendreJacobi, actualLegendreJacobi]
  change (1 - X ^ 2) *
      ((actualLegendreGauss p).comp q *
        (C (1 / 2 : ZMod p) * (degreeProperGauss p).derivative.comp q) -
      (-C (1 / 2 : ZMod p) * (actualLegendreGauss p).derivative.comp q) *
        (-(degreeProperGauss p).comp q)) = 1 - ((actualLegendreGauss p).comp q) ^ 2
  dsimp only [q] at hw ⊢
  linear_combination hw + C (1 / 2 : ZMod p) * (1 - X) ^ 2 *
    ((actualLegendreGauss p).comp (C (1 / 2 : ZMod p) * (1 - X)) *
      (degreeProperGauss p).derivative.comp (C (1 / 2 : ZMod p) * (1 - X)) -
      (actualLegendreGauss p).derivative.comp (C (1 / 2 : ZMod p) * (1 - X)) *
        (degreeProperGauss p).comp (C (1 / 2 : ZMod p) * (1 - X))) * haP

end WPActualRankTwoProper
