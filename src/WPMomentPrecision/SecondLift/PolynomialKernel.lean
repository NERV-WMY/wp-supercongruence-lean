import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped Polynomial
open Polynomial

namespace WPMomentPrecision.SecondPolynomialKernel

/-- The proper Wronskian supplies the explicit polynomial division witness. -/
theorem proper_wronskian_kernel_division {K : Type*} [Field K]
    (q Y n P : K[X]) (hY : Y ≠ 0)
    (hW : q * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hP : Y * P.derivative - Y.derivative * P = 0) :
    ∃ H : K[X], P = Y * H ∧ H.derivative = 0 := by
  let H := (Y + q * n.derivative) * P - q * n * P.derivative
  have hH : P = Y * H := by
    dsimp only [H]
    linear_combination -P * hW + q * n * hP
  refine ⟨H, hH, ?_⟩
  have hz : Y ^ 2 * H.derivative = 0 := by
    rw [hH] at hP
    simp only [derivative_mul] at hP
    linear_combination hP
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hY)

/-- Only the constant and p-th coefficient survive this full derivative kernel. -/
theorem derivative_kernel_shape (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[X]) (hdeg : P.natDegree < 2 * p) (hD : P.derivative = 0) :
    P = C (P.coeff 0) + C (P.coeff p) * X ^ p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [hp.ne]
  by_cases hnp : n = p
  · subst n
    simp only [coeff_add, coeff_C, if_neg hp.ne', coeff_C_mul,
      coeff_X_pow_self, mul_one, zero_add]
  have hz : P.coeff n = 0 := by
    by_cases hnlarge : 2 * p ≤ n
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnlarge)
    have hnd : ¬p ∣ n := by
      rintro ⟨k, hk⟩
      have hklt : k < 2 := by
        apply (Nat.mul_lt_mul_left hp).mp
        rw [← hk]
        omega
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp_all
    have hc : (n : ZMod p) ≠ 0 := by
      intro he
      exact hnd ((ZMod.natCast_eq_zero_iff n p).mp he)
    have he := congrArg (fun Q : (ZMod p)[X] => Q.coeff (n - 1)) hD
    have hnpos : 1 ≤ n := by omega
    have hmul : P.coeff n * (n : ZMod p) = 0 := by
      simpa only [coeff_derivative, ← Nat.cast_add_one,
        Nat.sub_add_cancel hnpos, coeff_zero] using he
    exact (mul_eq_zero.mp hmul).resolve_right hc
  simp only [coeff_add, coeff_C, if_neg hn0, coeff_C_mul, coeff_X_pow,
    if_neg hnp, mul_zero, zero_add, hz]

/-- Oddness and the actual endpoint kill both possible Frobenius coefficients. -/
theorem odd_derivative_kernel_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (P : (ZMod p)[X]) (hdeg : P.natDegree < 2 * p) (hD : P.derivative = 0)
    (hodd : P.comp (-X) = -P) (h1 : P.eval 1 = 0) : P = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
    omega
  have h0 : P.eval 0 = 0 := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) hodd
    simp only [eval_comp, eval_neg, eval_X, neg_zero] at he
    have hm : (2 : ZMod p) * P.eval 0 = 0 := by linear_combination he
    exact (mul_eq_zero.mp hm).resolve_left h2
  have hs := derivative_kernel_shape p P hdeg hD
  have hc0 : P.coeff 0 = 0 := by rwa [coeff_zero_eq_eval_zero]
  have hcp : P.coeff p = 0 := by
    have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hs
    simpa [h1, hc0] using he.symm
  rw [hs, hc0, hcp]
  simp

/-- The leading coefficient of the cleared logarithmic first-order operator. -/
theorem logarithmic_operator_top_coeff {K : Type*} [Field K]
    (Y L : K[X]) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hY : Y.natDegree = d) (hL : L.natDegree = m) :
    ((1 - X ^ 2) * (Y * L.derivative - 2 * Y.derivative * L)).coeff (d + m + 1) =
      -(Y.coeff d * L.coeff m * ((m : K) - 2 * (d : K))) := by
  let W := Y * L.derivative - 2 * Y.derivative * L
  have hYD : Y.derivative.natDegree ≤ d - 1 := by
    simpa [hY] using natDegree_derivative_le Y
  have hLD : L.derivative.natDegree ≤ m - 1 := by
    simpa [hL] using natDegree_derivative_le L
  have hYA := natDegree_mul_le_of_le (le_of_eq hY) hLD
  have hYL := natDegree_mul_le_of_le hYD (le_of_eq hL)
  have hWdeg : W.natDegree ≤ d + m - 1 := by
    have hB : (2 * Y.derivative * L).natDegree ≤ d - 1 + m := by
      exact (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (show (2 : K[X]).natDegree ≤ 0 by simp) hYD)
        (le_of_eq hL)).trans (by omega)
    exact (natDegree_sub_le_of_le hYA hB).trans (by omega)
  have hAC : (Y * L.derivative).coeff (d + m - 1) =
      Y.coeff d * L.coeff m * (m : K) := by
    rw [show d + m - 1 = d + (m - 1) by omega,
      coeff_mul_add_eq_of_natDegree_le (le_of_eq hY) hLD, coeff_derivative,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    ring
  have hBC : (Y.derivative * L).coeff (d + m - 1) =
      Y.coeff d * (d : K) * L.coeff m := by
    rw [show d + m - 1 = (d - 1) + m by omega,
      coeff_mul_add_eq_of_natDegree_le hYD (le_of_eq hL), coeff_derivative,
      Nat.sub_add_cancel (by omega : 1 ≤ d)]
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    ring
  have hWC : W.coeff (d + m - 1) =
      Y.coeff d * L.coeff m * ((m : K) - 2 * (d : K)) := by
    dsimp only [W]
    rw [coeff_sub, mul_assoc, coeff_ofNat_mul, hAC, hBC]
    ring
  have hWzero : W.coeff (d + m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hWdeg.trans_lt (by omega))
  change ((1 - X ^ 2) * W).coeff (d + m + 1) = _
  rw [sub_mul, one_mul, coeff_sub, coeff_X_pow_mul',
    if_pos (by omega : 2 ≤ d + m + 1), hWzero,
    show d + m + 1 - 2 = d + m - 1 by omega, hWC]
  ring

/-- An even logarithmic numerator cannot retain any native coefficient above 2d. -/
theorem logarithmic_operator_degree_bound (p d : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (Y L S : (ZMod p)[X]) (hd : 0 < d) (hY : Y ≠ 0) (hYdeg : Y.natDegree = d)
    (hLdeg : L.natDegree < 2 * p) (hLeven : Even L.natDegree)
    (hSdeg : S.natDegree ≤ 3 * d - 1)
    (hsource : (1 - X ^ 2) * (Y * L.derivative - 2 * Y.derivative * L) = S) :
    L.natDegree ≤ 2 * d := by
  by_contra hm
  have hm' : 2 * d < L.natDegree := by omega
  have hL : L ≠ 0 := by
    intro hz
    simp only [hz, natDegree_zero] at hm'
    omega
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff (d + L.natDegree + 1)) hsource
  rw [logarithmic_operator_top_coeff Y L d L.natDegree hd (by omega) hYdeg rfl,
    coeff_eq_zero_of_natDegree_lt (hSdeg.trans_lt (by omega)), neg_eq_zero] at hc
  have hyc : Y.coeff d ≠ 0 := by
    rw [← hYdeg]
    exact leadingCoeff_ne_zero.mpr hY
  have hlc : L.coeff L.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hL
  have he : (L.natDegree : ZMod p) - 2 * (d : ZMod p) = 0 :=
    (mul_eq_zero.mp hc).resolve_left (mul_ne_zero hyc hlc)
  have hcast : ((L.natDegree - 2 * d : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (by omega : 2 * d ≤ L.natDegree), Nat.cast_mul, Nat.cast_ofNat]
    exact he
  have hdiv := (ZMod.natCast_eq_zero_iff (L.natDegree - 2 * d) p).mp hcast
  obtain ⟨k, hk⟩ := hdiv
  have hp0 := (Fact.out : p.Prime).pos
  have hklt : k < 2 := by
    apply (Nat.mul_lt_mul_left hp0).mp
    rw [← hk]
    omega
  have hkpos : 0 < k := by
    by_contra hz
    have hk0 : k = 0 := by omega
    simp only [hk0, mul_zero] at hk
    omega
  have hk1 : k = 1 := by omega
  rw [hk1, mul_one] at hk
  obtain ⟨a, ha⟩ := hLeven
  obtain ⟨b, hb⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

end WPMomentPrecision.SecondPolynomialKernel
