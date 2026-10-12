import WPFiniteLogProduct

open scoped BigOperators
open Polynomial

namespace WPFiniteHomogeneousD

open WPFiniteAffineLog WPFiniteKSource WPFiniteDSource

variable {K : Type*} [Field K]

noncomputable def HP1 (p : ℕ) (b : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, C (b ^ (p - j) / (j : K)) * X ^ j

noncomputable def HP2 (p : ℕ) (b : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, C (b ^ (p - j) / (j : K) ^ 2) * X ^ j

theorem HP2_eval (p : ℕ) (a b : K) :
    (HP2 p b).eval a = WPFiniteDReciprocity.H2 p a b := by
  simp only [HP2, WPFiniteDReciprocity.H2, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv]
  ring

private theorem HP1_degree (p : ℕ) (b : K) : (HP1 p b).natDegree ≤ p - 1 := by
  unfold HP1
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans ((by simp : (X ^ j : K[X]).natDegree ≤ j).trans
    (by have h := (Finset.mem_Ico.mp hj).2; omega))

private theorem HP2_degree (p : ℕ) (b : K) : (HP2 p b).natDegree ≤ p - 1 := by
  unfold HP2
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans ((by simp : (X ^ j : K[X]).natDegree ≤ j).trans
    (by have h := (Finset.mem_Ico.mp hj).2; omega))

private theorem HP1_zero (p : ℕ) (b : K) : (HP1 p b).eval 0 = 0 := by
  unfold HP1
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by have h := (Finset.mem_Ico.mp hj).1; omega : j ≠ 0), mul_zero]

private theorem HP2_zero (p : ℕ) (b : K) : (HP2 p b).eval 0 = 0 := by
  unfold HP2
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by have h := (Finset.mem_Ico.mp hj).1; omega : j ≠ 0), mul_zero]

private theorem HP1_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) :
    (HP1 p b).derivative =
      C b * ∑ r ∈ Finset.range (p - 1), X ^ r * (C b) ^ (p - 2 - r) := by
  unfold HP1
  rw [derivative_sum]
  have he : (∑ j ∈ Finset.Ico 1 p,
      (C (b ^ (p - j) / (j : K)) * X ^ j).derivative) =
      ∑ j ∈ Finset.Ico 1 p, C (b ^ (p - j)) * X ^ (j - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [derivative_C_mul_X_pow, div_mul_cancel₀ _ (WPFiniteField.denominator_ne_zero p j hj)]
  rw [he, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show 1 + r - 1 = r by omega,
    show p - (1 + r) = (p - 2 - r) + 1 by omega, pow_succ]
  simp only [map_mul, map_pow]
  ring

theorem HP1_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) :
    X * (X - C b) * (HP1 p b).derivative = C b * X ^ p - C (b ^ p) * X := by
  have hp := (Fact.out : p.Prime).two_le
  rw [HP1_derivative]
  have hg := (Commute.all (X : K[X]) (C b)).mul_geom_sum₂ (p - 1)
  calc
    _ = C b * X * ((X - C b) *
        ∑ r ∈ Finset.range (p - 1), X ^ r * (C b) ^ (p - 2 - r)) := by ring
    _ = C b * X * (X ^ (p - 1) - (C b) ^ (p - 1)) := by
      simpa only [show p - 1 - 1 = p - 2 by omega] using congrArg (fun Q => C b * X * Q) hg
    _ = _ := by
      rw [show (X : K[X]) ^ p = X ^ (p - 1) * X by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)],
        show b ^ p = b ^ (p - 1) * b by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)], map_mul, map_pow]
      ring

theorem HP1_comp_source (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) (U : K[X]) :
    U * (U - C b) * ((HP1 p b).comp U).derivative =
      (C b * U ^ p - C (b ^ p) * U) * U.derivative := by
  have he := congrArg (fun Q : K[X] => Q.comp U) (HP1_cleared_derivative p b)
  simp only [mul_comp, sub_comp, X_comp, C_comp, pow_comp] at he
  rw [derivative_comp]
  linear_combination U.derivative * he

private theorem LP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] :
    X * (X - 1) * (LP p : K[X]).derivative = X ^ p - X := by
  have hp := (Fact.out : p.Prime).two_le
  have hpow : (1 - X : K[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char (p := p), one_pow]
  have hpow' : (1 - X : K[X]) ^ p = (1 - X) ^ (p - 1) * (1 - X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hxpow : (X : K[X]) ^ p = X ^ (p - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [LP_derivative_closed_eq]
  linear_combination -X * hpow + X * hpow' + (X - 1) * hxpow

private theorem zero_of_derivative_small (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (a : K) (hdeg : Q.natDegree < p) (hd : Q.derivative = 0)
    (hz : Q.eval a = 0) : Q = 0 := by
  have hc : Q = C (Q.coeff 0) := by
    ext n
    by_cases hn : n = 0
    · subst n; simp
    rw [coeff_C, if_neg hn]
    by_cases hnp : p ≤ n
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
    have he : Q.coeff n * (n : K) = 0 := by
      have he := congrArg (fun P : K[X] => P.coeff (n - 1)) hd
      simpa only [coeff_derivative, ← Nat.cast_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using he
    exact (mul_eq_zero.mp he).resolve_right
      (WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr (by omega)))
  rw [hc, eval_C] at hz
  rw [hc, hz, C_0]

private theorem comp_small (p : ℕ) (P U : K[X])
    (hP : P.natDegree ≤ p - 1) (hU : U.natDegree ≤ 1) :
    (P.comp U).natDegree ≤ p - 1 := by
  exact (natDegree_comp_le).trans ((Nat.mul_le_mul hP hU).trans (by simp))

theorem homogeneous_log_translation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (y : K) :
    (HP1 p (1 - y)).comp (X - C y) + (HP1 p y).comp (C y - X) =
      (LP p : K[X]) - C (WPFiniteField.ell p y) := by
  let U : K[X] := X - C y
  let A : K[X] := (HP1 p (1 - y)).comp U
  let B : K[X] := (HP1 p y).comp (-U)
  have ha := HP1_comp_source p (1 - y) U
  have hb := HP1_comp_source p y (-U)
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hUp : U ^ p = (X : K[X]) ^ p - C (y ^ p) := by
    dsimp only [U]; rw [sub_pow_char (p := p), map_pow]
  have hbp : (1 - y) ^ p = 1 - y ^ p := by rw [sub_pow_char (p := p), one_pow]
  have hUd : U.derivative = 1 := by simp [U]
  rw [hUd, mul_one, hbp] at ha
  rw [derivative_neg, hUd, hodd.neg_pow] at hb
  have hl := LP_cleared_source (K := K) p
  have hf : (X * (X - 1) * U : K[X]) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero X_ne_zero (by simpa using (X_sub_C_ne_zero (1 : K))))
      (by simpa [U] using (X_sub_C_ne_zero y))
  have hder : (A + B - LP p : K[X]).derivative = 0 := by
    have hmul : (X * (X - 1) * U : K[X]) * (A + B - LP p).derivative = 0 := by
      dsimp only [A, B]
      rw [derivative_sub, derivative_add]
      simp only [map_sub, map_one] at ha
      dsimp only [U] at ha hb hUp ⊢
      linear_combination X * ha + (X - 1) * hb - (X - C y) * hl +
        (X - C y) * hUp
    exact (mul_eq_zero.mp hmul).resolve_left hf
  have hUdeg : U.natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hAdeg : A.natDegree ≤ p - 1 := comp_small p _ _ (HP1_degree p (1 - y)) hUdeg
  have hBdeg : B.natDegree ≤ p - 1 := comp_small p _ _ (HP1_degree p y) (by simpa using hUdeg)
  let Q : K[X] := A + B - LP p + C (WPFiniteField.ell p y)
  have hdeg : Q.natDegree < p := by
    have he : Q.natDegree ≤ p - 1 :=
      (natDegree_add_le _ _).trans (max_le
        ((natDegree_sub_le _ _).trans (max_le
          ((natDegree_add_le _ _).trans (max_le hAdeg hBdeg)) (LP_natDegree_le p))) (by simp))
    omega
  have hd : Q.derivative = 0 := by dsimp only [Q]; rw [derivative_add, hder, derivative_C, add_zero]
  have hz : Q.eval y = 0 := by
    simp only [Q, A, B, U, eval_add, eval_sub, eval_comp, eval_neg, eval_X,
      eval_C, sub_self, neg_zero, HP1_zero, LP_eval_eq,
      zero_add, zero_sub, neg_add_cancel]
  have hzero := zero_of_derivative_small p Q y hdeg hd hz
  have he : A + B = (LP p : K[X]) - C (WPFiniteField.ell p y) := by
    dsimp only [Q] at hzero
    linear_combination hzero
  simpa only [A, B, U, neg_sub] using he

theorem HP2_X_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) :
    X * (HP2 p b).derivative = HP1 p b := by
  unfold HP2 HP1
  rw [derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd := WPFiniteField.denominator_ne_zero (K := K) p j hj
  have hc : (b ^ (p - j) / (j : K) ^ 2) * j = b ^ (p - j) / (j : K) := by
    field_simp [hjd]
  rw [derivative_C_mul_X_pow, hc]
  rw [show (X : K[X]) ^ j = X ^ (j - 1) * X by
    rw [← pow_succ, Nat.sub_add_cancel (Finset.mem_Ico.mp hj).1]]
  ring

theorem HP2_comp_source (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) (U : K[X]) :
    U * ((HP2 p b).comp U).derivative = (HP1 p b).comp U * U.derivative := by
  have he := congrArg (fun Q : K[X] => Q.comp U) (HP2_X_derivative p b)
  simp only [mul_comp, X_comp] at he
  rw [derivative_comp]
  linear_combination U.derivative * he

private theorem HP2_diagonal (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (y : K) :
    (HP2 p y).eval y = 0 := by
  have hr : WPFiniteField.R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
  have he : (HP2 p y).eval y = y ^ p * WPFiniteField.R p (1 : K) := by
    unfold HP2 WPFiniteField.R
    rw [eval_finsetSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, div_eq_mul_inv]
    have hpow : y ^ (p - j) * y ^ j = y ^ p := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.mem_Ico.mp hj).2.le]
    linear_combination ((j : K) ^ 2)⁻¹ * hpow
  rw [he, hr, mul_zero]

theorem full_D_three_H2 (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (x y : K) :
    WPFiniteLoop.D (p - 1) x y = WPFiniteDReciprocity.H2 p (x - y) (1 - y) -
      WPFiniteDReciprocity.H2 p (-y) (1 - y) + WPFiniteDReciprocity.H2 p (y - x) y := by
  let U : K[X] := X - C y
  let V : K[X] := (HP2 p (1 - y)).comp U - C ((HP2 p (1 - y)).eval (-y)) +
    (HP2 p y).comp (-U)
  have ha := HP2_comp_source p (1 - y) U
  have hb := HP2_comp_source p y (-U)
  have ht := homogeneous_log_translation (K := K) p hp y
  have hd := DP_cleared_derivative p y
  have hUd : U.derivative = 1 := by simp [U]
  rw [hUd, mul_one] at ha
  rw [derivative_neg, hUd, mul_neg, mul_one] at hb
  have hV : U * V.derivative = (LP p : K[X]) - C (WPFiniteField.ell p y) := by
    dsimp only [V]
    rw [derivative_add, derivative_sub, derivative_C, sub_zero]
    have ht' : (HP1 p (1 - y)).comp U + (HP1 p y).comp (-U) =
        (LP p : K[X]) - C (WPFiniteField.ell p y) := by simpa only [U, neg_sub] using ht
    linear_combination ha - hb + ht'
  have hder : ((DP p y) - V).derivative = 0 := by
    apply (mul_eq_zero.mp (show U * ((DP p y) - V).derivative = 0 from ?_)).resolve_left
      (by simpa [U] using (X_sub_C_ne_zero y))
    rw [derivative_sub]
    linear_combination hd - hV
  have hUdeg : U.natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hVdeg : V.natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le
        (comp_small p _ _ (HP2_degree p (1 - y)) hUdeg) (by simp)))
      (comp_small p _ _ (HP2_degree p y) (by simpa using hUdeg)))
  have hdeg : ((DP p y) - V).natDegree < p := by
    have he := (natDegree_sub_le _ _).trans (max_le (DP_natDegree_le p y) hVdeg)
    omega
  have hz : ((DP p y) - V).eval 0 = 0 := by
    simp only [V, U, eval_sub, DP_eval_zero, eval_add, eval_comp, eval_C, eval_neg,
      eval_X, zero_sub, neg_neg, HP2_diagonal p hp, sub_self, add_zero]
  have he := congrArg (fun Q : K[X] => Q.eval x)
    (sub_eq_zero.mp (zero_of_derivative_small p _ 0 hdeg hder hz))
  simpa only [DP_eval, V, U, eval_add, eval_sub, eval_comp, eval_C, eval_X,
    eval_neg, neg_sub, HP2_eval] using he

theorem H2_scaled_R (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) (hb : b ≠ 0) :
    WPFiniteDReciprocity.H2 p a b = b ^ p * WPFiniteField.R p (a / b) := by
  unfold WPFiniteDReciprocity.H2 WPFiniteField.R
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_sub₀ b hb (Finset.mem_Ico.mp hj).2.le, div_pow]
  simp only [div_eq_mul_inv]
  ring

end WPFiniteHomogeneousD
