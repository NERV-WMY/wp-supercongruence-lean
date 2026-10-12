import WPFiniteJNormalization

open scoped BigOperators
open Polynomial

namespace WPFiniteCubicLog

open WPFiniteAffineLog WPFiniteKSource

variable {K : Type*} [Field K]

theorem derivative_support_three (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree < 3 * p) (hd : Q.derivative = 0) :
    Q = C (Q.coeff 0) + C (Q.coeff p) * X ^ p + C (Q.coeff (2 * p)) * X ^ (2 * p) := by
  have hp := (Fact.out : p.Prime).pos
  have hother : ∀ n, n ≠ 0 → n ≠ p → n ≠ 2 * p → Q.coeff n = 0 := by
    intro n hn hnp hn2p
    by_cases hhigh : 3 * p ≤ n
    · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hhigh)
    have hnot : ¬p ∣ n := by
      rintro ⟨k, hk⟩
      have hk3 : k < 3 := by
        by_contra h
        have hmul := Nat.mul_le_mul_left p (not_lt.mp h)
        omega
      interval_cases k <;> omega
    have hunit : (n : K) ≠ 0 := by
      intro h; exact hnot ((CharP.cast_eq_zero_iff K p n).mp h)
    have he : Q.coeff n * (n : K) = 0 := by
      have he := congrArg (fun P : K[X] => P.coeff (n - 1)) hd
      simpa only [coeff_derivative, ← Nat.cast_add_one,
        Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using he
    exact (mul_eq_zero.mp he).resolve_right hunit
  ext n
  rw [coeff_add, coeff_add, coeff_C, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  by_cases hn : n = 0
  · subst n
    simp only [ite_true, if_neg (show 0 ≠ p by omega), if_neg (show 0 ≠ 2 * p by omega), add_zero]
  by_cases hnp : n = p
  · subst n
    simp only [ite_true, if_neg (show p ≠ 0 by omega), if_neg (show p ≠ 2 * p by omega), zero_add, add_zero]
  by_cases hn2p : n = 2 * p
  · subst n
    simp only [ite_true, if_neg (show 2 * p ≠ 0 by omega), if_neg (show 2 * p ≠ p by omega), zero_add]
  simp only [if_neg hn, if_neg hnp, if_neg hn2p, add_zero]
  exact hother n hn hnp hn2p

private theorem coeff_comp_neg (Q : K[X]) (n : ℕ) :
    (Q.comp (-X)).coeff n = Q.coeff n * (-1 : K) ^ n := by
  refine Polynomial.induction_on Q (fun a => ?_) (fun f g hf hg => ?_) (fun d a _ => ?_)
  · simp only [C_comp, coeff_C]
    by_cases hn : n = 0 <;> simp [hn]
  · rw [add_comp, coeff_add, coeff_add, hf, hg]; ring
  · have hpow : (-X : K[X]) ^ (d + 1) = C ((-1 : K) ^ (d + 1)) * X ^ (d + 1) := by
      calc
        _ = (C (-1 : K) * X) ^ (d + 1) := by simp
        _ = _ := by rw [mul_pow, ← C_pow]
    rw [mul_comp, C_comp, pow_comp, X_comp, hpow, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases hn : d + 1 = n
    · subst n; simp
    · simp only [if_neg (Ne.symm hn), zero_mul]

theorem even_kernel_three_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (Q : K[X]) (hdeg : Q.natDegree < 3 * p) (hd : Q.derivative = 0)
    (hev : Q.comp (-X) = Q) (h0 : Q.eval 0 = 0) (h1 : Q.eval 1 = 0) : Q = 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have he := congrArg (fun P : K[X] => P.coeff p) hev
  rw [coeff_comp_neg, hodd.neg_pow, one_pow] at he
  have hcP : Q.coeff p = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * Q.coeff p = 0 by linear_combination -he)).resolve_left h2
  have hc0 : Q.coeff 0 = 0 := by simpa only [coeff_zero_eq_eval_zero, eval_zero] using h0
  have hs := derivative_support_three p Q hdeg hd
  simp only [hc0, hcP, C_0, zero_mul, zero_add] at hs
  have he1 := congrArg (fun P : K[X] => P.eval 1) hs
  rw [h1, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] at he1
  rw [hs, ← he1, C_0, zero_mul]

theorem odd_kernel_three (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (Q : K[X]) (hdeg : Q.natDegree < 3 * p) (hd : Q.derivative = 0)
    (hod : Q.comp (-X) = -Q) : Q = C (Q.eval 1) * X ^ p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he0 := congrArg (fun P : K[X] => P.coeff 0) hod
  simp only [coeff_comp_neg, pow_zero, mul_one, coeff_neg] at he0
  have hc0 : Q.coeff 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * Q.coeff 0 = 0 by linear_combination he0)).resolve_left h2
  have he2 := congrArg (fun P : K[X] => P.coeff (2 * p)) hod
  rw [coeff_comp_neg, show (-1 : K) ^ (2 * p) = 1 by rw [pow_mul]; simp, mul_one, coeff_neg] at he2
  have hc2 : Q.coeff (2 * p) = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * Q.coeff (2 * p) = 0 by linear_combination he2)).resolve_left h2
  have hs := derivative_support_three p Q hdeg hd
  rw [hc0, hc2, C_0, zero_mul, zero_add, add_zero] at hs
  have he1 := congrArg (fun P : K[X] => P.eval 1) hs
  simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] at he1
  rw [he1]
  exact hs

theorem OP_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (OP p).derivative = 1 - X ^ (p - 1) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hunit : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have hpred : Even (p - 1) := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n, by omega⟩
  have hd : (OP p : K[X]).derivative = C (2 : K)⁻¹ *
      ((1 - X) ^ (p - 1) + (1 + X) ^ (p - 1) - 2 * X ^ (p - 1)) := by
    unfold OP
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub,
      derivative_comp, derivative_neg, derivative_X, LP_derivative_closed_eq]
    simp only [sub_comp, pow_comp, one_comp, X_comp, sub_neg_eq_add]
    rw [hpred.neg_pow]
    ring
  have hm : (1 - X : K[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char (p := p), one_pow]
  have hp1 : (1 + X : K[X]) ^ p = 1 + X ^ p := by rw [add_pow_char (p := p), one_pow]
  have hmp : (1 - X : K[X]) ^ p = (1 - X) ^ (p - 1) * (1 - X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hpp : (1 + X : K[X]) ^ p = (1 + X) ^ (p - 1) * (1 + X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hxp : X ^ (p - 1) * X = (X : K[X]) ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [hd]
  linear_combination -C (2 : K)⁻¹ * (1 + X) * hmp -
    C (2 : K)⁻¹ * (1 - X) * hpp + C (2 : K)⁻¹ * (1 + X) * hm +
    C (2 : K)⁻¹ * (1 - X) * hp1 + 2 * C (2 : K)⁻¹ * X * hxp +
    (1 - X ^ (p - 1)) * hunit

theorem LPsrc_comp_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (U : K[X]) :
    (1 - U ^ 2) * ((LPsrc p).comp U).derivative = (U - U ^ p) * U.derivative := by
  have he := congrArg (fun P : K[X] => P.comp U) (LPsrc_cleared_derivative p hp)
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp] at he
  rw [derivative_comp]
  linear_combination U.derivative * he

noncomputable def Tc : K[X] := 4 * X ^ 3 - 3 * X

noncomputable def UW1rhs (p : ℕ) : K[X] :=
  C (WPFiniteNC122.q p) * (1 - 4 * (X ^ p) ^ 2) +
    (1 + 4 * (X ^ p) ^ 2) * EP p +
    (2 - 4 * (X ^ p) ^ 2) * (EP p).comp (2 * X) +
    4 * X ^ p * OP p - 2 * X ^ p * (OP p).comp (2 * X)

theorem EP_comp_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (U : K[X]) :
    (1 - U ^ 2) * ((EP p).comp U).derivative = (U - U ^ p) * U.derivative := by
  have he := LPsrc_comp_source (K := K) p hp U
  simpa only [LPsrc, add_comp, C_comp, derivative_add, derivative_C, zero_add] using he

theorem OP_comp_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (U : K[X]) :
    (1 - U ^ 2) * ((OP p).comp U).derivative = (1 - U ^ (p - 1)) * U.derivative := by
  have he := congrArg (fun P : K[X] => P.comp U) (OP_cleared_derivative p hp)
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp] at he
  rw [derivative_comp]
  linear_combination U.derivative * he

private theorem prime_field_numeral_pow (p a : ℕ) [Fact p.Prime] [CharP K p] :
    (C (a : K)) ^ p = C (a : K) := by
  rw [← map_pow, WPFiniteField.natCast_pow_char p a]

theorem UW1_derivative_eq (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ((LPsrc p).comp (Tc : K[X])).derivative = (UW1rhs p).derivative := by
  let qT : K[X] := 1 - X ^ 2
  let B : K[X] := 4 * X ^ 2 - 1
  have hB : B ≠ 0 := by
    intro hz
    have he := congrArg (fun P : K[X] => P.eval 0) hz
    simp [B] at he
  have hqT : qT ≠ 0 := by
    intro hz
    have he := congrArg (fun P : K[X] => P.eval 0) hz
    simp [qT] at he
  have hDXp : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, CharP.cast_eq_zero K p, C_0, zero_mul]
  have hTcD : (Tc : K[X]).derivative = 3 * B := by
    unfold Tc B
    simp only [derivative_sub, derivative_mul, derivative_ofNat, zero_mul, zero_add,
      derivative_X_pow, derivative_X, mul_one, Nat.cast_ofNat, map_ofNat]
    norm_num only [Nat.reduceSub]
    ring
  have hTcPow : (Tc : K[X]) ^ p = 4 * (X ^ p) ^ 3 - 3 * X ^ p := by
    unfold Tc
    rw [sub_pow_char (p := p), mul_pow, mul_pow]
    have h4 : (4 : K[X]) ^ p = 4 := prime_field_numeral_pow (K := K) p 4
    have h3 : (3 : K[X]) ^ p = 3 := prime_field_numeral_pow (K := K) p 3
    rw [h4, h3, ← pow_mul, Nat.mul_comm 3 p, pow_mul]
  have hc := LPsrc_comp_source (K := K) p hp (Tc : K[X])
  have hfactor : (1 - (Tc : K[X]) ^ 2) = qT * B ^ 2 := by unfold Tc qT B; ring
  rw [hfactor, hTcD] at hc
  have hL : qT * B * ((LPsrc p).comp (Tc : K[X])).derivative = 3 * (Tc - Tc ^ p) := by
    apply mul_left_cancel₀ hB
    linear_combination hc
  have hE : qT * (EP p : K[X]).derivative = X - X ^ p := by
    have he := LPsrc_cleared_derivative (K := K) p hp
    simpa only [LPsrc, derivative_add, derivative_C, zero_add, qT] using he
  have h2pow : (2 : K[X]) ^ p = 2 := prime_field_numeral_pow (K := K) p 2
  have h2Xpow : (2 * X : K[X]) ^ p = 2 * X ^ p := by rw [mul_pow, h2pow]
  have hE2 := LPsrc_comp_source (K := K) p hp (2 * X : K[X])
  simp only [LPsrc, add_comp, C_comp, derivative_add, derivative_C, zero_add,
    derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_X, mul_one] at hE2
  rw [h2Xpow] at hE2
  have hE2' : B * ((EP p).comp (2 * X) : K[X]).derivative = -4 * (X - X ^ p) := by
    dsimp only [B]
    linear_combination -hE2
  have hO := OP_cleared_derivative (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h2pred : (2 : K) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ h2
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa only [one_mul, Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have h2predP : (2 : K[X]) ^ (p - 1) = 1 := by
    change C (2 : K) ^ (p - 1) = 1
    rw [← map_pow, h2pred, C_1]
  have hO2 := OP_comp_source (K := K) p hp (2 * X : K[X])
  simp only [derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_X,
    mul_one, mul_pow, h2predP, one_mul] at hO2
  have hO2' : B * ((OP p).comp (2 * X) : K[X]).derivative = -2 * (1 - X ^ (p - 1)) := by
    dsimp only [B]
    linear_combination -hO2
  have hxp : X * X ^ (p - 1) = (X : K[X]) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hR : qT * B * (UW1rhs p : K[X]).derivative = 3 * (Tc - Tc ^ p) := by
    rw [hTcPow]
    unfold UW1rhs Tc
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_C,
      derivative_ofNat, derivative_one, derivative_pow, hDXp, zero_mul, mul_zero,
      zero_add, add_zero, sub_zero]
    dsimp only [qT, B] at hE hE2' hO2' ⊢
    linear_combination (4 * X ^ 2 - 1) * (1 + 4 * (X ^ p) ^ 2) * hE +
      (1 - X ^ 2) * (2 - 4 * (X ^ p) ^ 2) * hE2' +
      4 * X ^ p * (4 * X ^ 2 - 1) * hO - 2 * X ^ p * (1 - X ^ 2) * hO2' -
      12 * X ^ p * X * hxp
  apply mul_left_cancel₀ (mul_ne_zero hqT hB)
  linear_combination hL - hR

private theorem EP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (EP p : K[X]).eval t = WPFiniteField.E p t := by
  simp only [EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg, eval_X,
    LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
  ring

theorem UW1rhs_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (UW1rhs p : K[X]).eval t = WPFiniteNC122.q p * (1 - 4 * (t ^ p) ^ 2) +
      (1 + 4 * (t ^ p) ^ 2) * WPFiniteField.E p t +
      (2 - 4 * (t ^ p) ^ 2) * WPFiniteField.E p (2 * t) +
      4 * t ^ p * WPFiniteField.O p t - 2 * t ^ p * WPFiniteField.O p (2 * t) := by
  simp only [UW1rhs, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    eval_one, eval_ofNat, eval_comp, EP_eval, OP_eval]

private theorem Tc_eval (t : K) : (Tc : K[X]).eval t = 4 * t ^ 3 - 3 * t := by simp [Tc]

private theorem EP_even (p : ℕ) : (EP p : K[X]).comp (-X) = EP p := by
  unfold EP
  simp only [mul_comp, C_comp, add_comp, comp_neg_X_comp_neg_X]
  ring

private theorem OP_odd (p : ℕ) : (OP p : K[X]).comp (-X) = -OP p := by
  unfold OP
  simp only [mul_comp, C_comp, sub_comp, comp_neg_X_comp_neg_X]
  ring

private theorem UW1_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((LPsrc p).comp (Tc : K[X]) - UW1rhs p).comp (-X) = (LPsrc p).comp Tc - UW1rhs p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hTc : (Tc : K[X]).comp (-X) = (-X).comp Tc := by
    simp only [Tc, sub_comp, mul_comp, ofNat_comp, pow_comp, X_comp, neg_comp]
    ring
  have h2arg : (2 * X : K[X]).comp (-X) = (-X).comp (2 * X) := by simp
  have hE2 : ((EP p).comp (2 * X) : K[X]).comp (-X) = (EP p).comp (2 * X) := by
    rw [comp_assoc, h2arg, ← comp_assoc, EP_even]
  have hO2 : ((OP p).comp (2 * X) : K[X]).comp (-X) = -(OP p).comp (2 * X) := by
    rw [comp_assoc, h2arg, ← comp_assoc, OP_odd, neg_comp]
  have hR : (UW1rhs p : K[X]).comp (-X) = UW1rhs p := by
    unfold UW1rhs
    simp only [sub_comp, add_comp, mul_comp, C_comp, one_comp, ofNat_comp,
      pow_comp, X_comp, hodd.neg_pow, EP_even, OP_odd, hE2, hO2]
    ring
  rw [sub_comp, comp_assoc, hTc, ← comp_assoc, WPFiniteNC122Residue.LPsrc_even, hR]

private theorem scale_degree (a : ℕ) (P : K[X]) (n : ℕ) (hP : P.natDegree ≤ n) :
    ((a : K[X]) * P).natDegree ≤ n := by
  change (C (a : K) * P).natDegree ≤ n
  exact (natDegree_C_mul_le _ _).trans hP

private theorem mul_degree (P Q : K[X]) (m n : ℕ) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    (P * Q).natDegree ≤ m + n := (natDegree_mul_le).trans (Nat.add_le_add hP hQ)

private theorem UW1_small_degree (p : ℕ) [Fact p.Prime] :
    ((LPsrc p).comp (Tc : K[X]) - UW1rhs p).natDegree < 3 * p := by
  have hp := (Fact.out : p.Prime).two_le
  have hnegX : (-X : K[X]).natDegree ≤ 1 := by simp
  have hLPn : ((LP p : K[X]).comp (-X)).natDegree ≤ p - 1 := by
    calc
      _ ≤ (LP p : K[X]).natDegree * (-X : K[X]).natDegree := natDegree_comp_le
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul (LP_natDegree_le p) hnegX
      _ = p - 1 := by omega
  have hEP : (EP p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le (LP_natDegree_le p) hLPn))
  have hOP : (OP p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le (LP_natDegree_le p) hLPn))
  have hL : (LPsrc p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) hEP)
  have hX3 : (X ^ 3 : K[X]).natDegree ≤ 3 := by simp
  have hX1 : (X : K[X]).natDegree ≤ 3 := by simp
  have hTc : (Tc : K[X]).natDegree ≤ 3 :=
    (natDegree_sub_le _ _).trans (max_le (scale_degree 4 _ _ hX3) (scale_degree 3 _ _ hX1))
  have hLC : ((LPsrc p).comp (Tc : K[X])).natDegree ≤ (p - 1) * 3 :=
    (natDegree_comp_le).trans (Nat.mul_le_mul hL hTc)
  have h2X : (2 * X : K[X]).natDegree ≤ 1 := scale_degree 2 _ _ (by simp)
  have hE2 : ((EP p).comp (2 * X) : K[X]).natDegree ≤ p - 1 :=
    (natDegree_comp_le).trans ((Nat.mul_le_mul hEP h2X).trans (by simp))
  have hO2 : ((OP p).comp (2 * X) : K[X]).natDegree ≤ p - 1 :=
    (natDegree_comp_le).trans ((Nat.mul_le_mul hOP h2X).trans (by simp))
  have hXP : (X ^ p : K[X]).natDegree ≤ p := by simp
  have hXP2 : ((X ^ p) ^ 2 : K[X]).natDegree ≤ 2 * p := by
    exact (natDegree_pow_le).trans (by omega)
  have h4XP2 := scale_degree 4 _ _ hXP2
  have hpoly1 : (1 - 4 * (X ^ p) ^ 2 : K[X]).natDegree ≤ 2 * p :=
    (natDegree_sub_le _ _).trans (max_le (by simp) h4XP2)
  have hpoly2 : (1 + 4 * (X ^ p) ^ 2 : K[X]).natDegree ≤ 2 * p :=
    (natDegree_add_le _ _).trans (max_le (by simp) h4XP2)
  have hpoly3 : (2 - 4 * (X ^ p) ^ 2 : K[X]).natDegree ≤ 2 * p :=
    (natDegree_sub_le _ _).trans (max_le (by simp) h4XP2)
  have hT0 : (C (WPFiniteNC122.q p) * (1 - 4 * (X ^ p) ^ 2) : K[X]).natDegree ≤ 3 * p - 1 :=
    (natDegree_C_mul_le _ _).trans (hpoly1.trans (by omega))
  have hT1 : ((1 + 4 * (X ^ p) ^ 2) * EP p : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ hpoly2 hEP).trans (by omega)
  have hT2 : ((2 - 4 * (X ^ p) ^ 2) * (EP p).comp (2 * X) : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ hpoly3 hE2).trans (by omega)
  have hT3 : (4 * X ^ p * OP p : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ (scale_degree 4 _ _ hXP) hOP).trans (by omega)
  have hT4 : (2 * X ^ p * (OP p).comp (2 * X) : K[X]).natDegree ≤ 3 * p - 1 :=
    (mul_degree _ _ _ _ (scale_degree 2 _ _ hXP) hO2).trans (by omega)
  have hR : (UW1rhs p : K[X]).natDegree ≤ 3 * p - 1 :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le
          ((natDegree_add_le _ _).trans (max_le hT0 hT1)) hT2)) hT3)) hT4)
  have hLC' : ((LPsrc p).comp (Tc : K[X])).natDegree ≤ 3 * p - 1 := hLC.trans (by omega)
  have he := (natDegree_sub_le _ _).trans (max_le hLC' hR)
  omega

private theorem E_O_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.E p (1 : K) = -WPFiniteNC122.q p ∧
    WPFiniteField.O p (1 : K) = WPFiniteNC122.q p ∧
    WPFiniteField.E p (2 : K) = -3 * WPFiniteJNormalization.r p / 2 ∧
    WPFiniteField.O p (2 : K) = -2 * WPFiniteNC122.q p + 3 * WPFiniteJNormalization.r p / 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hl1 : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K) (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hlN1 : WPFiniteField.ell p (-1 : K) = -2 * WPFiniteNC122.q p := by
    have he := WPFiniteField.ell_reflection p (by omega) (-1 : K)
    rw [show (1 - -1 : K) = 2 by ring, WPFiniteLoop.ell_two p hp] at he
    exact he.symm
  constructor
  · unfold WPFiniteField.E; rw [hl1, hlN1]; field_simp [h2]; ring
  constructor
  · unfold WPFiniteField.O; rw [hl1, hlN1]; field_simp [h2]; ring
  constructor
  · unfold WPFiniteField.E; rw [WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp]
    unfold WPFiniteJNormalization.r; field_simp [h2]; ring
  · unfold WPFiniteField.O; rw [WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp]
    unfold WPFiniteNC122.q WPFiniteJNormalization.r; field_simp [h2]; ring

theorem UW1_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LPsrc p).comp (Tc : K[X]) = UW1rhs p := by
  let Q : K[X] := (LPsrc p).comp Tc - UW1rhs p
  have hd : Q.derivative = 0 := by
    rw [derivative_sub, UW1_derivative_eq p hp, sub_self]
  have hEll0 : WPFiniteField.ell p (0 : K) = 0 := by
    unfold WPFiniteField.ell
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero_pow (by have h := (Finset.mem_Ico.mp hj).1; omega : j ≠ 0), zero_div]
  have hE0 : WPFiniteField.E p (0 : K) = 0 := by simp [WPFiniteField.E, hEll0]
  have hO0 : WPFiniteField.O p (0 : K) = 0 := by simp [WPFiniteField.O, hEll0]
  have h0 : Q.eval 0 = 0 := by
    dsimp only [Q]
    rw [eval_sub, eval_comp, Tc_eval]
    simp only [zero_pow (by decide : 3 ≠ 0), mul_zero, sub_zero]
    rw [LPsrc_eval, UW1rhs_eval]
    change WPFiniteNC122.q p + WPFiniteField.E p (0 : K) - _ = 0
    simp only [zero_pow (Fact.out : p.Prime).ne_zero, mul_zero, hE0, hO0, sub_zero, add_zero]
    ring
  have he := E_O_ends (K := K) p hp
  have hL1 : (LPsrc p : K[X]).eval 1 = 0 := by
    rw [LPsrc_eval]
    change WPFiniteNC122.q p + WPFiniteField.E p (1 : K) = 0
    rw [he.1, add_neg_cancel]
  have hR1 : (UW1rhs p : K[X]).eval 1 = 0 := by
    rw [UW1rhs_eval]
    simp only [one_pow, mul_one]
    rw [he.1, he.2.1, he.2.2.1, he.2.2.2]
    have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
    field_simp [h2]
    ring
  have h1 : Q.eval 1 = 0 := by
    dsimp only [Q]
    rw [eval_sub, eval_comp, Tc_eval, one_pow,
      show (4 * (1 : K) - 3 * 1) = 1 by ring, hL1, hR1, sub_self]
  have hz := even_kernel_three_zero p hp Q (UW1_small_degree p) hd (UW1_even p hp) h0 h1
  exact sub_eq_zero.mp hz

theorem UW1_literal (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteNC122.q p + WPFiniteField.E p (4 * t ^ 3 - 3 * t) =
      WPFiniteNC122.q p * (1 - 4 * (t ^ p) ^ 2) +
      (1 + 4 * (t ^ p) ^ 2) * WPFiniteField.E p t +
      (2 - 4 * (t ^ p) ^ 2) * WPFiniteField.E p (2 * t) +
      4 * t ^ p * WPFiniteField.O p t - 2 * t ^ p * WPFiniteField.O p (2 * t) := by
  have he := congrArg (fun P : K[X] => P.eval t) (UW1_polynomial (K := K) p hp)
  simpa only [eval_comp, Tc_eval, LPsrc_eval, UW1rhs_eval, WPFiniteNC122.L] using he

theorem UW1_four_logs_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LPsrc p).comp (Tc : K[X]) = C (WPFiniteNC122.q p) * (1 - 4 * (X ^ p) ^ 2) +
      (2 * (X ^ p) ^ 2 + 2 * X ^ p + C (2 : K)⁻¹) * LP p +
      (2 * (X ^ p) ^ 2 - 2 * X ^ p + C (2 : K)⁻¹) * (LP p).comp (-X) +
      (-2 * (X ^ p) ^ 2 - X ^ p + 1) * (LP p).comp (2 * X) +
      (-2 * (X ^ p) ^ 2 + X ^ p + 1) * (LP p).comp (-2 * X) := by
  rw [UW1_polynomial p hp]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hunit : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have harg : (-X : K[X]).comp (2 * X) = -2 * X := by simp
  unfold UW1rhs EP OP
  simp only [mul_comp, C_comp, add_comp, sub_comp, comp_assoc, harg]
  linear_combination ((2 * (X ^ p) ^ 2 + 2 * X ^ p) * (LP p : K[X]) +
    (2 * (X ^ p) ^ 2 - 2 * X ^ p) * (LP p).comp (-X) +
    (1 - 2 * (X ^ p) ^ 2 - X ^ p) * (LP p).comp (2 * X) +
    (1 - 2 * (X ^ p) ^ 2 + X ^ p) * (LP p).comp (-2 * X)) * hunit

theorem UW1_four_logs (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteNC122.q p + WPFiniteField.E p (4 * t ^ 3 - 3 * t) =
      WPFiniteNC122.q p * (1 - 4 * (t ^ p) ^ 2) +
      (2 * (t ^ p) ^ 2 + 2 * t ^ p + 1 / 2) * WPFiniteField.ell p t +
      (2 * (t ^ p) ^ 2 - 2 * t ^ p + 1 / 2) * WPFiniteField.ell p (-t) +
      (-2 * (t ^ p) ^ 2 - t ^ p + 1) * WPFiniteField.ell p (2 * t) +
      (-2 * (t ^ p) ^ 2 + t ^ p + 1) * WPFiniteField.ell p (-2 * t) := by
  have he := congrArg (fun P : K[X] => P.eval t) (UW1_four_logs_polynomial (K := K) p hp)
  simpa only [eval_comp, Tc_eval, LPsrc_eval, WPFiniteNC122.L, eval_add, eval_sub,
    eval_mul, eval_pow, eval_X, eval_C, eval_one, eval_ofNat, eval_neg, LP_eval_eq,
    one_div] using he

end WPFiniteCubicLog
