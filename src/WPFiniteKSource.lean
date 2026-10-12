import WPFiniteAffineLog

open scoped BigOperators
open Polynomial

namespace WPFiniteKSource

open WPFiniteAffineLog

variable {K : Type*} [Field K]

noncomputable def RP (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, C (((j : K) ^ 2)⁻¹) * X ^ j

noncomputable def EP (p : ℕ) : K[X] := C (2 : K)⁻¹ * ((LP p) + (LP p).comp (-X))

noncomputable def OP (p : ℕ) : K[X] := C (2 : K)⁻¹ * ((LP p) - (LP p).comp (-X))

noncomputable def LPsrc (p : ℕ) : K[X] := C (WPFiniteNC122.q p) + EP p

noncomputable def AP : K[X] := C (2 : K)⁻¹ * (1 + X)

noncomputable def BP : K[X] := C (2 : K)⁻¹ * (1 - X)

noncomputable def S2P (p : ℕ) : K[X] := (RP p).comp BP + (RP p).comp AP

noncomputable def JLP (p : ℕ) : K[X] := C (2 : K)⁻¹ * ((RP p).comp AP - (RP p).comp BP)

noncomputable def KsrcP (p : ℕ) (c : K) : K[X] :=
  C (2 : K)⁻¹ * ((RP p).comp (1 - X) + (RP p).comp (1 + X) + C ((WPFiniteNC122.q p) ^ 2)) -
    C (6 : K)⁻¹ * S2P p + C (2 * c / 3 - WPFiniteNC122.q p) * LPsrc p

theorem RP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (RP p).eval t = WPFiniteField.R p t := by
  simp only [RP, WPFiniteField.R, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem RP_natDegree_le (p : ℕ) : (RP p : K[X]).natDegree ≤ p - 1 := by
  unfold RP
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).2
  calc
    _ ≤ (X ^ j : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ j := by simp
    _ ≤ p - 1 := by omega

theorem LPsrc_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (LPsrc p).eval t = WPFiniteNC122.L p t := by
  simp only [LPsrc, EP, WPFiniteNC122.L, WPFiniteField.E, eval_add, eval_C, eval_mul,
    eval_comp, eval_neg, eval_X, LP_eval_eq, div_eq_mul_inv]
  ring

theorem OP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (OP p).eval t = WPFiniteField.O p t := by
  simp only [OP, WPFiniteField.O, eval_sub, eval_mul, eval_C, eval_comp, eval_neg,
    eval_X, LP_eval_eq, div_eq_mul_inv]
  ring

theorem S2P_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (S2P p).eval t = WPFiniteNC122.S2 p t := by
  simp only [S2P, AP, BP, WPFiniteNC122.S2, eval_add, eval_comp, eval_mul, eval_C,
    eval_sub, eval_one, eval_X, RP_eval, div_eq_mul_inv]
  rw [mul_comm (1 - t) (2 : K)⁻¹, mul_comm (1 + t) (2 : K)⁻¹]

theorem JLP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (JLP p).eval t = WPFiniteNC122.J_L p t := by
  simp only [JLP, AP, BP, WPFiniteNC122.J_L, eval_sub, eval_comp, eval_mul, eval_C,
    eval_add, eval_one, eval_X, RP_eval, div_eq_mul_inv]
  rw [mul_comm (1 - t) (2 : K)⁻¹, mul_comm (1 + t) (2 : K)⁻¹]
  ring

theorem KsrcP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (c t : K) :
    (KsrcP p c).eval t = WPFiniteNC122.Ksrc p c t := by
  simp only [KsrcP, S2P, LPsrc, EP, AP, BP, WPFiniteNC122.Ksrc, WPFiniteNC122.S2,
    WPFiniteNC122.L, WPFiniteField.E, eval_sub, eval_add, eval_mul, eval_comp,
    eval_C, eval_one, eval_X, eval_neg, RP_eval, LP_eval_eq, div_eq_mul_inv]
  rw [mul_comm (1 - t) (2 : K)⁻¹, mul_comm (1 + t) (2 : K)⁻¹]
  ring

private theorem comp_linear_degree (p : ℕ) (F U : K[X])
    (hF : F.natDegree ≤ p - 1) (hU : U.natDegree ≤ 1) :
    (F.comp U).natDegree ≤ p - 1 := by
  calc
    _ ≤ F.natDegree * U.natDegree := natDegree_comp_le
    _ ≤ (p - 1) * 1 := Nat.mul_le_mul hF hU
    _ = p - 1 := by simp

theorem KsrcP_natDegree_le (p : ℕ) (c : K) : (KsrcP p c).natDegree ≤ p - 1 := by
  have hm : (-X : K[X]).natDegree ≤ 1 := by simp
  have hplus : (1 + X : K[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  have hminus : (1 - X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hAP : (AP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hplus
  have hBP : (BP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hminus
  have hE : (EP p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans
      (max_le (LP_natDegree_le p) (comp_linear_degree p _ _ (LP_natDegree_le p) hm)))
  have hL : (LPsrc p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp) hE)
  have hS : (S2P p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le
      (comp_linear_degree p _ _ (RP_natDegree_le p) hBP)
      (comp_linear_degree p _ _ (RP_natDegree_le p) hAP))
  have hbase : (((RP p : K[X]).comp (1 - X) + (RP p).comp (1 + X)) +
      C ((WPFiniteNC122.q p) ^ 2)).natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        (comp_linear_degree p _ _ (RP_natDegree_le p) hminus)
        (comp_linear_degree p _ _ (RP_natDegree_le p) hplus))) (by simp))
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hbase) ((natDegree_C_mul_le _ _).trans hS)))
    ((natDegree_C_mul_le _ _).trans hL))

theorem KsrcP_normalized_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c : K) :
    (KsrcP p c).eval 1 = 0 ∧ (KsrcP p c).eval (-1) = 0 := by
  rw [KsrcP_eval, KsrcP_eval]
  exact WPFiniteNC122.Ksrc_normalized_end p hp c

theorem LP_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LP p : K[X]).comp (1 - X) = LP p := by
  let f := ZMod.castHom (dvd_refl p) K
  have hmap : (WPFiniteInversion.ellPolynomial p).map f = (LP p : K[X]) := by
    simp only [WPFiniteInversion.ellPolynomial, LP, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_inv₀, map_natCast]
  have he := congrArg (Polynomial.map f)
    (WPFiniteInversion.ellPolynomial_reflection_eq p (by omega : 3 ≤ p))
  simpa only [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, hmap] using he

theorem LP_plus_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LP p : K[X]).comp (1 + X) = (LP p).comp (-X) := by
  have he := congrArg (fun P : K[X] => P.comp (-X)) (LP_reflection (K := K) p hp)
  simpa only [comp_assoc, sub_comp, one_comp, X_comp, sub_neg_eq_add] using he

private theorem C_two_unit (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
  change C (2 : K)⁻¹ * C (2 : K) = 1
  rw [← C_mul, inv_mul_cancel₀ (WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))), C_1]

theorem X_mul_derivative_RP (p : ℕ) [Fact p.Prime] [CharP K p] :
    X * (RP p : K[X]).derivative = LP p := by
  unfold RP LP
  rw [derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hden := WPFiniteField.denominator_ne_zero (K := K) p j hj
  have hc : (((j : K) ^ 2)⁻¹) * j = (j : K)⁻¹ := by field_simp
  rw [derivative_C_mul_X_pow, hc]
  calc
    X * (C ((j : K)⁻¹) * X ^ (j - 1)) =
        C ((j : K)⁻¹) * (X ^ (j - 1) * X) := by ring
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hjpos]

theorem RP_comp_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (U : K[X]) :
    U * ((RP p).comp U).derivative = (LP p).comp U * U.derivative := by
  have he := congrArg (fun P : K[X] => P.comp U) (X_mul_derivative_RP (K := K) p)
  rw [mul_comp, X_comp] at he
  rw [derivative_comp]
  linear_combination U.derivative * he

private theorem LP_affine_both (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LP p : K[X]).comp AP = LPsrc p ∧ (LP p : K[X]).comp BP = LPsrc p := by
  have hAP := affine_log_polynomial (K := K) p hp
  have hBP : (BP : K[X]) = 1 - AP := by
    unfold BP AP
    linear_combination C_two_unit (K := K) p hp
  constructor
  · exact hAP
  · calc
      _ = ((LP p).comp (1 - X)).comp AP := by
        rw [comp_assoc]
        simp only [sub_comp, one_comp, X_comp, hBP]
      _ = _ := by rw [LP_reflection p hp]; exact hAP

private theorem affine_RP_sources (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * ((RP p).comp AP).derivative = (1 - X) * LPsrc p ∧
      (1 - X ^ 2 : K[X]) * ((RP p).comp BP).derivative = -(1 + X) * LPsrc p := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hc : (C (2 : K)⁻¹ : K[X]) ≠ 0 := C_ne_zero.mpr (inv_ne_zero htwo)
  have hAP := RP_comp_derivative (K := K) p (AP : K[X])
  have hBP := RP_comp_derivative (K := K) p (BP : K[X])
  have hlogs := LP_affine_both (K := K) p hp
  rw [hlogs.1] at hAP
  rw [hlogs.2] at hBP
  have hDA : (AP : K[X]).derivative = C (2 : K)⁻¹ := by
    simp only [AP, derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
      derivative_one, derivative_X, mul_one]
  have hDB : (BP : K[X]).derivative = -C (2 : K)⁻¹ := by
    simp only [BP, derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub,
      derivative_one, derivative_X, zero_sub, mul_neg, mul_one]
  rw [hDA] at hAP
  rw [hDB] at hBP
  constructor
  · apply mul_left_cancel₀ hc
    calc
      _ = (1 - X) * (AP * ((RP p).comp AP).derivative) := by unfold AP; ring
      _ = _ := by rw [hAP]; ring
  · apply mul_left_cancel₀ hc
    calc
      _ = (1 + X) * (BP * ((RP p).comp BP).derivative) := by unfold BP; ring
      _ = _ := by rw [hBP]; ring

theorem S2P_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (S2P p).derivative = -2 * X * LPsrc p := by
  unfold S2P
  rw [derivative_add, mul_add, (affine_RP_sources p hp).1, (affine_RP_sources p hp).2]
  ring

theorem JLP_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (JLP p).derivative = LPsrc p := by
  unfold JLP
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub]
  have he := affine_RP_sources (K := K) p hp
  calc
    _ = C (2 : K)⁻¹ * ((1 - X ^ 2) * ((RP p).comp AP).derivative -
        (1 - X ^ 2) * ((RP p).comp BP).derivative) := by ring
    _ = _ := by rw [he.1, he.2]; linear_combination LPsrc p * (C_two_unit (K := K) p hp)

theorem LPsrc_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (LPsrc p).derivative = X - X ^ p := by
  have hpred : Even (p - 1) := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n, by omega⟩
  have hd : (EP p : K[X]).derivative =
      C (2 : K)⁻¹ * ((1 - X) ^ (p - 1) - (1 + X) ^ (p - 1)) := by
    unfold EP
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
      derivative_comp, derivative_neg, derivative_X, LP_derivative_closed_eq]
    simp only [sub_comp, pow_comp, one_comp, X_comp, sub_neg_eq_add]
    rw [hpred.neg_pow]
    ring
  unfold LPsrc
  rw [derivative_add, derivative_C, zero_add, hd]
  have hminus : (1 - X : K[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char (p := p), one_pow]
  have hplus : (1 + X : K[X]) ^ p = 1 + X ^ p := by rw [add_pow_char (p := p), one_pow]
  have hminusPow : (1 - X : K[X]) ^ p = (1 - X) ^ (p - 1) * (1 - X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hplusPow : (1 + X : K[X]) ^ p = (1 + X) ^ (p - 1) * (1 + X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  calc
    _ = C (2 : K)⁻¹ * ((1 + X) * (1 - X) ^ p - (1 - X) * (1 + X) ^ p) := by
      rw [hminusPow, hplusPow]
      ring
    _ = _ := by rw [hminus, hplus]; linear_combination (X - X ^ p) * (C_two_unit (K := K) p hp)

theorem KsrcP_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c : K) :
    (1 - X ^ 2 : K[X]) * (KsrcP p c).derivative =
      C (WPFiniteNC122.q p - 2 * c / 3) * X ^ p - OP p -
        C (2 / 3 : K) * X * (LPsrc p - C c) := by
  have hm := RP_comp_derivative (K := K) p (1 - X : K[X])
  have hp1 := RP_comp_derivative (K := K) p (1 + X : K[X])
  rw [derivative_sub, derivative_one, derivative_X, zero_sub, LP_reflection p hp] at hm
  rw [derivative_add, derivative_one, derivative_X, zero_add, LP_plus_reflection p hp] at hp1
  have hsum : (1 - X ^ 2 : K[X]) *
      (C (2 : K)⁻¹ * ((RP p).comp (1 - X) + (RP p).comp (1 + X) +
        C ((WPFiniteNC122.q p) ^ 2))).derivative = -OP p - X * EP p := by
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
      derivative_add, derivative_C, add_zero]
    unfold OP EP
    linear_combination C (2 : K)⁻¹ * (1 + X) * hm + C (2 : K)⁻¹ * (1 - X) * hp1
  have hdk : (KsrcP p c : K[X]).derivative =
      (C (2 : K)⁻¹ * ((RP p).comp (1 - X) + (RP p).comp (1 + X) +
        C ((WPFiniteNC122.q p) ^ 2))).derivative -
        C (6 : K)⁻¹ * (S2P p).derivative +
        C (2 * c / 3 - WPFiniteNC122.q p) * (LPsrc p).derivative := by
    unfold KsrcP
    rw [derivative_add, derivative_sub]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  rw [hdk]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  have hc : (C (6 : K)⁻¹ : K[X]) * 6 = 1 := by
    change C (6 : K)⁻¹ * C (6 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h6, C_1]
  calc
    _ = (1 - X ^ 2) *
        (C (2 : K)⁻¹ * ((RP p).comp (1 - X) + (RP p).comp (1 + X) +
          C ((WPFiniteNC122.q p) ^ 2))).derivative -
        C (6 : K)⁻¹ * ((1 - X ^ 2) * (S2P p).derivative) +
        C (2 * c / 3 - WPFiniteNC122.q p) * ((1 - X ^ 2) * (LPsrc p).derivative) := by ring
    _ = _ := by
      rw [hsum, S2P_cleared_derivative p hp, LPsrc_cleared_derivative p hp]
      unfold LPsrc
      simp only [div_eq_mul_inv, map_sub, map_mul, map_ofNat]
      have hcinv : (C (3 : K)⁻¹ : K[X]) * 3 = 1 := by
        change C (3 : K)⁻¹ * C (3 : K) = 1
        rw [← C_mul, inv_mul_cancel₀ h3, C_1]
      apply mul_left_cancel₀ (C_ne_zero.mpr h3)
      simp only [map_ofNat]
      linear_combination ((C (WPFiniteNC122.q p) + EP p) * X) * hc +
        2 * ((C (WPFiniteNC122.q p) + EP p) * X) * hcinv

end WPFiniteKSource
