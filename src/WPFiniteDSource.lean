import WPFiniteKSource

open scoped BigOperators
open Polynomial

namespace WPFiniteDSource

open WPFiniteAffineLog WPFiniteKSource

variable {K : Type*} [Field K]

noncomputable def DP (p : ℕ) (y : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 (j + 1),
    C (y ^ (j - k) / ((k : K) * (j : K))) * X ^ k

theorem DP_eval (p : ℕ) [Fact p.Prime] (x y : K) :
    (DP p y).eval x = WPFiniteLoop.D (p - 1) x y := by
  simp only [DP, WPFiniteLoop.D, Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [div_eq_mul_inv]
  ring

theorem DP_natDegree_le (p : ℕ) (y : K) : (DP p y).natDegree ≤ p - 1 := by
  unfold DP
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).2
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk' := (Finset.mem_Ico.mp hk).2
  calc
    _ ≤ (X ^ k : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ k := by simp
    _ ≤ p - 1 := by omega

theorem DP_eval_zero (p : ℕ) (y : K) : (DP p y).eval 0 = 0 := by
  unfold DP
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := (Finset.mem_Ico.mp hk).1
  simp only [eval_mul, eval_C, eval_pow, eval_X, zero_pow (by omega : k ≠ 0), mul_zero]

private theorem DP_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (y : K) :
    (DP p y).derivative = ∑ j ∈ Finset.Ico 1 p,
      C ((j : K)⁻¹) * ∑ k ∈ Finset.Ico 1 (j + 1), C (y ^ (j - k)) * X ^ (k - 1) := by
  unfold DP
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  have hj' := Finset.mem_Ico.mp hj
  have hkd : (k : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p k (Finset.mem_Ico.mpr (by omega))
  have hjd : (j : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j hj
  have hc : (y ^ (j - k) / ((k : K) * (j : K))) * k = y ^ (j - k) / (j : K) := by
    field_simp [hkd, hjd]
  rw [derivative_C_mul_X_pow, hc]
  simp only [div_eq_mul_inv, map_mul]
  ring

private theorem geometric_cutoff (j : ℕ) (y : K) :
    (X - C y) * (∑ k ∈ Finset.Ico 1 (j + 1), C (y ^ (j - k)) * X ^ (k - 1)) =
      (X : K[X]) ^ j - C (y ^ j) := by
  have he : (∑ k ∈ Finset.Ico 1 (j + 1), C (y ^ (j - k)) * (X : K[X]) ^ (k - 1)) =
      ∑ r ∈ Finset.range j, X ^ r * (C y) ^ (j - 1 - r) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show 1 + r - 1 = r by omega,
      show j - (1 + r) = j - 1 - r by omega, map_pow]
    ring
  rw [he, map_pow]
  exact (Commute.all (X : K[X]) (C y)).mul_geom_sum₂ j

theorem DP_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (y : K) :
    (X - C y) * (DP p y).derivative = (LP p : K[X]) - C (WPFiniteField.ell p y) := by
  rw [DP_derivative, Finset.mul_sum]
  unfold LP WPFiniteField.ell
  rw [map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = C ((j : K)⁻¹) * ((X - C y) *
        (∑ k ∈ Finset.Ico 1 (j + 1), C (y ^ (j - k)) * X ^ (k - 1))) := by ring
    _ = _ := by rw [geometric_cutoff]; simp only [div_eq_mul_inv, map_mul, map_pow]; ring

private theorem zero_of_derivative_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree < p) (hder : Q.derivative = 0)
    (hz : Q.eval 0 = 0) : Q = 0 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_eval_zero, eval_zero] using hz
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
  have hsmall : n ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have he : Q.coeff n * (n : K) = 0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (n - 1)) hder
    simpa only [coeff_derivative, ← Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p n hsmall)

theorem DP_at_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (DP p (1 : K)) = (RP p).comp (1 - X) := by
  have hlog1 : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hR1 : WPFiniteField.R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
  have hd := DP_cleared_derivative p (1 : K)
  simp only [map_one, hlog1, map_zero, sub_zero] at hd
  have hr := RP_comp_derivative (K := K) p (1 - X : K[X])
  rw [derivative_sub, derivative_one, derivative_X, zero_sub, LP_reflection p hp] at hr
  have hf : (X - 1 : K[X]) ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (X_ne_C (1 : K))
  have hder : ((DP p 1) - (RP p).comp (1 - X) : K[X]).derivative = 0 := by
    have hmul : (X - 1 : K[X]) *
      ((DP p (1 : K)) - (RP p).comp (1 - X) : K[X]).derivative = 0 := by
      rw [derivative_sub]
      linear_combination hd + hr
    exact (mul_eq_zero.mp hmul).resolve_left hf
  have hcomp : ((RP p : K[X]).comp (1 - X)).natDegree ≤ p - 1 := by
    calc
      _ ≤ (RP p : K[X]).natDegree * (1 - X : K[X]).natDegree := natDegree_comp_le
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul (RP_natDegree_le p)
        ((natDegree_sub_le _ _).trans (by simp))
      _ = p - 1 := by simp
  have hdeg : ((DP p 1) - (RP p).comp (1 - X) : K[X]).natDegree < p := by
    have he := (natDegree_sub_le _ _).trans (max_le (DP_natDegree_le p 1) hcomp)
    omega
  have hz : ((DP p 1) - (RP p).comp (1 - X) : K[X]).eval 0 = 0 := by
    simp only [eval_sub, DP_eval_zero, eval_comp, eval_sub, eval_one, eval_X,
      sub_zero, RP_eval, hR1, sub_self]
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hdeg hder hz)

private theorem comp_degree (p : ℕ) (F U : K[X])
    (hF : F.natDegree ≤ p - 1) (hU : U.natDegree ≤ 1) :
    (F.comp U).natDegree ≤ p - 1 := by
  calc
    _ ≤ F.natDegree * U.natDegree := natDegree_comp_le
    _ ≤ (p - 1) * 1 := Nat.mul_le_mul hF hU
    _ = p - 1 := by simp

theorem DP_at_neg_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (DP p (-1 : K)) = 2 * (RP p).comp AP + C ((WPFiniteNC122.q p) ^ 2) -
      (RP p).comp (1 + X) := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (C (2 : K)⁻¹ : K[X]) ≠ 0 := C_ne_zero.mpr (inv_ne_zero htwo)
  have hlogneg : WPFiniteField.ell p (-1 : K) = -2 * WPFiniteNC122.q p := by
    have he := WPFiniteField.ell_reflection p (by omega : 3 ≤ p) (-1 : K)
    rw [show (1 - (-1) : K) = 2 by ring, WPFiniteLoop.ell_two p hp] at he
    exact he.symm
  have hd := DP_cleared_derivative p (-1 : K)
  simp only [map_neg, map_one, sub_neg_eq_add, hlogneg, map_mul, map_ofNat] at hd
  have ha := RP_comp_derivative (K := K) p (AP : K[X])
  have hlogAP : (LP p : K[X]).comp AP = LPsrc p := affine_log_polynomial p hp
  have hDA : (AP : K[X]).derivative = C (2 : K)⁻¹ := by
    simp only [AP, derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
      derivative_one, derivative_X, mul_one]
  rw [hlogAP, hDA] at ha
  have hasource : (1 + X : K[X]) * ((RP p).comp AP).derivative = LPsrc p := by
    apply mul_left_cancel₀ hc
    unfold AP at ha ⊢
    linear_combination ha
  have hb := RP_comp_derivative (K := K) p (1 + X : K[X])
  rw [derivative_add, derivative_one, derivative_X, zero_add, mul_one,
    LP_plus_reflection p hp] at hb
  have htwoP : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ htwo, C_1]
  let V : K[X] := 2 * (RP p).comp AP + C ((WPFiniteNC122.q p) ^ 2) -
    (RP p).comp (1 + X)
  have hsourceV : (1 + X : K[X]) * V.derivative = LP p + 2 * C (WPFiniteNC122.q p) := by
    dsimp only [V]
    rw [derivative_sub, derivative_add, derivative_mul, derivative_ofNat,
      zero_mul, zero_add, derivative_C, add_zero]
    unfold LPsrc EP at hasource
    linear_combination 2 * hasource - hb +
      ((LP p : K[X]) + (LP p).comp (-X)) * htwoP
  have hf : (1 + X : K[X]) ≠ 0 := by
    rw [add_comm]
    simpa using (X_add_C_ne_zero (1 : K))
  have hder : ((DP p (-1 : K)) - V).derivative = 0 := by
    have hmul : (1 + X : K[X]) * ((DP p (-1 : K)) - V).derivative = 0 := by
      rw [derivative_sub]
      linear_combination hd - hsourceV
    exact (mul_eq_zero.mp hmul).resolve_left hf
  have hplusdeg : (1 + X : K[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp)
  have hAPdeg : (AP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hplusdeg
  have htwodeg : (2 * (RP p : K[X]).comp AP).natDegree ≤ p - 1 := by
    change (C (2 : K) * (RP p).comp AP).natDegree ≤ p - 1
    exact (natDegree_C_mul_le _ _).trans
      (comp_degree p (RP p) AP (RP_natDegree_le p) hAPdeg)
  have hVdeg : V.natDegree ≤ p - 1 := by
    dsimp only [V]
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le htwodeg (by simp)))
      (comp_degree p (RP p) (1 + X) (RP_natDegree_le p) hplusdeg))
  have hdeg : ((DP p (-1 : K)) - V).natDegree < p := by
    have he := (natDegree_sub_le _ _).trans (max_le (DP_natDegree_le p (-1 : K)) hVdeg)
    omega
  have hR1 : WPFiniteField.R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
  have hR2 : WPFiniteField.R p (2 : K) = -(WPFiniteNC122.q p) ^ 2 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_two_eq_fermat p hp)
    simpa only [← WPFiniteField.R_castHom, map_ofNat, map_neg, map_pow, map_intCast,
      WPFiniteNC122.q] using he
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hhalf := WPFiniteField.R_inversion p (2 : K) htwo
  rw [h2pow, hR2] at hhalf
  have hz : ((DP p (-1 : K)) - V).eval 0 = 0 := by
    dsimp only [V]
    simp only [eval_sub, DP_eval_zero, eval_add, eval_mul, eval_ofNat, eval_comp,
      eval_C, AP, eval_one, eval_X, add_zero, mul_one, RP_eval, hR1, hhalf]
    field_simp [htwo]
    ring
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hdeg hder hz)

theorem D_at_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteLoop.D (p - 1) t 1 = WPFiniteField.R p (1 - t) := by
  have he := congrArg (fun P : K[X] => P.eval t) (DP_at_one (K := K) p hp)
  simpa only [DP_eval, eval_comp, eval_sub, eval_one, eval_X, RP_eval] using he

theorem D_at_neg_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteLoop.D (p - 1) t (-1) =
      2 * WPFiniteField.R p ((1 + t) / 2) + (WPFiniteNC122.q p) ^ 2 -
        WPFiniteField.R p (1 + t) := by
  have he := congrArg (fun P : K[X] => P.eval t) (DP_at_neg_one (K := K) p hp)
  simp only [DP_eval, eval_sub, eval_add, eval_mul, eval_ofNat, eval_C, eval_comp,
    AP, eval_one, eval_X, RP_eval] at he
  simpa only [div_eq_mul_inv, mul_comm (2 : K)⁻¹ (1 + t)] using he

noncomputable def R_D (p : ℕ) (t : K) : K :=
  (WPFiniteLoop.D (p - 1) t 1 - WPFiniteLoop.D (p - 1) t (-1) -
    WPFiniteLoop.D (p - 1) (-t) (-1) + WPFiniteLoop.D (p - 1) (-t) 1) / 4

theorem R_D_reduction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    R_D p t = (WPFiniteField.R p (1 - t) + WPFiniteField.R p (1 + t) -
      WPFiniteNC122.S2 p t - (WPFiniteNC122.q p) ^ 2) / 2 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  unfold R_D WPFiniteNC122.S2
  rw [D_at_one p hp, D_at_neg_one p hp, D_at_neg_one p hp, D_at_one p hp]
  rw [show (1 + -t : K) = 1 - t by ring]
  simp only [sub_neg_eq_add]
  field_simp [htwo, hfour]
  ring

theorem Ksrc_original_D_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (c t : K) :
    WPFiniteNC122.Ksrc p c t = R_D p t - WPFiniteNC122.q p * WPFiniteNC122.L p t +
      (WPFiniteNC122.q p) ^ 2 + WPFiniteNC122.S2 p t / 3 +
        (2 * c / 3) * WPFiniteNC122.L p t := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hthree : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hsix : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  rw [R_D_reduction p hp]
  unfold WPFiniteNC122.Ksrc
  field_simp [htwo, hthree, hsix]
  ring

end WPFiniteDSource
