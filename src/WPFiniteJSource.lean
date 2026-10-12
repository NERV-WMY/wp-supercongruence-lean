import WPFiniteDSource

open scoped BigOperators
open Polynomial

namespace WPFiniteJSource

open WPFiniteAffineLog WPFiniteKSource

variable {K : Type*} [Field K]

noncomputable def H (n : ℕ) : K := ∑ j ∈ Finset.Ico 1 (n + 1), (j : K)⁻¹

noncomputable def JHP (p : ℕ) : K[X] :=
  ∑ r ∈ Finset.range ((p - 1) / 2),
    C ((WPFiniteNC122.q p + H r / 2) / ((2 * r + 1 : ℕ) : K)) * X ^ (2 * r + 1)

private theorem sum_full_pairs {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.Ico 1 (2 * n + 1), f j) =
      (∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j)) +
        ∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
      rw [Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1 + 1) (by omega)]
      rw [Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1) (by omega)]
      rw [ih]
      simp only [Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega)]
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
        show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      ac_rfl

theorem EP_half_cutoff (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (EP p : K[X]) = ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      C (((2 * j : ℕ) : K)⁻¹) * X ^ (2 * j) := by
  let n := (p - 1) / 2
  have hpn : p = 2 * n + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    dsimp only [n]
    omega
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ htwo, C_1]
  unfold EP LP
  rw [sum_comp]
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [← Finset.sum_add_distrib, hpn, sum_full_pairs, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  rw [show (2 * n + 1 - 1) / 2 = n by omega]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have heven : (-X : K[X]) ^ (2 * j) = X ^ (2 * j) := by
    rw [pow_mul, neg_sq, ← pow_mul]
  have hodd : (-X : K[X]) ^ (2 * j - 1) = -(X ^ (2 * j - 1)) := by
    rw [show 2 * j - 1 = 2 * (j - 1) + 1 by omega]
    simp only [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
  rw [heven, hodd]
  linear_combination (C (((2 * j : ℕ) : K)⁻¹) * X ^ (2 * j)) * hc

theorem H_half_eq_quotient (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (H ((p - 1) / 2) : K) = -2 * WPFiniteNC122.q p := by
  have he := (WPFiniteLoop.L_rational_ends (K := K) p hp).1
  simpa only [H, WPFiniteLoop.L, one_pow, one_div, WPFiniteNC122.q] using he

private theorem H_succ (n : ℕ) : (H (n + 1) : K) = H n + ((n + 1 : ℕ) : K)⁻¹ := by
  unfold H
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]

private theorem harmonic_geometric (n : ℕ) (q : K) :
    (1 - X ^ 2 : K[X]) * (∑ r ∈ Finset.range n, C (q + H r / 2) * X ^ (2 * r)) =
      C q + (∑ j ∈ Finset.Ico 1 (n + 1), C (((2 * j : ℕ) : K)⁻¹) * X ^ (2 * j)) -
        C (q + H n / 2) * X ^ (2 * n) := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      rw [mul_add, ih, H_succ]
      simp only [Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev, div_eq_mul_inv,
        map_add, map_mul]
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      ring

theorem JHP_natDegree_le (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (JHP p : K[X]).natDegree ≤ p - 2 := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  unfold JHP
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hr' := Finset.mem_range.mp hr
  calc
    _ ≤ (X ^ (2 * r + 1) : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ 2 * r + 1 := by simp
    _ ≤ p - 2 := by omega

theorem JHP_eval_zero (p : ℕ) : (JHP p : K[X]).eval 0 = 0 := by
  unfold JHP
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro r hr
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by omega : 2 * r + 1 ≠ 0), mul_zero]

theorem JHP_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (JHP p).derivative = LPsrc p := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have hder : (JHP p : K[X]).derivative =
      ∑ r ∈ Finset.range ((p - 1) / 2), C (WPFiniteNC122.q p + H r / 2) * X ^ (2 * r) := by
    unfold JHP
    rw [derivative_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hd : ((2 * r + 1 : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p
      (2 * r + 1) (Finset.mem_Ico.mpr (by omega))
    rw [derivative_C_mul_X_pow, div_mul_cancel₀ _ hd,
      show 2 * r + 1 - 1 = 2 * r by omega]
  have hz : (WPFiniteNC122.q p + H ((p - 1) / 2) / 2 : K) = 0 := by
    rw [H_half_eq_quotient p hp]
    have hd : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
      (Finset.mem_Ico.mpr (by omega))
    field_simp [hd]
    ring
  rw [hder, harmonic_geometric, hz, map_zero, zero_mul, sub_zero]
  rw [LPsrc, EP_half_cutoff p hp]

private theorem comp_degree (p : ℕ) (F U : K[X])
    (hF : F.natDegree ≤ p - 1) (hU : U.natDegree ≤ 1) :
    (F.comp U).natDegree ≤ p - 1 := by
  calc
    _ ≤ F.natDegree * U.natDegree := natDegree_comp_le
    _ ≤ (p - 1) * 1 := Nat.mul_le_mul hF hU
    _ = p - 1 := by simp

theorem JLP_natDegree_le (p : ℕ) : (JLP p : K[X]).natDegree ≤ p - 1 := by
  have hplus : (1 + X : K[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  have hminus : (1 - X : K[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hAP : (AP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hplus
  have hBP : (BP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hminus
  unfold JLP
  exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
    (max_le (comp_degree p _ _ (RP_natDegree_le p) hAP)
      (comp_degree p _ _ (RP_natDegree_le p) hBP)))

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

theorem JLP_eq_harmonic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (JLP p : K[X]) = JHP p := by
  have hdeg : ((JLP p : K[X]) - JHP p).natDegree < p := by
    have hd := (natDegree_sub_le _ _).trans
      (max_le (JLP_natDegree_le (K := K) p) ((JHP_natDegree_le p hp).trans (by omega)))
    omega
  have hf : (1 - X ^ 2 : K[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun P : K[X] => P.coeff 2) he
    have h1 : (1 : K[X]).coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by simp)
    rw [coeff_sub, h1, coeff_X_pow, if_pos rfl, coeff_zero, zero_sub] at hc
    exact (neg_ne_zero.mpr one_ne_zero) hc
  have hder : ((JLP p : K[X]) - JHP p).derivative = 0 := by
    have he : (1 - X ^ 2 : K[X]) * ((JLP p : K[X]) - JHP p).derivative = 0 := by
      rw [derivative_sub, mul_sub, JLP_cleared_derivative p hp,
        JHP_cleared_derivative p hp, sub_self]
    exact (mul_eq_zero.mp he).resolve_left hf
  have hz : ((JLP p : K[X]) - JHP p).eval 0 = 0 := by
    rw [eval_sub, JHP_eval_zero, JLP_eval]
    unfold WPFiniteNC122.J_L
    simp only [add_zero, sub_zero, sub_self, zero_div]
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hdeg hder hz)

theorem J_L_harmonic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteNC122.J_L p t = ∑ r ∈ Finset.range ((p - 1) / 2),
      ((WPFiniteNC122.q p + H r / 2) / ((2 * r + 1 : ℕ) : K)) * t ^ (2 * r + 1) := by
  have he := congrArg (fun P : K[X] => P.eval t) (JLP_eq_harmonic (K := K) p hp)
  simpa only [JLP_eval, JHP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using he

theorem harmonic_coefficient_tail (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (r : ℕ) (hr : r < (p - 1) / 2) :
    (WPFiniteNC122.q p + H r / 2) / ((2 * r + 1 : ℕ) : K) =
      -(∑ k ∈ Finset.Ico (r + 1) ((p - 1) / 2 + 1), (k : K)⁻¹) /
        (2 * ((2 * r + 1 : ℕ) : K)) := by
  have hsplit : (H r : K) +
      (∑ k ∈ Finset.Ico (r + 1) ((p - 1) / 2 + 1), (k : K)⁻¹) = H ((p - 1) / 2) := by
    unfold H
    exact Finset.sum_Ico_consecutive (fun k => (k : K)⁻¹) (by omega) (by omega)
  rw [H_half_eq_quotient p hp] at hsplit
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hm : ((2 * r + 1 : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p
    (2 * r + 1) (Finset.mem_Ico.mpr (by omega))
  field_simp [htwo, hm]
  simp only [one_div]
  linear_combination hsplit

noncomputable def HJP (p : ℕ) : K[X] :=
  ∑ r ∈ Finset.range ((p - 1) / 2),
    C (((WPFiniteNC122.q p + H r / 2) / ((2 * r + 1 : ℕ) : K)) /
      (5 : K) ^ (2 * r + 1)) *
        (C (5 : K)⁻¹ * (X + 1)) ^ ((p - 1) / 2 + r + 1) * (4 * X - 11) ^ (2 * r + 1)

theorem HJP_natDegree_le (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (HJP p : K[X]).natDegree ≤ 2 * p - 3 := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have hs : (C (5 : K)⁻¹ * (X + 1) : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hb : (4 * X - 11 : K[X]).natDegree ≤ 1 := by
    have h4 : (4 * X : K[X]).natDegree ≤ 1 := by
      change (C (4 : K) * X).natDegree ≤ 1
      exact (natDegree_C_mul_le _ _).trans (by simp)
    exact (natDegree_sub_le _ _).trans (max_le h4 (by simp))
  unfold HJP
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hr' := Finset.mem_range.mp hr
  calc
    _ ≤ ((C (5 : K)⁻¹ * (X + 1)) ^ ((p - 1) / 2 + r + 1) *
        (4 * X - 11) ^ (2 * r + 1) : K[X]).natDegree := by
      rw [mul_assoc]
      exact natDegree_C_mul_le _ _
    _ ≤ ((p - 1) / 2 + r + 1) * 1 + (2 * r + 1) * 1 :=
      natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_pow_le_of_le _ hs) (natDegree_pow_le_of_le _ hb))
    _ ≤ 2 * p - 3 := by omega

theorem HJP_conic_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x t : K) (ht : t ^ 2 = (x + 1) / 5) :
    (HJP p).eval x = t ^ p * WPFiniteNC122.J_L p (t * (4 * x - 11) / 5) := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  rw [J_L_harmonic p hp, Finset.mul_sum]
  unfold HJP
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one, eval_sub, eval_ofNat]
  rw [mul_comm (5 : K)⁻¹ (x + 1), ← div_eq_mul_inv]
  have hrow : (t * (4 * x - 11) / 5) ^ (2 * r + 1) =
      t ^ (2 * r + 1) * (4 * x - 11) ^ (2 * r + 1) / (5 : K) ^ (2 * r + 1) := by
    rw [div_pow, mul_pow]
  rw [hrow]
  calc
    _ = ((WPFiniteNC122.q p + H r / 2) / ((2 * r + 1 : ℕ) : K)) /
        (5 : K) ^ (2 * r + 1) * (t ^ 2) ^ ((p - 1) / 2 + r + 1) *
          (4 * x - 11) ^ (2 * r + 1) := by rw [ht]
    _ = _ := by
      rw [← pow_mul, show 2 * ((p - 1) / 2 + r + 1) = p + (2 * r + 1) by omega,
        pow_add]
      ring

theorem J_L_normalized_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteNC122.J_L p (1 : K) = 0 ∧ WPFiniteNC122.J_L p (-1 : K) = 0 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hR1 : WPFiniteField.R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
  have hR0 : WPFiniteField.R p (0 : K) = 0 := by
    unfold WPFiniteField.R
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).1
    simp only [zero_pow (by omega : j ≠ 0), zero_div]
  unfold WPFiniteNC122.J_L
  simp only [show (1 + 1 : K) = 2 by ring, div_self htwo, sub_self,
    show (1 - (-1) : K) = 2 by ring, show (1 + (-1) : K) = 0 by ring,
    zero_div, hR0, hR1]
  exact ⟨trivial, trivial⟩

theorem HJP_original_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (HJP p : K[X]).eval 4 = 0 ∧ (HJP p : K[X]).eval (1 / 4) = 0 := by
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hb : (1 : K) ^ 2 = (4 + 1) / 5 := by field_simp [hfive]; ring
  have ha : (1 / 2 : K) ^ 2 = (1 / 4 + 1) / 5 := by
    field_simp [htwo, hfour, hfive]
    ring
  have heB := HJP_conic_eval p hp (4 : K) 1 hb
  have heA := HJP_conic_eval p hp (1 / 4 : K) (1 / 2) ha
  have hTB : (1 * (4 * 4 - 11) / 5 : K) = 1 := by field_simp [hfive]; ring
  have hTA : ((1 / 2) * (4 * (1 / 4) - 11) / 5 : K) = -1 := by
    field_simp [htwo, hfour, hfive]
    ring
  rw [hTB, (J_L_normalized_ends p hp).1, mul_zero] at heB
  rw [hTA, (J_L_normalized_ends p hp).2, mul_zero] at heA
  exact ⟨heB, heA⟩

theorem HJP_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (HJP p).eval 0 = WPFiniteNC122.h0J p u := by
  have he := HJP_conic_eval p hp (0 : K) u (by simpa using hu)
  unfold WPFiniteNC122.h0J WPFiniteNC122.T0
  rw [show (u * (4 * 0 - 11) / 5 : K) = -11 * u / 5 by ring] at he
  exact he

end WPFiniteJSource
