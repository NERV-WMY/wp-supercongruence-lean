import WPFiniteJSource

open scoped BigOperators Polynomial
open Polynomial WPFiniteKSource WPFiniteAffineLog WPFiniteJSource

namespace WPFieldAssembly.ActualFiniteA2

set_option maxHeartbeats 1400000

variable {K : Type*} [Field K]

/-- The entire even weight-two polynomial, with its actual harmonic coefficients. -/
noncomputable def harmonicPrimitive (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
    C ((H (2 * j - 1) : K) / ((2 * j : ℕ) : K)) * X ^ (2 * j)

noncomputable def dilogPrimitive (p : ℕ) : K[X] :=
  -C (2 : K)⁻¹ * ((RP p).comp (1 - X) + (RP p).comp (1 + X))

private theorem H_succ (n : ℕ) :
    (H (n + 1) : K) = H n + ((n + 1 : ℕ) : K)⁻¹ := by
  unfold H
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]

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

theorem OP_half_cutoff (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (OP p : K[X]) =
      ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        C (((2 * j - 1 : ℕ) : K)⁻¹) * X ^ (2 * j - 1) := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
    change C (2 : K)⁻¹ * C (2 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h2, C_1]
  have he : (OP p : K[X]) = LP p - EP p := by
    unfold OP EP
    linear_combination (LP p) * hc
  rw [he, EP_half_cutoff p hp]
  have hl : (LP p : K[X]) =
      (∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        C (((2 * j : ℕ) : K)⁻¹) * X ^ (2 * j)) +
      ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        C (((2 * j - 1 : ℕ) : K)⁻¹) * X ^ (2 * j - 1) := by
    unfold LP
    rw [hpn, sum_full_pairs]
    rw [show (2 * ((p - 1) / 2) + 1 - 1) / 2 = (p - 1) / 2 by omega]
  rw [hl]
  ring

/-- Telescoping keeps the complete final harmonic boundary. -/
private theorem harmonic_cleared (n : ℕ) :
    (1 - X ^ 2 : K[X]) *
      (∑ j ∈ Finset.Ico 1 (n + 1), C (H (2 * j - 1)) * X ^ (2 * j - 1)) =
      (∑ j ∈ Finset.Ico 1 (n + 1), C (((2 * j - 1 : ℕ) : K)⁻¹) *
        X ^ (2 * j - 1)) +
      X * (∑ j ∈ Finset.Ico 1 (n + 1), C (((2 * j : ℕ) : K)⁻¹) *
        X ^ (2 * j)) -
      C (H (2 * n)) * X ^ (2 * n + 1) := by
  induction n with
  | zero => simp [H]
  | succ n ih =>
    simp only [Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega)]
    rw [mul_add, ih]
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      ]
    simp only [H_succ, map_add]
    rw [show (2 * n + 1 + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add,
      show 2 * n + 1 + 1 = (2 * n + 1) + 1 by omega, pow_succ]
    ring

theorem harmonicPrimitive_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (harmonicPrimitive p : K[X]).derivative =
      ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        C (H (2 * j - 1)) * X ^ (2 * j - 1) := by
  have hpn : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  unfold harmonicPrimitive
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hd : ((2 * j : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p
    (2 * j) (Finset.mem_Ico.mpr (by omega))
  rw [derivative_C_mul_X_pow, div_mul_cancel₀ _ hd]

private theorem H_full_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (H (p - 1) : K) = 0 := by
  have he := congrArg (fun P : K[X] => P.eval 0) (LP_reflection (K := K) p hp)
  have hz : (LP p : K[X]).eval 0 = 0 := by
    unfold LP
    rw [eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjpos := (Finset.mem_Ico.mp hj).1
    simp only [eval_mul, eval_C, eval_pow, eval_X,
      zero_pow (by omega : j ≠ 0), mul_zero]
  simp only [eval_comp, eval_sub, eval_one, eval_X, sub_zero, hz] at he
  have hv : (LP p : K[X]).eval 1 = H (p - 1) := by
    simp only [LP, H, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      one_pow, mul_one, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [hv] at he
  exact he

theorem harmonicPrimitive_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (harmonicPrimitive p).derivative =
      OP p + X * EP p := by
  have hpn : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  rw [harmonicPrimitive_derivative p hp, harmonic_cleared,
    hpn, H_full_zero p hp, map_zero, zero_mul, sub_zero,
    ← OP_half_cutoff p hp, ← EP_half_cutoff p hp]

theorem dilogPrimitive_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (dilogPrimitive p).derivative =
      OP p + X * EP p := by
  have hm := RP_comp_derivative (K := K) p (1 - X)
  have ha := RP_comp_derivative (K := K) p (1 + X)
  simp only [derivative_sub, derivative_one, derivative_X, zero_sub,
    derivative_add, zero_add, LP_reflection p hp, LP_plus_reflection p hp,
    mul_neg, mul_one] at hm ha
  unfold dilogPrimitive OP EP
  simp only [derivative_mul, derivative_neg, derivative_C, neg_zero,
    zero_mul, zero_add, derivative_add]
  linear_combination
    -C (2 : K)⁻¹ * ((1 + X) * hm + (1 - X) * ha)

theorem harmonicPrimitive_natDegree_le (p : ℕ) :
    (harmonicPrimitive p : K[X]).natDegree ≤ p - 1 := by
  unfold harmonicPrimitive
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  calc
    _ ≤ (X ^ (2 * j) : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ 2 * j := by simp
    _ ≤ p - 1 := by
      have hh := Nat.div_mul_le_self (p - 1) 2
      omega

theorem dilogPrimitive_natDegree_le (p : ℕ) :
    (dilogPrimitive p : K[X]).natDegree ≤ p - 1 := by
  have hd (U : K[X]) (hU : U.natDegree ≤ 1) :
      ((RP p : K[X]).comp U).natDegree ≤ p - 1 := by
    calc
      _ ≤ (RP p : K[X]).natDegree * U.natDegree := natDegree_comp_le
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul (RP_natDegree_le p) hU
      _ = p - 1 := by simp
  have hm : (1 - X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have ha : (1 + X : K[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp)
  rw [dilogPrimitive, neg_mul]
  exact (by rw [natDegree_neg]; exact
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans
      (max_le (hd _ hm) (hd _ ha))))

private theorem zero_of_derivative_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree < p) (hder : Q.derivative = 0)
    (hz : Q.eval 0 = 0) : Q = 0 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_eval_zero, eval_zero] using hz
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
  have he : Q.coeff n * (n : K) = 0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (n - 1)) hder
    simpa only [coeff_derivative, ← Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p n
    (Finset.mem_Ico.mpr (by omega)))

/-- The harmonic polynomial is the literal even finite dilogarithm. -/
theorem actual_even_dilog_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (harmonicPrimitive p : K[X]) = dilogPrimitive p := by
  have hdeg : ((harmonicPrimitive p : K[X]) - dilogPrimitive p).natDegree < p := by
    have hd := (natDegree_sub_le _ _).trans
      (max_le (harmonicPrimitive_natDegree_le (K := K) p)
        (dilogPrimitive_natDegree_le (K := K) p))
    have hp0 := (Fact.out : p.Prime).pos
    omega
  have hf : (1 - X ^ 2 : K[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun P : K[X] => P.coeff 2) he
    have h1 : (1 : K[X]).coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by simp)
    rw [coeff_sub, h1, coeff_X_pow, if_pos rfl, coeff_zero, zero_sub] at hc
    exact (neg_ne_zero.mpr one_ne_zero) hc
  have hder : ((harmonicPrimitive p : K[X]) - dilogPrimitive p).derivative = 0 := by
    have he : (1 - X ^ 2 : K[X]) *
        ((harmonicPrimitive p : K[X]) - dilogPrimitive p).derivative = 0 := by
      rw [derivative_sub, mul_sub, harmonicPrimitive_cleared_derivative p hp,
        dilogPrimitive_cleared_derivative p hp, sub_self]
    exact (mul_eq_zero.mp he).resolve_left hf
  have hz : ((harmonicPrimitive p : K[X]) - dilogPrimitive p).eval 0 = 0 := by
    have hH : (harmonicPrimitive p : K[X]).eval 0 = 0 := by
      unfold harmonicPrimitive
      rw [eval_finsetSum]
      apply Finset.sum_eq_zero
      intro j hj
      have hjpos := (Finset.mem_Ico.mp hj).1
      simp only [eval_mul, eval_C, eval_pow, eval_X,
        zero_pow (by omega : 2 * j ≠ 0), mul_zero]
    have hR : WPFiniteField.R p (1 : K) = 0 := by
      have he := congrArg (ZMod.castHom (dvd_refl p) K)
        (WPFiniteInversion.R_one_eq_zero p (by omega))
      simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using he
    simp only [eval_sub, hH, dilogPrimitive, eval_mul, eval_neg, eval_C,
      eval_add, eval_comp, eval_one, eval_X, sub_zero, add_zero, RP_eval, hR,
      mul_zero, sub_zero]
  exact sub_eq_zero.mp (zero_of_derivative_degree p _ hdeg hder hz)

theorem actual_even_dilog_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (harmonicPrimitive p : K[X]).eval z = WPFiniteNC122.Aeven p z := by
  rw [actual_even_dilog_polynomial p hp]
  simp only [dilogPrimitive, WPFiniteNC122.Aeven, eval_mul, eval_neg, eval_C,
    eval_add, eval_comp, eval_sub, eval_one, eval_X, RP_eval, div_eq_mul_inv]
  ring

end WPFieldAssembly.ActualFiniteA2

