import WPActualFinalConsumer

open scoped BigOperators
open Polynomial

namespace WPFiniteAffineLog

variable {K : Type*} [Field K]

noncomputable def LP (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p, C ((j : K)⁻¹) * X ^ j

private theorem LP_eval (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (LP p).eval x = WPFiniteField.ell p x := by
  simp only [LP, WPFiniteField.ell, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem LP_degree (p : ℕ) : (LP p : K[X]).natDegree ≤ p - 1 := by
  unfold LP
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).2
  calc
    _ ≤ (X ^ j : K[X]).natDegree := natDegree_C_mul_le _ _
    _ ≤ j := by simp
    _ ≤ p - 1 := by omega

private theorem LP_derivative (p : ℕ) [Fact p.Prime] [CharP K p] :
    (LP p : K[X]).derivative = ∑ j ∈ Finset.range (p - 1), (X : K[X]) ^ j := by
  unfold LP
  rw [derivative_sum]
  have ht : (∑ j ∈ Finset.Ico 1 p, (C ((j : K)⁻¹) * X ^ j).derivative) =
      ∑ j ∈ Finset.Ico 1 p, (X : K[X]) ^ (j - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [derivative_C_mul_X_pow,
      inv_mul_cancel₀ (WPFiniteField.denominator_ne_zero p j hj), C_1, one_mul]
  rw [ht, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  omega

private theorem LP_derivative_closed (p : ℕ) [Fact p.Prime] [CharP K p] :
    (LP p : K[X]).derivative = (1 - X) ^ (p - 1) - X ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hnz : (1 - X : K[X]) ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa using (X_ne_C (1 : K)).symm
  have hg : (∑ j ∈ Finset.range p, (X : K[X]) ^ j) = (1 - X) ^ (p - 1) := by
    apply mul_right_cancel₀ hnz
    rw [geom_sum_mul_neg, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    simpa using (sub_pow_char (1 : K[X]) X (p := p)).symm
  rw [LP_derivative]
  have he : (∑ j ∈ Finset.range (p - 1), (X : K[X]) ^ j) + X ^ (p - 1) =
      (1 - X : K[X]) ^ (p - 1) := by
    rw [← Finset.sum_range_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact hg
  linear_combination he

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

private theorem affine_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ((LP p : K[X]).comp (C (2 : K)⁻¹ * (1 + X))).derivative =
      C (2 : K)⁻¹ * ((1 - X) ^ (p - 1) - (1 + X) ^ (p - 1)) := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hsum : (1 - C (2 : K)⁻¹ * (1 + X) : K[X]) = C (2 : K)⁻¹ * (1 - X) := by
    have he : (C (2 : K)⁻¹ : K[X]) * 2 = 1 := by
      change C (2 : K)⁻¹ * C (2 : K) = 1
      rw [← C_mul, inv_mul_cancel₀ htwo, C_1]
    linear_combination -he
  have hc : (C (2 : K)⁻¹ : K[X]) ^ (p - 1) * C (2 : K)⁻¹ = C (2 : K)⁻¹ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), ← C_pow, inv_pow, h2pow]
  rw [derivative_comp, LP_derivative_closed]
  simp only [sub_comp, pow_comp, one_comp, X_comp, derivative_mul, derivative_C,
    zero_mul, zero_add, derivative_add, derivative_one, derivative_X, mul_one]
  rw [hsum, mul_pow, mul_pow]
  calc
    _ = ((C (2 : K)⁻¹ : K[X]) ^ (p - 1) * C (2 : K)⁻¹) *
        ((1 - X) ^ (p - 1) - (1 + X) ^ (p - 1)) := by ring
    _ = _ := by rw [hc]

private theorem even_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (C (2 : K)⁻¹ * ((LP p : K[X]) + (LP p).comp (-X))).derivative =
      C (2 : K)⁻¹ * ((1 - X) ^ (p - 1) - (1 + X) ^ (p - 1)) := by
  have hpred : Even (p - 1) := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨n, by omega⟩
  rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
    derivative_comp, derivative_neg, derivative_X, LP_derivative_closed]
  simp only [sub_comp, pow_comp, one_comp, X_comp, sub_neg_eq_add]
  rw [hpred.neg_pow]
  ring

theorem affine_log_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LP p : K[X]).comp (C (2 : K)⁻¹ * (1 + X)) =
      C (WPFiniteInversion.integerFermatQuotient p 2 : K) +
        C (2 : K)⁻¹ * ((LP p) + (LP p).comp (-X)) := by
  let Q : K[X] := (LP p).comp (C (2 : K)⁻¹ * (1 + X)) -
    C (2 : K)⁻¹ * ((LP p) + (LP p).comp (-X)) -
      C (WPFiniteInversion.integerFermatQuotient p 2 : K)
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have haffdeg : (C (2 : K)⁻¹ * (1 + X) : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hmdeg : (-X : K[X]).natDegree ≤ 1 := by simp
  have hcomp : ((LP p : K[X]).comp (C (2 : K)⁻¹ * (1 + X))).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans (by nlinarith [LP_degree (K := K) p])
  have hnegcomp : ((LP p : K[X]).comp (-X)).natDegree ≤ p - 1 :=
    natDegree_comp_le.trans (by nlinarith [LP_degree (K := K) p])
  have hevendeg : (C (2 : K)⁻¹ * ((LP p : K[X]) + (LP p).comp (-X))).natDegree ≤ p - 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le (LP_degree p) hnegcomp))
  have hdeg : Q.natDegree < p := by
    dsimp only [Q]
    have hd := (natDegree_sub_le _ _).trans
      (max_le ((natDegree_sub_le _ _).trans (max_le hcomp hevendeg))
        (by simp : (C (WPFiniteInversion.integerFermatQuotient p 2 : K)).natDegree ≤ p - 1))
    omega
  have hder : Q.derivative = 0 := by
    dsimp only [Q]
    rw [derivative_sub, derivative_sub, derivative_C, affine_derivative p hp,
      even_derivative p hp, sub_self, sub_self]
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hhalf := WPFiniteField.ell_inversion p (2 : K) htwo
  rw [h2pow, WPFiniteLoop.ell_two p hp] at hhalf
  have hzero : WPFiniteField.ell p (0 : K) = 0 := by
    unfold WPFiniteField.ell
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).1
    simp only [zero_pow (by omega : j ≠ 0), zero_div]
  have hqzero : Q.eval 0 = 0 := by
    dsimp only [Q]
    simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_add, eval_one, eval_X,
      eval_neg, neg_zero, add_zero, mul_one, LP_eval, hzero, hhalf]
    field_simp [htwo]
    ring
  have hz := zero_of_derivative_degree p Q hdeg hder hqzero
  dsimp only [Q] at hz
  linear_combination hz

theorem ell_affine_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    WPFiniteField.ell p ((1 + t) / 2) =
      (WPFiniteInversion.integerFermatQuotient p 2 : K) + WPFiniteField.E p t := by
  have he := congrArg (fun P : K[X] => P.eval t) (affine_log_polynomial (K := K) p hp)
  simp only [eval_comp, eval_mul, eval_C, eval_add, eval_one, eval_X,
    eval_neg, LP_eval] at he
  unfold WPFiniteField.E
  simp only [div_eq_mul_inv]
  rw [mul_comm (1 + t) (2 : K)⁻¹]
  linear_combination he

theorem LP_eval_eq (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (LP p).eval x = WPFiniteField.ell p x := LP_eval p x

theorem LP_natDegree_le (p : ℕ) : (LP p : K[X]).natDegree ≤ p - 1 := LP_degree p

theorem LP_derivative_closed_eq (p : ℕ) [Fact p.Prime] [CharP K p] :
    (LP p : K[X]).derivative = (1 - X) ^ (p - 1) - X ^ (p - 1) := LP_derivative_closed p

end WPFiniteAffineLog

namespace WPFiniteNC122

open WPFiniteField

variable {K : Type*} [Field K]

def q (p : ℕ) : K := WPFiniteInversion.integerFermatQuotient p 2

def h (p : ℕ) : K := -2 * q p - 3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 2

def L (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K := q p + E p t

def J_L (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (R p ((1 + t) / 2) - R p ((1 - t) / 2)) / 2

def S2 (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  R p ((1 - t) / 2) + R p ((1 + t) / 2)

def Aeven (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  -(R p (1 - t) + R p (1 + t)) / 2

def Ksrc (p : ℕ) [Fact p.Prime] [CharP K p] (c t : K) : K :=
  (R p (1 - t) + R p (1 + t) + (q p) ^ 2) / 2 - S2 p t / 6 +
    (2 * c / 3 - q p) * L p t

theorem S2_quadratic_identity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    S2 p t = -(L p t) ^ 2 - 2 * t ^ p * J_L p t := by
  have htwo : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 2)
  have harg : (1 - (1 + t) / 2 : K) = (1 - t) / 2 := by field_simp [htwo]; ring
  have ha : ((1 + t) / 2) ^ p = (1 + t ^ p) / (2 : K) := by
    rw [div_pow, add_pow_char (p := p), one_pow, h2pow]
  have hb : ((1 - t) / 2) ^ p = (1 - t ^ p) / (2 : K) := by
    rw [div_pow, sub_pow_char (p := p), one_pow, h2pow]
  have he := R_weight_two_reflection p (by omega : 5 ≤ p) ((1 + t) / 2)
  rw [harg, ha, hb, WPFiniteAffineLog.ell_affine_half p hp t] at he
  unfold S2 L q J_L
  linear_combination 2 * he -
    (R p ((1 + t) / 2) + R p ((1 - t) / 2) +
      ((WPFiniteInversion.integerFermatQuotient p 2 : K) + E p t) ^ 2) *
        (inv_mul_cancel₀ htwo)

theorem Ksrc_quadratic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c t : K) :
    Ksrc p c t = -Aeven p t + (q p) ^ 2 / 2 + (L p t) ^ 2 / 6 +
      t ^ p * J_L p t / 3 + (2 * c / 3 - q p) * L p t := by
  have htwo : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hthree : (3 : K) ≠ 0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hsix : (6 : K) ≠ 0 := denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  unfold Ksrc Aeven
  rw [S2_quadratic_identity p hp t]
  field_simp [htwo, hthree, hsix]
  ring

theorem Ksrc_normalized_end (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (c : K) :
    Ksrc p c (1 : K) = 0 ∧ Ksrc p c (-1 : K) = 0 := by
  have htwo : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hzero : R p (0 : K) = 0 := by
    unfold R
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).1
    simp only [zero_pow (by omega : j ≠ 0), zero_div]
  have hone : R p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← R_castHom, map_one, map_zero] using he
  have hR2 : R p (2 : K) = -(q p) ^ 2 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_two_eq_fermat p hp)
    simpa only [← R_castHom, map_ofNat, map_neg, map_pow, map_intCast, q] using he
  have hE1 : E p (1 : K) = -q p := by
    have he := (WPFiniteLoop.L_rational_ends (K := K) p hp).1
    have he2 := WPFiniteLoop.L_square_eq_twice_E p hp (1 : K)
    rw [one_pow] at he2
    rw [he2] at he
    apply mul_left_cancel₀ htwo
    simpa only [q, mul_neg, neg_mul] using he
  have hEneg : E p (-1 : K) = E p (1 : K) := by
    unfold E
    simp only [neg_neg]
    ring
  unfold Ksrc S2 L
  simp only [sub_self, zero_div, add_neg_cancel, sub_neg_eq_add,
    show (1 + 1 : K) = 2 by ring, div_self htwo, hzero, hone, hR2, hEneg, hE1,
    mul_zero, zero_add, add_zero]
  constructor <;> ring

def T0 (u : K) : K := -11 * u / 5

def a0 (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K := L p (T0 u) - h p

def h0J (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K := u ^ p * J_L p (T0 u)

def G_KQ (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  -2 * Ksrc p (h p) (T0 u) - (a0 p u) ^ 2 + (h p) ^ 2

private theorem L_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (x : ZMod p) :
    WPFiniteLoop.L ((p - 1) / 2) (ZMod.castHom (dvd_refl p) K x) =
      ZMod.castHom (dvd_refl p) K (WPFiniteLoop.L ((p - 1) / 2) x) := by
  simp only [WPFiniteLoop.L, map_sum, map_div₀, map_pow, map_natCast]

private def a0base (p : ℕ) [Fact p.Prime] : ZMod p :=
  q p + WPFiniteLoop.L ((p - 1) / 2) (121 / 125 : ZMod p) / 2 - h p

private theorem a0_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) : a0 p u = ZMod.castHom (dvd_refl p) K (a0base p) := by
  have htwo : (2 : K) ≠ 0 := denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by rw [show (25 : K) = 5 ^ 2 by ring]; exact pow_ne_zero _ hfive
  have h125 : (125 : K) ≠ 0 := by rw [show (125 : K) = 5 ^ 3 by ring]; exact pow_ne_zero _ hfive
  have hsq : (T0 u) ^ 2 = (121 / 125 : K) := by
    unfold T0
    rw [div_pow, mul_pow, hu]
    field_simp [hfive, h25, h125]
    ring
  have he : E p (T0 u) = WPFiniteLoop.L ((p - 1) / 2) (121 / 125 : K) / 2 := by
    apply (eq_div_iff htwo).mpr
    rw [mul_comm, ← WPFiniteLoop.L_square_eq_twice_E p hp (T0 u), hsq]
  unfold a0 L a0base h q
  rw [he]
  simp only [map_sub, map_add, map_mul, map_div₀, map_intCast, map_ofNat,
    map_neg, ← L_castHom]

theorem original_corrected_endpoint (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    G_KQ p u = 2 * Aeven p (T0 u) - 4 * (a0 p u) ^ 2 / 3 +
      2 * (q p - h p) * a0 p u - 2 * (h p) ^ 2 / 3 + 2 * q p * h p - (q p) ^ 2 +
        22 * h0J p u / 15 := by
  have hthree : (3 : K) ≠ 0 := denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := denominator_ne_zero p 15 (Finset.mem_Ico.mpr (by omega))
  have he := WPFinalEndpointAlgebra.original_source_constant p hp (a0base p)
    (h p) (q p) 0 0
  have hm := congrArg (ZMod.castHom (dvd_refl p) K) he
  simp only [map_sub, map_add, map_mul, map_div₀, map_pow, map_intCast, map_ofNat,
    map_neg, map_zero, q, h, ← a0_castHom p hp u hu] at hm
  have hTpow : (T0 u) ^ p = -11 * u ^ p / 5 := by
    have h5 : (5 : K) ^ p = 5 := by
      simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
    have h11 : (11 : K) ^ p = 11 := by
      simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 11)
    unfold T0
    rw [div_pow, mul_pow, (Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow,
      h5, h11]
  have hphase : -2 * ((T0 u) ^ p * J_L p (T0 u)) / 3 = 22 * h0J p u / 15 := by
    rw [hTpow]
    unfold h0J
    field_simp [hthree, hfive, h15]
    ring
  have hraw : G_KQ p u = 2 * Aeven p (T0 u) - 4 * (a0 p u) ^ 2 / 3 +
      2 * (q p - h p) * a0 p u - 2 * (h p) ^ 2 / 3 + 2 * q p * h p - (q p) ^ 2 -
        2 * ((T0 u) ^ p * J_L p (T0 u)) / 3 := by
    unfold G_KQ
    rw [Ksrc_quadratic p hp]
    have hL : L p (T0 u) = a0 p u + h p := by unfold a0; ring
    rw [hL]
    dsimp only [q, h] at hm ⊢
    linear_combination hm
  rw [hraw]
  linear_combination hphase

end WPFiniteNC122
