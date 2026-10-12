import WPFieldAssembly.ActualCauchyMoment
import WPFieldAssembly.ActualJointGreen
import WPFiniteJSource

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPFiniteCarry WPActualRankTwoHatLift
  WPActualRankTwoParameter WPActualRankTwoLegendreField WPActualRankTwoLowTaylor
  WPActualGaussBottom WPActualGaussProper
  WPActualEvenLogCarry WPActualRankTwoCarrySource
  WPFieldAssembly.ActualCauchyMoment WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.ActualDeltaUNextSource WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualJointGreen WPFiniteKSource WPFiniteAffineLog

namespace WPFieldAssembly.ActualCauchyTbarAttachment

private theorem H_eq_fieldHarmonic (p n : ℕ) [Fact p.Prime] :
    (WPFiniteJSource.H n : ZMod p) = fieldHarmonic p n := by
  unfold WPFiniteJSource.H fieldHarmonic
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  omega

private theorem H_succ {K : Type*} [Field K] (n : ℕ) :
    (WPFiniteJSource.H (n + 1) : K) =
      WPFiniteJSource.H n + ((n + 1 : ℕ) : K)⁻¹ := by
  unfold WPFiniteJSource.H
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]

/-- The exact finite telescoping identity used in the literal second coefficient. -/
private theorem harmonic_geometric {K : Type*} [Field K] (n : ℕ) (a : K) :
    (1 - X ^ 2 : K[X]) *
      (∑ r ∈ Finset.range n, C (a + WPFiniteJSource.H r / 2) * X ^ (2 * r)) =
      C a + (∑ j ∈ Finset.Ico 1 (n + 1),
        C (((2 * j : ℕ) : K)⁻¹) * X ^ (2 * j)) -
      C (a + WPFiniteJSource.H n / 2) * X ^ (2 * n) := by
  induction n with
  | zero => simp [WPFiniteJSource.H]
  | succ n ih =>
      rw [Finset.sum_range_succ,
        Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
      rw [mul_add, ih, H_succ]
      simp only [Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev, div_eq_mul_inv,
        map_add, map_mul]
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      ring

private theorem even_geometric {K : Type*} [CommRing K] (N : ℕ) :
    (1 - X ^ 2 : K[X]) *
      (∑ r ∈ Finset.range N, X ^ (2 * (r + 1))) =
      X ^ 2 - X ^ (2 * (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [show 2 * (N + 1 + 1) = 2 * (N + 1) + 2 by omega, pow_add]
      ring

noncomputable def V2field (p : ℕ) [Fact p.Prime] (h : ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ Finset.range ((p - 1) / 2),
    C ((1 / 2 : ZMod p) ^ 2 * (((r + 1 : ℕ) : ZMod p)⁻¹) ^ 2 +
      (1 / 6 : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹ *
        ((WPFiniteNC122.q p : ZMod p) - h) +
      (1 / 6 : ZMod p) * (1 / 2 : ZMod p) *
        ((r + 1 : ℕ) : ZMod p)⁻¹ * WPFiniteJSource.H r) *
      X ^ (2 * (r + 1))

theorem universalPolynomialIntegral_field (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (universalPolynomialIntegral p hp).map (residueHom p) =
      V2field p (fieldHarmonic p (p / 6)) := by
  simp only [universalPolynomialIntegral, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    V2field]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  simp only [universalCoefficient, map_add, map_sub, map_mul, map_pow,
    map_intCast, cauchyHalf_field, integralSixth_field,
    smallIntegralInverse_field p (r + 1) (by omega) (by omega),
    integralHarmonic_field p (p / 6) (by omega),
    integralHarmonic_field p r (by omega), Nat.add_sub_cancel]
  rw [H_eq_fieldHarmonic]
  rfl

private theorem EP_range (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (EP p : (ZMod p)[X]) = ∑ r ∈ Finset.range ((p - 1) / 2),
      C ((1 / 2 : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹) * X ^ (2 * (r + 1)) := by
  rw [WPFiniteJSource.EP_half_cutoff p hp, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro r hr
  have he : ((2 * (1 + r) : ℕ) : ZMod p) =
      (2 : ZMod p) * ((r + 1 : ℕ) : ZMod p) := by push_cast; ring
  rw [he, mul_inv_rev]
  have hn : 1 + r = r + 1 := by omega
  rw [hn]
  simp only [one_div]
  ring

private theorem V2field_X_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) :
    X * (V2field p h).derivative = EP p +
      C (((WPFiniteNC122.q p : ZMod p) - h) / 3) *
        (∑ r ∈ Finset.range ((p - 1) / 2), X ^ (2 * (r + 1))) +
      C (1 / 6 : ZMod p) *
        (∑ r ∈ Finset.range ((p - 1) / 2),
          C (WPFiniteJSource.H r) * X ^ (2 * (r + 1))) := by
  rw [V2field, derivative_sum, Finset.mul_sum, EP_range p hp,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  have hu : ((r + 1 : ℕ) : ZMod p) ≠ 0 :=
    small_cast_ne_zero p (r + 1) (by omega) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  rw [derivative_C_mul_X_pow]
  have hx : (X : (ZMod p)[X]) * X ^ (2 * (r + 1) - 1) = X ^ (2 * (r + 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * (r + 1))]
  rw [show X * (C _ * X ^ (2 * (r + 1) - 1)) =
    C _ * (X * X ^ (2 * (r + 1) - 1)) by ring, hx]
  have hc :
      ((1 / 2 : ZMod p) ^ 2 * (((r + 1 : ℕ) : ZMod p)⁻¹) ^ 2 +
        (1 / 6 : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹ *
          ((WPFiniteNC122.q p : ZMod p) - h) +
        (1 / 6 : ZMod p) * (1 / 2 : ZMod p) *
          ((r + 1 : ℕ) : ZMod p)⁻¹ * WPFiniteJSource.H r) *
          ((2 * (r + 1) : ℕ) : ZMod p) =
        (1 / 2 : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹ +
          ((WPFiniteNC122.q p : ZMod p) - h) / 3 +
          WPFiniteJSource.H r / 6 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hu, h2, h3, h6]
    ring
  rw [hc]
  simp only [map_add, map_mul, map_one, div_eq_mul_inv]
  ring

private theorem harmonic_even_source (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (1 - X ^ 2 : (ZMod p)[X]) *
      (∑ r ∈ Finset.range ((p - 1) / 2),
        C (WPFiniteJSource.H r) * X ^ (2 * (r + 1))) =
      2 * X ^ 2 * EP p -
        C (WPFiniteJSource.H ((p - 1) / 2)) *
          X ^ (2 * (((p - 1) / 2) + 1)) := by
  let N := (p - 1) / 2
  let S : (ZMod p)[X] :=
    ∑ r ∈ Finset.range N, C (WPFiniteJSource.H r / 2) * X ^ (2 * r)
  have hg := harmonic_geometric (K := ZMod p) N 0
  simp only [zero_add, C_0] at hg
  rw [← WPFiniteJSource.EP_half_cutoff p hp] at hg
  change (1 - X ^ 2 : (ZMod p)[X]) * S =
    EP p - C (WPFiniteJSource.H N / 2) * X ^ (2 * N) at hg
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hc : (2 : (ZMod p)[X]) * C (WPFiniteJSource.H N / 2) =
      C (WPFiniteJSource.H N) := by
    change C (2 : ZMod p) * C (WPFiniteJSource.H N / 2) = _
    rw [← C_mul]
    congr 1
    field_simp [h2]
  have hl : (∑ r ∈ Finset.range N,
      C (WPFiniteJSource.H r) * (X : (ZMod p)[X]) ^ (2 * (r + 1))) =
      2 * X ^ 2 * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hcr : (2 : (ZMod p)[X]) * C (WPFiniteJSource.H r / 2) =
        C (WPFiniteJSource.H r) := by
      change C (2 : ZMod p) * C (WPFiniteJSource.H r / 2) = _
      rw [← C_mul]
      congr 1
      field_simp [h2]
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    linear_combination -(X ^ (2 * r) * X ^ 2) * hcr
  change (1 - X ^ 2 : (ZMod p)[X]) * (∑ r ∈ Finset.range N, _) = _
  rw [hl]
  have hpw : (X : (ZMod p)[X]) ^ (2 * (N + 1)) =
      X ^ 2 * X ^ (2 * N) := by
    rw [show 2 * (N + 1) = 2 + 2 * N by omega, pow_add]
  rw [hpw]
  linear_combination (2 * X ^ 2) * hg - (X ^ 2 * X ^ (2 * N)) * hc

/-- Actual universal second coefficient has the exact unseen-slot source. -/
theorem V2field_cleared_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) :
    (1 - X ^ 2) * X * (V2field p h).derivative =
      (1 - X ^ 2) * EP p + C (1 / 3 : ZMod p) * X ^ 2 * (LPsrc p - C h) +
        C (h / 3) * X ^ (p + 1) := by
  have hd := V2field_X_derivative p hp h
  have hg := even_geometric (K := ZMod p) ((p - 1) / 2)
  have hh := harmonic_even_source p hp
  have hn : 2 * (((p - 1) / 2) + 1) = p + 1 := by
    have he := prime_half_identity p (by omega : 7 ≤ p)
    omega
  rw [hn] at hg hh
  rw [WPFiniteJSource.H_half_eq_quotient p hp] at hh
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  have h23 : (2 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p) := by
    change C (2 : ZMod p) * C (1 / 6 : ZMod p) = _
    rw [← C_mul]
    congr 1
    field_simp [h3, h6]
    ring
  unfold LPsrc
  linear_combination (norm := (simp [div_eq_mul_inv, map_ofNat]; ring))
    (1 - X ^ 2) * hd +
    C (((WPFiniteNC122.q p : ZMod p) - h) / 3) * hg +
    C (1 / 6 : ZMod p) * hh +
    (X ^ 2 * EP p + C (WPFiniteNC122.q p : ZMod p) * X ^ (p + 1)) * h23

private theorem even_RP_X_derivative (p : ℕ) [Fact p.Prime] :
    X * (C ((2 : ZMod p)⁻¹) * (RP p + (RP p).comp (-X))).derivative = EP p := by
  have h0 := X_mul_derivative_RP (K := ZMod p) p
  have h1 := RP_comp_derivative (K := ZMod p) p (-X : (ZMod p)[X])
  simp only [derivative_neg, derivative_X] at h1
  simp only [derivative_C_mul, derivative_add, EP]
  linear_combination C ((2 : ZMod p)⁻¹) * h0 - C ((2 : ZMod p)⁻¹) * h1

/-- This source uses the saved literal RP/S2P/LPsrc Tbar. -/
theorem literal_Tbar_cleared_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) :
    (1 - X ^ 2) * X * (universalTbarP p h).derivative =
      (1 - X ^ 2) * EP p + C (1 / 3 : ZMod p) * X ^ 2 * (LPsrc p - C h) +
        C (h / 3) * X ^ (p + 1) := by
  have hr := even_RP_X_derivative p
  have hs := S2P_cleared_derivative (K := ZMod p) p hp
  have hl := LPsrc_cleared_derivative (K := ZMod p) p hp
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  have h23 : (2 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p) := by
    change C (2 : ZMod p) * C (1 / 6 : ZMod p) = _
    rw [← C_mul]
    congr 1
    field_simp [h3, h6]
    ring
  unfold universalTbarP
  simp only [derivative_sub, derivative_C_mul] at hr ⊢
  rw [show (X : (ZMod p)[X]) ^ (p + 1) = X * X ^ p by
    rw [pow_succ']]
  linear_combination (norm := (simp [div_eq_mul_inv]; ring))
    (1 - X ^ 2) * hr - C (1 / 6 : ZMod p) * X * hs -
    C (h / 3) * X * hl + X ^ 2 * LPsrc p * h23

private theorem comp_linear_bound {K : Type*} [Field K]
    (P U : K[X]) (D : ℕ) (hP : P.natDegree ≤ D) (hU : U.natDegree ≤ 1) :
    (P.comp U).natDegree ≤ D := by
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hP hU).trans (by simp))

private theorem literalTbar_degree {K : Type*} [Field K]
    (p : ℕ) (h : K) : (universalTbarP p h).natDegree ≤ p - 1 := by
  have hneg : (-X : K[X]).natDegree ≤ 1 := by simp
  have hplus : (1 + X : K[X]).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (by simp)
  have hminus : (1 - X : K[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hAP : (AP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hplus
  have hBP : (BP : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans hminus
  have hE : (EP p : K[X]).natDegree ≤ p - 1 := by
    unfold EP
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_add_le _ _).trans (max_le (LP_natDegree_le p)
        (comp_linear_bound _ _ _ (LP_natDegree_le p) hneg)))
  have hL : (LPsrc p : K[X]).natDegree ≤ p - 1 := by
    unfold LPsrc
    exact (natDegree_add_le _ _).trans (max_le (by simp) hE)
  have hS : (S2P p : K[X]).natDegree ≤ p - 1 := by
    unfold S2P
    exact (natDegree_add_le _ _).trans
      (max_le (comp_linear_bound _ _ _ (RP_natDegree_le p) hBP)
        (comp_linear_bound _ _ _ (RP_natDegree_le p) hAP))
  have hR : (RP p + (RP p).comp (-X) : K[X]).natDegree ≤ p - 1 :=
    (natDegree_add_le _ _).trans (max_le (RP_natDegree_le p)
      (comp_linear_bound _ _ _ (RP_natDegree_le p) hneg))
  unfold universalTbarP
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hR) ((natDegree_C_mul_le _ _).trans hS)))
    ((natDegree_C_mul_le _ _).trans hL))

private theorem V2field_degree (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) : (V2field p h).natDegree ≤ p - 1 := by
  unfold V2field
  apply natDegree_sum_le_of_forall_le
  intro r hr
  have hr' := Finset.mem_range.mp hr
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  exact (natDegree_C_mul_le _ _).trans
    ((show (X ^ (2 * (r + 1)) : (ZMod p)[X]).natDegree ≤ 2 * (r + 1) by simp).trans
      (by omega))

private theorem V2field_origin (p : ℕ) [Fact p.Prime] (h : ZMod p) :
    (V2field p h).eval 0 = 0 := by
  unfold V2field
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro r hr
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by omega : 2 * (r + 1) ≠ 0), mul_zero]

private theorem RP_origin (p : ℕ) [Fact p.Prime] : (RP p : (ZMod p)[X]).eval 0 = 0 := by
  unfold RP
  rw [eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (Finset.mem_Ico.mp hj).1
  simp only [eval_mul, eval_C, eval_pow, eval_X,
    zero_pow (by omega : j ≠ 0), mul_zero]

private theorem RP_half (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (1 / 2 : ZMod p) = -(WPFiniteNC122.q p : ZMod p) ^ 2 / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hR2 : WPFiniteField.R p (2 : ZMod p) = -(WPFiniteNC122.q p : ZMod p) ^ 2 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) (ZMod p))
      (WPFiniteInversion.R_two_eq_fermat p hp)
    simpa only [← WPFiniteField.R_castHom, map_ofNat, map_neg,
      map_pow, map_intCast, WPFiniteNC122.q] using he
  have hpw : (2 : ZMod p) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using
      (WPFiniteField.natCast_pow_char (K := ZMod p) p 2)
  have he := WPFiniteField.R_inversion p (2 : ZMod p) h2
  rw [hpw, hR2] at he
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using he

private theorem literalTbar_origin (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) :
    (universalTbarP p h).eval 0 =
      (WPFiniteNC122.q p : ZMod p) ^ 2 / 6 - h * WPFiniteNC122.q p / 3 := by
  have hE : (EP p : (ZMod p)[X]).eval 0 = 0 := by
    rw [WPFiniteJSource.EP_half_cutoff p hp, eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).1
    simp only [eval_mul, eval_C, eval_pow, eval_X,
      zero_pow (by omega : 2 * j ≠ 0), mul_zero]
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  simp only [universalTbarP, eval_sub, eval_mul, eval_C, eval_add, eval_comp,
    eval_neg, eval_X, neg_zero, RP_origin, add_zero, S2P, AP, BP,
    eval_one, sub_zero, mul_one, LPsrc, hE]
  simp only [RP_eval]
  rw [show (2 : ZMod p)⁻¹ = 1 / 2 by simp]
  simp only [RP_half p hp]
  field_simp [h2, h3, h6]
  ring

private theorem zero_of_derivative_degree (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[X]) (hdeg : P.natDegree < p)
    (hder : P.derivative = 0) (hz : P.eval 0 = 0) : P = 0 := by
  ext n
  by_cases hn : n = 0
  · subst n
    simpa only [coeff_zero_eq_eval_zero, eval_zero, coeff_zero] using hz
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hnp)
  have hsmall : n ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have he : P.coeff n * (n : ZMod p) = 0 := by
    have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (n - 1)) hder
    simpa only [coeff_derivative, ← Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n), coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right
    (WPFiniteField.denominator_ne_zero p n hsmall)

/-- Literal finite polynomial identity; the origin coefficient is kept explicitly. -/
theorem actual_V2_eq_literal_Tbar (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (h : ZMod p) :
    V2field p h = universalTbarP p h +
      C (h * WPFiniteNC122.q p / 3 - (WPFiniteNC122.q p : ZMod p) ^ 2 / 6) := by
  let a : ZMod p := h * WPFiniteNC122.q p / 3 -
    (WPFiniteNC122.q p : ZMod p) ^ 2 / 6
  let D : (ZMod p)[X] := V2field p h - universalTbarP p h - C a
  have hdeg : D.natDegree < p := by
    have h0 := V2field_degree p hp h
    have h1 := literalTbar_degree (K := ZMod p) p h
    have h2 : (C a : (ZMod p)[X]).natDegree ≤ p - 1 := by simp
    exact ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le h0 h1)) h2)).trans_lt (by omega)
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
    norm_num at hc
  have hx : (X : (ZMod p)[X]) ≠ 0 := X_ne_zero
  have hder : D.derivative = 0 := by
    have hs : ((1 - X ^ 2) * X : (ZMod p)[X]) * D.derivative = 0 := by
      dsimp [D]
      simp only [derivative_sub, derivative_C, sub_zero]
      linear_combination V2field_cleared_derivative p hp h -
        literal_Tbar_cleared_derivative p hp h
    exact (mul_eq_zero.mp hs).resolve_left (mul_ne_zero hq hx)
  have hz : D.eval 0 = 0 := by
    simp only [D, eval_sub, eval_C, V2field_origin, literalTbar_origin p hp]
    dsimp [a]
    ring
  have hd := zero_of_derivative_degree p D hdeg hder hz
  dsimp [D, a] at hd
  linear_combination hd

/-- Only the proved low-degree multiple of F removes the constant. -/
theorem actual_V2_literal_Tbar_pair (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p ^ 2 *
      (universalPolynomialIntegral p hp).map (residueHom p)) =
      QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) := by
  have hF : QO p (actualLegendreJacobi p ^ 2) = 0 := by
    change ResidualProjection.Ij p 0 (ActualLowEuler.actualF p) = 0
    exact ResidualProjection.low_correction_both_projections_zero p hp _
      (ActualLowEuler.actualF_degree p hp) 0
  rw [universalPolynomialIntegral_field p hp,
    actual_V2_eq_literal_Tbar p hp (fieldHarmonic p (p / 6))]
  rw [mul_add, QO_add]
  have hc : actualLegendreJacobi p ^ 2 *
      C (fieldHarmonic p (p / 6) * WPFiniteNC122.q p / 3 -
        (WPFiniteNC122.q p : ZMod p) ^ 2 / 6) =
      C (fieldHarmonic p (p / 6) * WPFiniteNC122.q p / 3 -
        (WPFiniteNC122.q p : ZMod p) ^ 2 / 6) * actualLegendreJacobi p ^ 2 := by ring
  rw [hc, QO_C_mul, hF, mul_zero, add_zero]
  rfl

private theorem evenSeries_X_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    X * ((evenSeriesIntegral p hp).map (integralRationals p).subtype).derivative =
      ∑ r ∈ Finset.range ((p - 1) / 2), (X : ℚ[X]) ^ (2 * (r + 1)) := by
  simp only [evenSeriesIntegral, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_mul]
  rw [derivative_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  simp only [Subring.subtype_apply]
  rw [cauchyHalf_value, smallIntegralInverse_value p (r + 1) (by omega) (by omega),
    ← C_mul, derivative_C_mul_X_pow]
  have hc : ((1 / 2 : ℚ) * (1 / ((r + 1 : ℕ) : ℚ))) *
      ((2 * (r + 1) : ℕ) : ℚ) = 1 := by
    have hu : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hu]
  rw [hc, C_1, one_mul, ← pow_succ',
    Nat.sub_add_cancel (by omega : 1 ≤ 2 * (r + 1))]

private theorem evenSeries_rational_source (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      ((evenSeriesIntegral p hp).map (integralRationals p).subtype).derivative =
      (X - X ^ p : ℚ[X]) := by
  have he := evenSeries_X_derivative p hp
  have hg := even_geometric (K := ℚ) ((p - 1) / 2)
  have hn : 2 * (((p - 1) / 2) + 1) = p + 1 := by
    have hh := prime_half_identity p (by omega : 7 ≤ p)
    omega
  rw [hn, pow_succ'] at hg
  apply mul_left_cancel₀ (X_ne_zero : (X : ℚ[X]) ≠ 0)
  linear_combination (1 - X ^ 2) * he + hg

private theorem zeroEndEvenIntegral_endpoint_one (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (zeroEndEvenIntegral p hp).eval 1 = 0 := by
  simp only [zeroEndEvenIntegral, evenSeriesIntegral, eval_sub,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
  unfold integralHarmonic
  rw [← Finset.mul_sum]
  ring

/-- The actual zero-q-end logarithm, proved in characteristic zero. -/
theorem zeroEndEvenIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (zeroEndEvenIntegral p hp).map (integralRationals p).subtype =
      (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) := by
  let A := (zeroEndEvenIntegral p hp).map (integralRationals p).subtype
  let B : ℚ[X] := (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2)
  have ha : (1 - X ^ 2) * A.derivative = (X - X ^ p : ℚ[X]) := by
    dsimp [A]
    simp only [zeroEndEvenIntegral, Polynomial.map_sub, Polynomial.map_C,
      derivative_sub, derivative_C, sub_zero]
    exact evenSeries_rational_source p hp
  have hb : (1 - X ^ 2) * B.derivative = (X - X ^ p : ℚ[X]) :=
    rationalBinomialLog_pullback_source p (by omega)
  have hq : (1 - X ^ 2 : ℚ[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : ℚ[X] => P.coeff 0) hz
    norm_num at hc
  have hd : (A - B).derivative = 0 := by
    have hs : (1 - X ^ 2 : ℚ[X]) * (A - B).derivative = 0 := by
      rw [derivative_sub]
      linear_combination ha - hb
    exact (mul_eq_zero.mp hs).resolve_left hq
  have hA1 : A.eval 1 = 0 := by
    have he := congrArg (integralRationals p).subtype
      (zeroEndEvenIntegral_endpoint_one p hp)
    simpa only [← eval_map_apply, map_one, map_zero] using he
  have hB1 : B.eval 1 = 0 := by
    simp [B, eval_comp, rationalBinomialLog_origin]
  have he : (A - B).eval 1 = 0 := by rw [eval_sub, hA1, hB1, sub_self]
  have hz := rational_derivative_zero_one (A - B) he hd
  exact sub_eq_zero.mp hz

noncomputable def fullLogPairNumerator (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : ℚ :=
  QO p (rankJacobiNode p 1 ^ 2 *
    ((rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) +
      C (metricStar p hp).val * unitWindow ((p : ℚ) / 3) ((p - 1) / 2)))

noncomputable def fullLogDividedIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : integralRationals p :=
  -QOi p hp (balancedFirstIntegral p hp ^ 2 * universalPolynomialIntegral p hp) +
    (p : integralRationals p) *
      QOi p hp (balancedFirstIntegral p hp ^ 2 * universalRemainderIntegral p hp)

private theorem actual_F_QO_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : QO p (rankJacobiNode p 1 ^ 2) = 0 := by
  change ResidualProjection.Ij p 0 (NativeOriginalResidues.squareQ p) = 0
  exact ResidualProjection.low_correction_both_projections_zero p hp _
    (NativeOriginalResidues.actual_squareQ_degree p hp) 0

theorem fullLogPair_precision_two (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    fullLogPairNumerator p hp =
      -(p : ℚ) *
        (QOi p hp (balancedFirstIntegral p hp ^ 2 *
          universalPolynomialIntegral p hp)).val +
      (p : ℚ) ^ 2 *
        (QOi p hp (balancedFirstIntegral p hp ^ 2 *
          universalRemainderIntegral p hp)).val := by
  have he := congrArg (fun P : (integralRationals p)[X] =>
    P.map (integralRationals p).subtype)
    (actual_universal_polynomial_precision_two p hp)
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_natCast,
    map_mul, map_pow, map_natCast,
    zeroEndEvenIntegral_value p hp, weightedWindowIntegral_value p hp] at he
  have hm : rankJacobiNode p 1 ^ 2 *
      ((rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) +
        C (metricStar p hp).val * unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) =
      -C ((cauchyHalf p hp * integralHarmonic p ((p - 1) / 2)).val) *
        rankJacobiNode p 1 ^ 2 -
      C (p : ℚ) * (rankJacobiNode p 1 ^ 2 *
        (universalPolynomialIntegral p hp).map (integralRationals p).subtype) +
      C ((p : ℚ) ^ 2) * (rankJacobiNode p 1 ^ 2 *
        (universalRemainderIntegral p hp).map (integralRationals p).subtype) := by
    linear_combination (norm := (simp; ring)) (rankJacobiNode p 1 ^ 2) * he
  simp only [neg_mul] at hm
  have hq := congrArg (QO p) hm
  simp only [QO_add, QO_sub_local, QO_neg_local, QO_C_mul,
    actual_F_QO_zero p hp, mul_zero, neg_zero, zero_sub] at hq
  simp only [QOi_value, Polynomial.map_mul, Polynomial.map_pow,
    balancedFirstIntegral_value p hp]
  unfold fullLogPairNumerator
  linear_combination hq

/-- Explicit actual rational p division; no residue is divided by p. -/
theorem fullLogDividedIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (fullLogDividedIntegral p hp).val = fullLogPairNumerator p hp / (p : ℚ) := by
  change -(QOi p hp (balancedFirstIntegral p hp ^ 2 *
      universalPolynomialIntegral p hp)).val +
    (p : ℚ) * (QOi p hp (balancedFirstIntegral p hp ^ 2 *
      universalRemainderIntegral p hp)).val = _
  rw [fullLogPair_precision_two p hp]
  field_simp [show (p : ℚ) ≠ 0 by positivity]

/-- SB82d with the literal Tbar, including its original normalization. -/
theorem actual_SB82d (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (fullLogDividedIntegral p hp) =
      -QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) := by
  simp only [fullLogDividedIntegral, map_add, map_neg, map_mul,
    map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    QOi_field, Polynomial.map_mul, Polynomial.map_pow,
    balancedFirstIntegral_field p hp]
  rw [actual_V2_literal_Tbar_pair p hp]

private theorem fullLogPair_split (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    fullLogPairNumerator p hp =
      QO p (rankJacobiNode p 1 ^ 2 *
        (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2)) +
      (metricStar p hp).val * QO p (rankJacobiNode p 1 ^ 2 *
        unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) := by
  unfold fullLogPairNumerator
  have he : rankJacobiNode p 1 ^ 2 *
      ((rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) +
        C (metricStar p hp).val * unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) =
      rankJacobiNode p 1 ^ 2 *
        (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2) +
      C (metricStar p hp).val * (rankJacobiNode p 1 ^ 2 *
        unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) := by ring
  rw [he, QO_add, QO_C_mul]

noncomputable def coupledCauchyNormNumerator (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : ℚ :=
  fullUnitG p hp / 3 - QH p (rankJacobiNode p 1 ^ 2) / 2 -
    WPFirstResidue.LiteralNormalization.literalR0 p

/-- The whole finite-log numerator, before its p division. -/
theorem finiteGreen_Cauchy_source (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    finiteGreenNumerator p hp =
      -fullLogPairNumerator p hp / 3 + coupledCauchyNormNumerator p hp := by
  have he : finiteGreenJ p hp =
      C (2 : ℚ) * (rankJacobiNode p 1 ^ 2 *
        (rationalBinomialLog ((p - 1) / 2)).comp (1 - X ^ 2)) +
      C (2 * (balancedProperQ p hp).eval 1) * rankJacobiNode p 1 ^ 2 -
      C (2 : ℚ) * (X ^ p * (rankJacobiNode p 1 * balancedProperQ p hp)) := by
    unfold finiteGreenJ
    simp only [map_mul, map_ofNat]
    ring
  rw [finiteGreenNumerator, he]
  simp only [QO_sub_local, QO_add, QO_C_mul, actual_F_QO_zero p hp,
    mul_zero, add_zero]
  rw [actual_SB82c p hp, fullLogPair_split p hp]
  unfold coupledCauchyNormNumerator
  ring

noncomputable def coupledCauchyNormDigitIntegral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : integralRationals p :=
  finiteGreenDigitIntegral p hp +
    (2 * integralSixth p (by omega)) * fullLogDividedIntegral p hp

/-- The remaining digit is the specified joint norm numerator / p over Q. -/
theorem coupledCauchyNormDigitIntegral_value (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (coupledCauchyNormDigitIntegral p hp).val =
      coupledCauchyNormNumerator p hp / (p : ℚ) := by
  change (finiteGreenDigitIntegral p hp).val +
    (2 * (1 / 6 : ℚ)) * (fullLogDividedIntegral p hp).val = _
  rw [finiteGreenDigitIntegral_value p hp, fullLogDividedIntegral_value p hp,
    finiteGreen_Cauchy_source p hp]
  field_simp [show (p : ℚ) ≠ 0 by positivity]
  ring

/-- Actual SB82e: literal Tbar plus the still-coupled leading low norm digit. -/
theorem actual_SB82e (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (finiteGreenDigitIntegral p hp) =
      QO p (actualLegendreJacobi p ^ 2 * actualTbarP p) / 3 +
        residueHom p (coupledCauchyNormDigitIntegral p hp) := by
  simp only [coupledCauchyNormDigitIntegral, map_add, map_mul, map_ofNat,
    integralSixth_field, actual_SB82d p hp]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h3, h6]
  ring

end WPFieldAssembly.ActualCauchyTbarAttachment
