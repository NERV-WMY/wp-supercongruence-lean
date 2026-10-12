import WPFieldAssembly.ActualBpairLowHEndpoints
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFiniteNC122Residue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The original quadratic coordinate x=5t^2-1. -/
noncomputable def lowHQuadraticX : K[X] := C 5 * X ^ 2 - 1

noncomputable def lowHLinearS : K[X] := C (1 / 5 : K) * (X + 1)

/-- The literal polynomial y*s^N/Abar, with its proper-end factors cancelled as a whole. -/
noncomputable def lowHWeightedBranchDensity (N : ℕ) (H : K[X]) : K[X] :=
  C (1 / 125 : K) * (4 * X - 1) * H.divX.comp VP * lowHLinearS ^ N

/-- The full t^p source is retained before the even contraction. -/
noncomputable def lowHWeightedTPrimitive (p : ℕ) (H : K[X]) : K[X] :=
  C (2 / 15 : K) * X ^ p * (lowHEulerJ p H).comp lowHTripleC

noncomputable def lowHWeightedXPrimitive (p : ℕ) (H : K[X]) : K[X] :=
  ((lowHWeightedTPrimitive p H).contract 2).comp lowHLinearS

private theorem lowHWeighted_units (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 ∧ (5 : K) ≠ 0 ∧ (125 : K) ≠ 0 := by
  refine ⟨WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega)),
    WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega)),
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)), ?_⟩
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  convert pow_ne_zero 3 h5 using 1; norm_num

theorem lowHQuadraticX_cubic_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (VP : K[X]).comp lowHQuadraticX = 1 - lowHTripleC ^ 2 := by
  have hu := lowHWeighted_units (K := K) p hp
  have hc := congrArg (C : K →+* K[X]) (inv_mul_cancel₀ hu.2.2.2)
  simp only [map_mul, map_ofNat, map_one] at hc
  simp only [VP, mul_comp, C_comp, pow_comp, sub_comp, X_comp, ofNat_comp,
    lowHQuadraticX, lowHTripleC, one_comp, C_ofNat]
  linear_combination (1 - (X : K[X]) ^ 2) * (4 * X ^ 2 - 1) ^ 2 * hc

theorem lowHLinearS_quadratic_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (lowHLinearS : K[X]).comp lowHQuadraticX = X ^ 2 := by
  have hu := lowHWeighted_units (K := K) p hp
  have hc := congrArg (C : K →+* K[X]) (one_div_mul_cancel hu.2.2.1)
  simp only [map_mul, map_ofNat, map_one] at hc
  simp only [lowHLinearS, lowHQuadraticX, mul_comp, C_comp, add_comp, X_comp, one_comp,
    C_ofNat]
  linear_combination (X : K[X]) ^ 2 * hc

theorem lowHWeightedTPrimitive_even (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHWeightedTPrimitive p H).comp (-X) = lowHWeightedTPrimitive p H := by
  have hx : (-(X : K[X])) ^ p = -(X ^ p) := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with he | ⟨k, hk⟩
    · omega
    · have hp' : p = 2 * k + 1 := by omega
      rw [hp', pow_succ, pow_mul, neg_sq]
      ring
  have hj := lowHEulerJ_odd p hp d hd hband H hH
  have hc : (lowHTripleC : K[X]).comp (-X) = -lowHTripleC := by
    simp only [lowHTripleC, sub_comp, mul_comp, C_comp, pow_comp, X_comp]
    ring
  have he : (lowHEulerJ p H).comp (-lowHTripleC) = -(lowHEulerJ p H).comp lowHTripleC := by
    rw [show -(lowHTripleC : K[X]) = (-(X : K[X])).comp lowHTripleC by rw [neg_comp, X_comp],
      ← comp_assoc, hj, neg_comp]
  simp only [lowHWeightedTPrimitive, mul_comp, C_comp, pow_comp, X_comp, comp_assoc, hc, hx, he]
  ring

/-- Every coefficient, including the top Frobenius source, enters the even contraction. -/
theorem lowHWeightedTPrimitive_expand (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    expand K 2 ((lowHWeightedTPrimitive p H).contract 2) = lowHWeightedTPrimitive p H := by
  have hu := lowHWeighted_units (K := K) p hp
  have heven := lowHWeightedTPrimitive_even p hp d hd hband H hH
  have hodd (n : ℕ) (hn : ¬2 ∣ n) : (lowHWeightedTPrimitive p H).coeff n = 0 := by
    have hn0 : n % 2 ≠ 0 := by intro h; exact hn (Nat.dvd_of_mod_eq_zero h)
    have hn' : n = 2 * (n / 2) + 1 := by have := Nat.mod_add_div n 2; omega
    have hpow : (-1 : K) ^ n = -1 := by
      rw [hn', pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    have hx : -(X : K[X]) = C (-1 : K) * X := by rw [map_neg, map_one]; ring
    have he := congrArg (fun P : K[X] => P.coeff n) heven
    rw [hx, comp_C_mul_X_coeff, hpow] at he
    have hz : (lowHWeightedTPrimitive p H).coeff n * 2 = 0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_right hu.1
  ext n
  rw [coeff_expand (by decide : 0 < 2), coeff_contract (by decide : 2 ≠ 0)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, Nat.div_mul_cancel hn]
  · rw [if_neg hn, hodd n hn]

theorem lowHWeightedTPrimitive_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hN : 2 * N + 1 = p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHWeightedTPrimitive p H).derivative =
      (lowHWeightedBranchDensity N H).comp lowHQuadraticX * lowHQuadraticX.derivative := by
  have hu := lowHWeighted_units (K := K) p hp
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hcoef : (2 / 15 : K) * 3 = (1 / 125 : K) * 50 := by
    field_simp [h15, hu.2.2.2]
    ring
  have hcoefC := congrArg (C : K →+* K[X]) hcoef
  simp only [map_mul, map_ofNat] at hcoefC
  have hxp : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, CharP.cast_eq_zero K p, map_zero, zero_mul]
  have ht : (lowHTripleC : K[X]).derivative = 3 * (4 * X ^ 2 - 1) := by
    rw [lowHTripleC, derivative_sub, derivative_C_mul, derivative_C_mul,
      derivative_X_pow, derivative_X]
    simp only [Nat.cast_ofNat, C_ofNat, Nat.reduceSub]
    ring
  have hU : (lowHQuadraticX : K[X]).derivative = C (10 : K) * X := by
    rw [lowHQuadraticX, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_one]
    simp only [Nat.cast_ofNat, C_ofNat, Nat.reduceSub, pow_one, sub_zero]
    ring
  rw [lowHWeightedTPrimitive, derivative_mul, derivative_mul, derivative_C, hxp]
  simp only [zero_mul, mul_zero, zero_add]
  rw [derivative_comp,
    lowHEulerJ_derivative p hp d hd hband H hH, ht]
  simp only [lowHEulerR, comp_assoc, sub_comp, one_comp, pow_comp, X_comp]
  rw [← lowHQuadraticX_cubic_source p hp]
  simp only [lowHWeightedBranchDensity, mul_comp, C_comp, sub_comp, ofNat_comp,
    X_comp, one_comp, pow_comp]
  rw [lowHLinearS_quadratic_source p hp, hU]
  simp only [comp_assoc, lowHQuadraticX, C_ofNat, Nat.cast_ofNat]
  rw [← pow_mul, ← hN, pow_succ]
  linear_combination (X : K[X]) ^ (2 * N) * X * (4 * X ^ 2 - 1) *
      H.divX.comp (VP.comp (5 * X ^ 2 - 1)) *
      hcoefC

theorem lowHWeightedBranchDensity_source (N : ℕ) (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHCubicY H * lowHLinearS ^ N =
      ((4 - X) * (4 * X - 1)) * lowHWeightedBranchDensity N H := by
  rw [lowHCubicY_source H h0]
  simp only [VP, lowHWeightedBranchDensity, one_div]
  ring

private theorem lowH_compQuadratic_injective (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F G : K[X]) (he : F.comp lowHQuadraticX = G.comp lowHQuadraticX) : F = G := by
  have hz : (F - G).comp lowHQuadraticX = 0 := by rw [sub_comp, he, sub_self]
  rcases comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
  · exact sub_eq_zero.mp h
  · have hc := congrArg (fun Q : K[X] => Q.coeff 2) h
    have hu := lowHWeighted_units (K := K) p hp
    simp [lowHQuadraticX] at hc
    exact False.elim (hu.2.2.1 hc)

theorem lowHWeightedXPrimitive_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hN : 2 * N + 1 = p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHWeightedXPrimitive p H).derivative = lowHWeightedBranchDensity N H := by
  have hu := lowHWeighted_units (K := K) p hp
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero hu.1 hu.2.2.1
  have hU : (lowHQuadraticX : K[X]).derivative = C (10 : K) * X := by
    rw [lowHQuadraticX, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_one]
    simp only [Nat.cast_ofNat, C_ofNat, Nat.reduceSub, pow_one, sub_zero]
    ring
  have hUne : (lowHQuadraticX : K[X]).derivative ≠ 0 := by
    rw [hU]
    exact mul_ne_zero (C_ne_zero.mpr h10) (X_ne_zero (R := K))
  have he : (lowHWeightedXPrimitive p H).comp lowHQuadraticX = lowHWeightedTPrimitive p H := by
    rw [lowHWeightedXPrimitive, comp_assoc, lowHLinearS_quadratic_source p hp,
      ← expand_eq_comp_X_pow, lowHWeightedTPrimitive_expand p hp d hd hband H hH]
  have hder := congrArg Polynomial.derivative he
  rw [derivative_comp, lowHWeightedTPrimitive_derivative p N hp hN d hd hband H hH] at hder
  apply lowH_compQuadratic_injective p hp
  exact mul_right_cancel₀ hUne (by simpa only [mul_comm] using hder)

theorem lowHWeightedXPrimitive_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHWeightedXPrimitive p H).natDegree < p := by
  have ht : (lowHTripleC : K[X]).natDegree ≤ 3 := by
    unfold lowHTripleC
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp))
      ((natDegree_C_mul_le _ _).trans (by simp)))
  have hj := lowHEulerJ_degree p hp d hd hband H hH
  have hc : ((lowHEulerJ p H).comp lowHTripleC).natDegree ≤ (2 * d - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hj ht)
  have hF : (lowHWeightedTPrimitive p H).natDegree ≤ p + (2 * d - 1) * 3 := by
    exact (natDegree_mul_le (p := C (2 / 15 : K) * X ^ p)
      (q := (lowHEulerJ p H).comp lowHTripleC)).trans
        (Nat.add_le_add ((natDegree_C_mul_le _ _).trans (by simp)) hc)
  have he := congrArg Polynomial.natDegree (lowHWeightedTPrimitive_expand p hp d hd hband H hH)
  rw [natDegree_expand] at he
  have hhalf : ((lowHWeightedTPrimitive p H).contract 2).natDegree < p := by omega
  have hs : (lowHLinearS : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  exact natDegree_comp_le.trans_lt (by
    have hm := Nat.mul_le_mul_left ((lowHWeightedTPrimitive p H).contract 2).natDegree hs
    exact hm.trans_lt (by simpa only [Nat.mul_one] using hhalf))

theorem lowHWeightedBranchDensity_degree (p N : ℕ) (hp : 19 ≤ p) (hN : 2 * N + 1 = p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHWeightedBranchDensity N H).natDegree < p - 1 := by
  have hdiv : H.divX.natDegree ≤ d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have hc : (H.divX.comp (VP : K[X])).natDegree ≤ (d - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hdiv lowHCubicV_degree)
  have hl : (4 * (X : K[X]) - 1).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have hs : (lowHLinearS : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hpow : ((lowHLinearS : K[X]) ^ N).natDegree ≤ N :=
    natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left N hs)
  have he : (lowHWeightedBranchDensity N H).natDegree ≤ 1 + (d - 1) * 3 + N :=
    natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add ((natDegree_C_mul_le _ _).trans hl) hc)) hpow)
  omega

/-- This is the canonical original x integral, obtained from the entire even t primitive. -/
theorem lowHWeightedBranchDensity_integral (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hN : 2 * N + 1 = p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) (c : K) :
    (lowHIntegralP p (lowHWeightedBranchDensity N H)).eval c =
      (lowHWeightedXPrimitive p H).eval c - (lowHWeightedXPrimitive p H).eval 0 := by
  let J := lowHWeightedXPrimitive p H
  let I := lowHIntegralP p (lowHWeightedBranchDensity N H)
  have hJ := lowHWeightedXPrimitive_degree p hp d hd hband H hH
  have hI : I.natDegree < p := (lowHIntegralP_degree p _).trans_lt (by omega)
  have hdeg : (I - J + C (J.eval 0)).natDegree < p :=
    (natDegree_add_le _ _).trans_lt (max_lt
      ((natDegree_sub_le _ _).trans_lt (max_lt hI hJ)) (by simpa using (by omega : 0 < p)))
  have hder : (I - J + C (J.eval 0)).derivative = 0 := by
    rw [derivative_add, derivative_sub, derivative_C, add_zero]
    rw [lowHIntegralP_derivative p hp _
      (lowHWeightedBranchDensity_degree p N hp hN d hd hband H hH),
      lowHWeightedXPrimitive_derivative p N hp hN d hd hband H hH, sub_self]
  have h0 : (I - J + C (J.eval 0)).eval 0 = 0 := by
    rw [eval_add, eval_sub, eval_C, lowHIntegralP_zero]
    ring
  have hz := WPFinitePrimitiveTransport.zero_of_derivative_degree p _ hdeg hder h0
  have he := congrArg (fun Q : K[X] => Q.eval c) hz
  simp only [eval_add, eval_sub, eval_C, eval_zero] at he
  linear_combination he

/-- The original branch difference is J_H(1)/5, with the native Gauss value still unevaluated. -/
theorem lowHWeightedBranchDensity_both_ends (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hN : 2 * N + 1 = p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHIntegralP p (lowHWeightedBranchDensity N H)).eval 4 -
      (lowHIntegralP p (lowHWeightedBranchDensity N H)).eval (1 / 4) =
        (1 / 5 : K) * (lowHEulerJ p H).eval 1 := by
  have hu := lowHWeighted_units (K := K) p hp
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h30 : (30 : K) ≠ 0 := by
    rw [show (30 : K) = 2 * 3 * 5 by ring]
    exact mul_ne_zero (mul_ne_zero hu.1 hu.2.1) hu.2.2.1
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h2p : (2 : K) ^ p = 2 := WPFiniteField.natCast_pow_char p 2
  have hhalf : (1 / 2 : K) ^ p = 1 / 2 := by rw [one_div, inv_pow, h2p]
  have hSb : (lowHLinearS : K[X]).eval 4 = 1 := by
    simp only [lowHLinearS, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [hu.2.2.1]
    ring
  have hSa : (lowHLinearS : K[X]).eval (1 / 4) = (1 / 2 : K) ^ 2 := by
    simp only [lowHLinearS, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [hu.1, h4, hu.2.2.1]
    ring
  have hTc1 : (lowHTripleC : K[X]).eval 1 = 1 := by
    simp only [lowHTripleC, eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    ring
  have hTch : (lowHTripleC : K[X]).eval (1 / 2) = -1 := by
    simp only [lowHTripleC, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    field_simp [hu.1]
    ring
  have he (z : K) : ((lowHWeightedTPrimitive p H).contract 2).eval (z ^ 2) =
      (lowHWeightedTPrimitive p H).eval z := by
    have hh := congrArg (fun Q : K[X] => Q.eval z)
      (lowHWeightedTPrimitive_expand p hp d hd hband H hH)
    simpa only [expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X] using hh
  have he1 : ((lowHWeightedTPrimitive p H).contract 2).eval 1 =
      (lowHWeightedTPrimitive p H).eval 1 := by simpa only [one_pow] using he 1
  calc
    _ = (lowHWeightedXPrimitive p H).eval 4 - (lowHWeightedXPrimitive p H).eval (1 / 4) := by
      rw [lowHWeightedBranchDensity_integral p N hp hN d hd hband H hH,
        lowHWeightedBranchDensity_integral p N hp hN d hd hband H hH]
      ring
    _ = _ := by
      rw [lowHWeightedXPrimitive, eval_comp, eval_comp, hSb, hSa, he1, he (1 / 2)]
      simp only [lowHWeightedTPrimitive, eval_mul, eval_C, eval_pow, eval_X, eval_comp,
        hTc1, hTch, one_pow, mul_one, hhalf,
        lowHEulerJ_negative_one p hp d hd hband H hH]
      field_simp [hu.1, h15, hu.2.2.1, h30]
      ring

theorem lowHWeightedBranchDensity_prime_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHIntegralP p (lowHWeightedBranchDensity ((p - 1) / 2) H)).eval 4 -
      (lowHIntegralP p (lowHWeightedBranchDensity ((p - 1) / 2) H)).eval (1 / 4) =
        (1 / 5 : K) * (lowHEulerJ p H).eval 1 := by
  have hb := lowH_prime_six_band p hp
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  exact lowHWeightedBranchDensity_both_ends p ((p - 1) / 2) hp hN (p / 6) (by omega) hb.2 H hH

end WPFieldAssembly.ActualBpairContraction
