import WPFieldAssembly.ActualBpairLowHGreen
import WPFieldAssembly.ActualBpairLowHConicPrimitive
import WPFinitePrimitiveTransport

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The sharper bound uses the actual sub-p source, so no invisible term is removed. -/
theorem lowH_primitive_sharp_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (J R : K[X]) (hJ : J.natDegree < p) (hsource : J.derivative = R) (m : ℕ)
    (hR : R.natDegree ≤ m) : J.natDegree ≤ m + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hnp : p ≤ n
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hu : (n : K) ≠ 0 := WPFiniteField.denominator_ne_zero p n
    (Finset.mem_Ico.mpr (by omega))
  have he := congrArg (fun P : K[X] => P.coeff (n - 1)) hsource
  simp only [coeff_derivative, ← Nat.cast_add_one,
    Nat.sub_add_cancel (by omega : 1 ≤ n)] at he
  rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < n - 1)] at he
  exact (mul_eq_zero.mp he).resolve_right hu

theorem lowH_primitive_odd (p : ℕ) [Fact p.Prime] [CharP K p]
    (J R : K[X]) (hJ : J.natDegree < p) (hJ0 : J.eval 0 = 0)
    (hsource : J.derivative = R) (heven : R.comp (-X) = R) :
    J.comp (-X) = -J := by
  have hdeg : (J.comp (-X) + J).natDegree < p := by
    have hc : (J.comp (-X)).natDegree ≤ J.natDegree := by
      simpa only [natDegree_neg, natDegree_X, Nat.mul_one] using
        (natDegree_comp_le (p := J) (q := -(X : K[X])))
    exact (natDegree_add_le _ _).trans_lt (max_lt (hc.trans_lt hJ) hJ)
  have hd : (J.comp (-X) + J).derivative = 0 := by
    rw [derivative_add, derivative_comp, hsource, heven, derivative_neg, derivative_X]
    ring
  have hz : (J.comp (-X) + J).eval 0 = 0 := by
    simp only [eval_add, eval_comp, eval_neg, eval_X, neg_zero, hJ0, add_zero]
  have he := WPFinitePrimitiveTransport.zero_of_derivative_degree p _ hdeg hd hz
  exact eq_neg_of_add_eq_zero_left he

theorem lowH_odd_even_coeff (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (J : K[X]) (hodd : J.comp (-X) = -J) (n : ℕ) (hn : n % 2 = 0) : J.coeff n = 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hn' : n = 2 * (n / 2) := by have := Nat.mod_add_div n 2; omega
  have hpow : (-1 : K) ^ n = 1 := by rw [hn', pow_mul, neg_one_sq, one_pow]
  have hx : -(X : K[X]) = C (-1 : K) * X := by rw [map_neg, map_one]; ring
  have he := congrArg (fun P : K[X] => P.coeff n) hodd
  rw [hx, comp_C_mul_X_coeff, hpow, mul_one, coeff_neg] at he
  have hz : J.coeff n * 2 = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_right h2

/-- H(q)/q is taken as the literal polynomial divX, before conic composition. -/
noncomputable def lowHEulerR (H : K[X]) : K[X] := H.divX.comp (1 - X ^ 2)

noncomputable def lowHEulerJ (p : ℕ) (H : K[X]) : K[X] := lowHIntegralP p (lowHEulerR H)

theorem lowHEulerR_degree (d : ℕ) (hd : 1 ≤ d) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerR H).natDegree ≤ 2 * d - 2 := by
  have hq : (1 - (X : K[X]) ^ 2).natDegree ≤ 2 := by
    apply (natDegree_sub_le _ _).trans
    simp only [natDegree_one, natDegree_X_pow]
    omega
  have hh : H.divX.natDegree ≤ d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have he : (lowHEulerR H).natDegree ≤ (d - 1) * 2 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hh hq)
  omega

theorem lowHEulerR_even (H : K[X]) : (lowHEulerR H).comp (-X) = lowHEulerR H := by
  have hx : (1 - (X : K[X]) ^ 2).comp (-X) = 1 - X ^ 2 := by
    simp only [sub_comp, one_comp, pow_comp, X_comp, neg_sq]
  rw [lowHEulerR, comp_assoc, hx]

theorem lowHEulerJ_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerJ p H).derivative = lowHEulerR H := by
  exact lowHIntegralP_derivative p hp _ (by have := lowHEulerR_degree d hd H hH; omega)

theorem lowHEulerJ_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (hH0 : H.coeff 0 = 0) :
    (1 - X ^ 2) * (lowHEulerJ p H).derivative = H.comp (1 - X ^ 2) := by
  rw [lowHEulerJ_derivative p hp d hd hband H hH]
  have he := congrArg (fun P : K[X] => P.comp (1 - X ^ 2)) (X_mul_divX_add H)
  simpa only [lowHEulerR, mul_comp, X_comp, C_comp, hH0, map_zero, add_zero] using he

theorem lowHEulerJ_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerJ p H).natDegree ≤ 2 * d - 1 := by
  have he := lowH_primitive_sharp_degree p (lowHEulerJ p H) (lowHEulerR H)
    (by change (lowHIntegralP p (lowHEulerR H)).natDegree < p
        have := lowHIntegralP_degree p (lowHEulerR H)
        omega)
    (lowHEulerJ_derivative p hp d hd hband H hH) (2 * d - 2) (lowHEulerR_degree d hd H hH)
  omega

theorem lowHEulerJ_odd (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerJ p H).comp (-X) = -lowHEulerJ p H := by
  exact lowH_primitive_odd p _ _
    (by change (lowHIntegralP p (lowHEulerR H)).natDegree < p
        have := lowHIntegralP_degree p (lowHEulerR H)
        omega)
    (lowHIntegralP_zero p _) (lowHEulerJ_derivative p hp d hd hband H hH) (lowHEulerR_even H)

theorem lowHEulerJ_negative_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerJ p H).eval (-1) = -(lowHEulerJ p H).eval 1 := by
  have he := congrArg (fun P : K[X] => P.eval 1) (lowHEulerJ_odd p hp d hd hband H hH)
  simpa only [eval_comp, eval_neg, eval_X] using he

noncomputable def lowHTripleC : K[X] := C 4 * X ^ 3 - C 3 * X

/-- The endpoint is retained literally, before any native Gauss evaluation. -/
noncomputable def lowHEulerDelta (p : ℕ) (H : K[X]) : K[X] :=
  (lowHEulerJ p H).comp lowHTripleC - C ((lowHEulerJ p H).eval 1) * lowHTripleC

private theorem lowHTripleC_degree : (lowHTripleC : K[X]).natDegree ≤ 3 := by
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_C_mul_le _ _).trans (by simp))
    ((natDegree_C_mul_le _ _).trans (by simp)))

private theorem lowHTripleC_odd : (lowHTripleC : K[X]).comp (-X) = -lowHTripleC := by
  simp only [lowHTripleC, sub_comp, mul_comp, C_comp, pow_comp, X_comp]
  ring

theorem lowHEulerDelta_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerDelta p H).natDegree ≤ 6 * d - 3 := by
  have hj := lowHEulerJ_degree p hp d hd hband H hH
  have hc : ((lowHEulerJ p H).comp lowHTripleC).natDegree ≤ (2 * d - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hj lowHTripleC_degree)
  have he : (lowHEulerDelta p H).natDegree ≤ max ((2 * d - 1) * 3) 3 :=
    (natDegree_sub_le _ _).trans (max_le_max hc ((natDegree_C_mul_le _ _).trans lowHTripleC_degree))
  omega

theorem lowHEulerDelta_odd (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerDelta p H).comp (-X) = -lowHEulerDelta p H := by
  have hj := lowHEulerJ_odd p hp d hd hband H hH
  have hx : -(lowHTripleC : K[X]) = (-(X : K[X])).comp lowHTripleC := by
    rw [neg_comp, X_comp]
  simp only [lowHEulerDelta, sub_comp, mul_comp, C_comp, comp_assoc, lowHTripleC_odd]
  rw [hx, ← comp_assoc, hj, neg_comp]
  simp only [neg_comp, X_comp]
  ring

theorem lowHEulerDelta_one (p : ℕ) (H : K[X]) : (lowHEulerDelta p H).eval 1 = 0 := by
  have ht : (lowHTripleC : K[X]).eval 1 = 1 := by
    simp only [lowHTripleC, eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    ring
  rw [lowHEulerDelta, eval_sub, eval_comp, eval_mul, eval_C, ht, mul_one, sub_self]

theorem lowHEulerDelta_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerDelta p H).eval (1 / 2) = 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have ht : (lowHTripleC : K[X]).eval (1 / 2) = -1 := by
    simp only [lowHTripleC, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    field_simp [h2]
    ring
  rw [lowHEulerDelta, eval_sub, eval_comp, eval_mul, eval_C, ht,
    lowHEulerJ_negative_one p hp d hd hband H hH]
  ring

theorem lowHEulerDelta_four_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHEulerDelta p H).eval 1 = 0 ∧ (lowHEulerDelta p H).eval (-1) = 0 ∧
      (lowHEulerDelta p H).eval (1 / 2) = 0 ∧ (lowHEulerDelta p H).eval (-(1 / 2)) = 0 := by
  have hodd := lowHEulerDelta_odd p hp d hd hband H hH
  have he (z : K) : (lowHEulerDelta p H).eval (-z) = -(lowHEulerDelta p H).eval z := by
    have hh := congrArg (fun P : K[X] => P.eval z) hodd
    simpa only [eval_comp, eval_neg, eval_X] using hh
  refine ⟨lowHEulerDelta_one p H, ?_, lowHEulerDelta_half p hp d hd hband H hH, ?_⟩
  · rw [he, lowHEulerDelta_one, neg_zero]
  · rw [he, lowHEulerDelta_half p hp d hd hband H hH, neg_zero]

/-- The four genuine branch factors, before any quotient or conic substitution. -/
noncomputable def lowHBranchQuartic : K[X] :=
  ((X - C 1) * (X - C (-1))) * (X - C (1 / 2)) * (X - C (-(1 / 2)))

noncomputable def lowHBranchA : K[X] := (1 - X ^ 2) * (C 4 * X ^ 2 - 1)

theorem lowH_four_ends_divisibility (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (Q : K[X]) (h1 : Q.eval 1 = 0) (hm1 : Q.eval (-1) = 0)
    (hh : Q.eval (1 / 2) = 0) (hmh : Q.eval (-(1 / 2)) = 0) :
    (lowHBranchQuartic : K[X]) ∣ Q := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 : K) - 1 / 2 = 1 / 2 := by field_simp [h2]; ring
  have hb : (1 : K) - -(1 / 2) = 3 / 2 := by field_simp [h2]; ring
  have hc : (-1 : K) - 1 / 2 = -(3 / 2) := by field_simp [h2]; ring
  have hd : (-1 : K) - -(1 / 2) = -(1 / 2) := by field_simp [h2]; ring
  have he : (1 / 2 : K) - -(1 / 2) = 1 := by field_simp [h2]; ring
  have h12 : IsCoprime (X - C (1 : K)) (X - C (-1 : K)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    have hdiff : (1 : K) - -1 ≠ 0 := by convert h2 using 1; ring
    exact hdiff.isUnit
  have h1h : IsCoprime (X - C (1 : K)) (X - C (1 / 2 : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [ha]; exact (one_div_ne_zero h2).isUnit)
  have h1mh : IsCoprime (X - C (1 : K)) (X - C (-(1 / 2) : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [hb]; exact (div_ne_zero h3 h2).isUnit)
  have hm1h : IsCoprime (X - C (-1 : K)) (X - C (1 / 2 : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [hc]; exact (neg_ne_zero.mpr (div_ne_zero h3 h2)).isUnit)
  have hm1mh : IsCoprime (X - C (-1 : K)) (X - C (-(1 / 2) : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [hd]; exact (neg_ne_zero.mpr (one_div_ne_zero h2)).isUnit)
  have hhmh : IsCoprime (X - C (1 / 2 : K)) (X - C (-(1 / 2) : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by rw [he]; exact isUnit_one)
  have hd1 := (dvd_iff_isRoot.mpr h1 : X - C (1 : K) ∣ Q)
  have hdm1 := (dvd_iff_isRoot.mpr hm1 : X - C (-1 : K) ∣ Q)
  have hdh := (dvd_iff_isRoot.mpr hh : X - C (1 / 2 : K) ∣ Q)
  have hdmh := (dvd_iff_isRoot.mpr hmh : X - C (-(1 / 2) : K) ∣ Q)
  exact ((h1mh.mul_left hm1mh).mul_left hhmh).mul_dvd
    ((h1h.mul_left hm1h).mul_dvd (h12.mul_dvd hd1 hdm1) hdh) hdmh

theorem lowHBranchA_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (lowHBranchA : K[X]) = C (-4 : K) * lowHBranchQuartic := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hs : (4 : K) * (1 / 2) ^ 2 = 1 := by field_simp [h2]; ring
  have hc := congrArg (C : K →+* K[X]) hs
  simp only [map_mul, map_pow, map_ofNat, map_one] at hc
  simp only [lowHBranchA, lowHBranchQuartic, map_one, map_neg, map_ofNat]
  linear_combination (1 - (X : K[X]) ^ 2) * hc

private theorem lowHBranchQuartic_monic : (lowHBranchQuartic : K[X]).Monic :=
  (((monic_X_sub_C 1).mul (monic_X_sub_C (-1))).mul (monic_X_sub_C (1 / 2))).mul
    (monic_X_sub_C (-(1 / 2)))

private theorem lowHBranchQuartic_degree : (lowHBranchQuartic : K[X]).natDegree = 4 := by
  unfold lowHBranchQuartic
  rw [(((monic_X_sub_C (1 : K)).mul (monic_X_sub_C (-1))).mul
      (monic_X_sub_C (1 / 2))).natDegree_mul (monic_X_sub_C (-(1 / 2))),
    ((monic_X_sub_C (1 : K)).mul (monic_X_sub_C (-1))).natDegree_mul (monic_X_sub_C (1 / 2)),
    (monic_X_sub_C (1 : K)).natDegree_mul (monic_X_sub_C (-1))]
  norm_num only [natDegree_X_sub_C]

theorem lowHBranchA_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (lowHBranchA : K[X]).natDegree = 4 := by
  have h4 : (-4 : K) ≠ 0 := neg_ne_zero.mpr (WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega)))
  rw [lowHBranchA_factor p hp, natDegree_C_mul_of_isUnit h4.isUnit, lowHBranchQuartic_degree]

theorem lowHBranchA_even : (lowHBranchA : K[X]).comp (-X) = lowHBranchA := by
  simp only [lowHBranchA, mul_comp, sub_comp, one_comp, C_comp, pow_comp, X_comp, neg_sq]

/-- The whole endpoint correction factors through the original quartic with exact parity and degree. -/
theorem lowHEulerDelta_conic_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 2 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d) :
    ∃ P : K[X], lowHEulerDelta p H = lowHBranchA * P ∧ P.natDegree ≤ p - 8 ∧
      (∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) := by
  have hends := lowHEulerDelta_four_ends p hp d (by omega) hband H hH
  obtain ⟨R, hR⟩ := lowH_four_ends_divisibility p hp _ hends.1 hends.2.1 hends.2.2.1 hends.2.2.2
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  let P : K[X] := C (-(1 / 4 : K)) * R
  have hs : (-4 : K) * -(1 / 4) = 1 := by field_simp [h4]
  have hc := congrArg (C : K →+* K[X]) hs
  simp only [map_mul, map_one] at hc
  have he : lowHEulerDelta p H = lowHBranchA * P := by
    rw [hR, lowHBranchA_factor p hp]
    dsimp only [P]
    linear_combination -lowHBranchQuartic * R * hc
  have ha : (lowHBranchA : K[X]) ≠ 0 := by
    intro hz
    have hh := lowHBranchA_degree (K := K) p hp
    rw [hz, natDegree_zero] at hh
    omega
  have hpdeg : P.natDegree ≤ p - 8 := by
    by_cases hp0 : P = 0
    · simp only [hp0, natDegree_zero]; omega
    · have hh := congrArg natDegree he
      rw [natDegree_mul ha hp0, lowHBranchA_degree p hp] at hh
      have hdelt := lowHEulerDelta_degree p hp d (by omega) hband H hH
      omega
  have hpodd : P.comp (-X) = -P := by
    apply mul_left_cancel₀ ha
    calc
      lowHBranchA * P.comp (-X) = (lowHBranchA * P).comp (-X) := by
        symm
        rw [mul_comp, lowHBranchA_even]
      _ = (lowHEulerDelta p H).comp (-X) := by rw [he]
      _ = -lowHEulerDelta p H := lowHEulerDelta_odd p hp d (by omega) hband H hH
      _ = lowHBranchA * -P := by rw [he]; ring
  exact ⟨P, he, hpdeg, lowH_odd_even_coeff p hp P hpodd⟩

theorem lowH_prime_six_band (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 ≤ p / 6 ∧ 6 * (p / 6) < p := by
  have ho := (Fact.out : p.Prime).eq_two_or_odd
  rcases ho with he | ho
  · omega
  · omega

/-- The original all-prime low degree creates the required conic source without a new endpoint premise. -/
theorem lowHEulerDelta_full_conic_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (η : K) :
    ∃ P : K[X], lowHEulerDelta p H = lowHBranchA * P ∧ P.natDegree ≤ p - 8 ∧
      D (lowHUnitLaurentPrimitive (lowHConicPullback η P)) = lowHConicPullback η P := by
  have hb := lowH_prime_six_band p hp
  obtain ⟨P, he, hd, ho⟩ := lowHEulerDelta_conic_source p hp (p / 6) hb.1 hb.2 H hH
  exact ⟨P, he, hd, lowHConicPullback_primitive p hp η P hd ho⟩

end WPFieldAssembly.ActualBpairContraction
