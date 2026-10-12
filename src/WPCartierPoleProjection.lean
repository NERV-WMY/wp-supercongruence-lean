import WPRationalCartier

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPRationalCartier

namespace WPCartierPoleProjection

variable (p : ℕ) [Fact p.Prime]

private theorem variable_ne_zero : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

private theorem pole_ne_zero (a : ZMod p) :
    (RatFunc.X : RatFunc (ZMod p)) - RatFunc.C a ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)
  simpa using h

theorem selected_power (k : ℤ) :
    rationalCartier p (RatFunc.X ^ ((p : ℤ) * (k + 1) - 1)) = RatFunc.X ^ k := by
  have h := congrArg (evaluate p)
    (WPFiniteCartier.cartier_selected_monomial p (Fact.out : p.Prime).pos (1 : ZMod p) k)
  rw [← rationalCartier_evaluate] at h
  simpa using h

theorem unselected_power (n : ℤ) (hn : ¬(p : ℤ) ∣ n + 1) :
    rationalCartier p (RatFunc.X ^ n) = 0 := by
  have h := congrArg (evaluate p)
    (WPFiniteCartier.cartier_unselected_monomial p (Fact.out : p.Prime).pos (1 : ZMod p) n hn)
  rw [← rationalCartier_evaluate] at h
  simpa using h

theorem first_positive_band (n : ℕ) (hn : n + 1 < 2 * p) :
    rationalCartier p (RatFunc.X ^ n) = if n + 1 = p then 1 else 0 := by
  have hpz : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases he : n + 1 = p
  · rw [if_pos he]
    have hi : (n : ℤ) = (p : ℤ) * (0 + 1) - 1 := by omega
    have h := selected_power p 0
    rw [← hi] at h
    simpa using h
  · rw [if_neg he]
    have hnot : ¬(p : ℤ) ∣ (n : ℤ) + 1 := by
      rintro ⟨b, hb⟩
      have hbpos : 0 < b := by by_contra h; nlinarith
      have hblt : b < 2 := by
        have hnz : (n : ℤ) + 1 < 2 * (p : ℤ) := by exact_mod_cast hn
        by_contra h
        nlinarith
      have hb1 : b = 1 := by omega
      subst b
      apply he
      omega
    simpa only [zpow_natCast] using unselected_power p (n : ℤ) hnot

/-- Full signed-power recurrence at the literal simple pole. -/
theorem pole_power_step (a : ZMod p) (n : ℤ) :
    rationalCartier p (RatFunc.X ^ (n + 1) / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a * rationalCartier p (RatFunc.X ^ n / (RatFunc.X - RatFunc.C a)) +
      rationalCartier p (RatFunc.X ^ n) := by
  have hx := variable_ne_zero p
  have hz : (RatFunc.X : RatFunc (ZMod p)) ^ (n + 1) = RatFunc.X ^ n * RatFunc.X := by
    rw [zpow_add₀ hx, zpow_one]
  have hfrac : (RatFunc.X : RatFunc (ZMod p)) ^ (n + 1) /
      (RatFunc.X - RatFunc.C a) =
      RatFunc.C a * (RatFunc.X ^ n / (RatFunc.X - RatFunc.C a)) + RatFunc.X ^ n := by
    rw [hz]
    field_simp [pole_ne_zero p a]
    ring
  rw [hfrac, rationalCartier_add, rationalCartier_const_mul]

/-- Every positive monomial below 2p retains its complete pole and high-band constant. -/
theorem pole_positive_band (a : ZMod p) (n : ℕ) (hn : n < 2 * p) :
    rationalCartier p (RatFunc.X ^ n / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ n / (RatFunc.X - RatFunc.C a) +
        if p ≤ n then RatFunc.C a ^ (n - p) else 0 := by
  revert hn
  induction n with
  | zero =>
    intro _
    have hp : ¬p ≤ 0 := by have := (Fact.out : p.Prime).pos; omega
    simp only [pow_zero, if_neg hp, add_zero]
    exact rationalCartier_simple_pole p a
  | succ n ih =>
    intro hn
    have hn0 : n < 2 * p := by omega
    have hstep := pole_power_step p a (n : ℤ)
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega] at hstep
    simp only [zpow_natCast] at hstep
    rw [hstep, ih hn0, first_positive_band p n (by omega)]
    by_cases hsmall : n + 1 < p
    · have h1 : ¬p ≤ n := by omega
      have h2 : ¬p ≤ n + 1 := by omega
      have he : n + 1 ≠ p := by omega
      simp only [if_neg h1, if_neg h2, if_neg he, add_zero, pow_succ]
      ring
    · by_cases he : n + 1 = p
      · have h1 : ¬p ≤ n := by omega
        have h2 : p ≤ n + 1 := by omega
        rw [if_neg h1, if_pos h2, if_pos he]
        rw [show n + 1 - p = 0 by omega, pow_zero, pow_succ]
        ring
      · have h1 : p ≤ n := by omega
        have h2 : p ≤ n + 1 := by omega
        rw [if_pos h1, if_pos h2, if_neg he,
          show n + 1 - p = n - p + 1 by omega, pow_succ, pow_succ]
        ring

theorem first_negative_band (n : ℕ) (hn : 0 < n) (hnp : n < p) :
    rationalCartier p (RatFunc.X ^ (-(n : ℤ))) =
      if n = 1 then RatFunc.X ^ (-1 : ℤ) else 0 := by
  have hpz : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases he : n = 1
  · subst n
    simpa using selected_power p (-1)
  · rw [if_neg he]
    apply unselected_power
    rintro ⟨b, hb⟩
    have hnz : (n : ℤ) < (p : ℤ) := by exact_mod_cast hnp
    have hnz1 : 1 < (n : ℤ) := by omega
    have hbneg : b < 0 := by by_contra h; nlinarith
    have hblow : -1 < b := by by_contra h; nlinarith
    omega

private theorem pole_negative_succ (a : ZMod p) (ha : a ≠ 0) (k : ℕ)
    (hnp : k + 1 < p) :
    rationalCartier p (RatFunc.X ^ (-((k + 1 : ℕ) : ℤ)) /
        (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ (-((k + 1 : ℕ) : ℤ)) / (RatFunc.X - RatFunc.C a) -
        RatFunc.C a ^ (-((k + 1 : ℕ) : ℤ)) / RatFunc.X := by
  have haR : (RatFunc.C a : RatFunc (ZMod p)) ≠ 0 := by
    intro h
    apply ha
    exact RatFunc.C.injective (by simpa using h)
  revert hnp
  induction k with
  | zero =>
    intro hn
    have hs := pole_power_step p a (-1)
    norm_num only [Int.reduceNeg, Int.reduceAdd, zpow_zero] at hs
    rw [rationalCartier_simple_pole] at hs
    have hlog : rationalCartier p (RatFunc.X ^ (-1 : ℤ)) = RatFunc.X ^ (-1 : ℤ) := by
      simpa using selected_power p (-1)
    rw [hlog, zpow_neg_one] at hs
    change rationalCartier p (RatFunc.X ^ (-1 : ℤ) / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ (-1 : ℤ) / (RatFunc.X - RatFunc.C a) -
        RatFunc.C a ^ (-1 : ℤ) / RatFunc.X
    apply mul_left_cancel₀ haR
    simp only [zpow_neg_one]
    rw [mul_sub, ← mul_div_assoc, ← mul_div_assoc, mul_inv_cancel₀ haR]
    linear_combination -hs
  | succ k ih =>
    intro hn
    have hn0 : k + 1 < p := by omega
    have hs := pole_power_step p a (-((k + 2 : ℕ) : ℤ))
    rw [show (-((k + 2 : ℕ) : ℤ)) + 1 = -((k + 1 : ℕ) : ℤ) by omega,
      ih hn0] at hs
    have hmono := first_negative_band p (k + 2) (by omega) (by omega)
    rw [if_neg (show k + 2 ≠ 1 by omega)] at hmono
    rw [hmono, add_zero] at hs
    have hpow : (RatFunc.C a : RatFunc (ZMod p)) *
        RatFunc.C a ^ (-((k + 2 : ℕ) : ℤ)) =
        RatFunc.C a ^ (-((k + 1 : ℕ) : ℤ)) := by
      calc
        _ = RatFunc.C a ^ ((1 : ℤ) + (-((k + 2 : ℕ) : ℤ))) := by
          rw [zpow_add₀ haR, zpow_one]
        _ = _ := congrArg (fun j : ℤ => (RatFunc.C a : RatFunc (ZMod p)) ^ j) (by omega)
    apply mul_left_cancel₀ haR
    rw [mul_sub, ← mul_div_assoc, ← mul_div_assoc, hpow]
    exact hs.symm

/-- Every negative monomial above -p retains its pole and the full x^-1 projection. -/
theorem pole_negative_band (a : ZMod p) (ha : a ≠ 0) (n : ℕ)
    (hn : 0 < n) (hnp : n < p) :
    rationalCartier p (RatFunc.X ^ (-(n : ℤ)) / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ (-(n : ℤ)) / (RatFunc.X - RatFunc.C a) -
        RatFunc.C a ^ (-(n : ℤ)) / RatFunc.X := by
  cases n with
  | zero => omega
  | succ k => exact pole_negative_succ p a ha k hnp

/-- The full Laurent band, with both projections expressed before coefficient summation. -/
theorem pole_signed_band (a : ZMod p) (ha : a ≠ 0) (j : ℤ)
    (hlo : -(p : ℤ) < j) (hhi : j < 2 * (p : ℤ)) :
    rationalCartier p (RatFunc.X ^ j / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ j / (RatFunc.X - RatFunc.C a) -
        (if j < 0 then RatFunc.C a ^ j else 0) / RatFunc.X +
        (if (p : ℤ) ≤ j then RatFunc.C a ^ j else 0) / RatFunc.C a := by
  have haR : (RatFunc.C a : RatFunc (ZMod p)) ≠ 0 := by
    intro h
    exact ha (RatFunc.C.injective (by simpa using h))
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast] at hlo hhi
    have hneg : ¬(n : ℤ) < 0 := by omega
    have hnhi : n < 2 * p := by omega
    simp only [Int.ofNat_eq_natCast, if_neg hneg, zero_div, sub_zero, zpow_natCast]
    rw [pole_positive_band p a n hnhi]
    by_cases hn : p ≤ n
    · have hnp : (p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      rw [if_pos hn, if_pos hnp]
      congr 1
      apply (eq_div_iff haR).mpr
      have hcard : (RatFunc.C a : RatFunc (ZMod p)) ^ p = RatFunc.C a := by
        rw [← map_pow, ZMod.pow_card]
      calc
        _ = RatFunc.C a ^ (n - p) * RatFunc.C a ^ p :=
          congrArg (fun z : RatFunc (ZMod p) => RatFunc.C a ^ (n - p) * z) hcard.symm
        _ = RatFunc.C a ^ (n - p + p) := by rw [pow_add]
        _ = _ := by rw [Nat.sub_add_cancel hn]
    · have hnp : ¬(p : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      rw [if_neg hn, if_neg hnp, zero_div]
  | negSucc n =>
    have hn : n + 1 < p := by omega
    change rationalCartier p (RatFunc.X ^ (-((n + 1 : ℕ) : ℤ)) /
        (RatFunc.X - RatFunc.C a)) =
      RatFunc.C a ^ (-((n + 1 : ℕ) : ℤ)) / (RatFunc.X - RatFunc.C a) -
        (if -((n + 1 : ℕ) : ℤ) < 0 then RatFunc.C a ^ (-((n + 1 : ℕ) : ℤ)) else 0) /
          RatFunc.X +
        (if (p : ℤ) ≤ -((n + 1 : ℕ) : ℤ) then
          RatFunc.C a ^ (-((n + 1 : ℕ) : ℤ)) else 0) / RatFunc.C a
    rw [if_pos (show -((n + 1 : ℕ) : ℤ) < 0 by omega),
      if_neg (show ¬(p : ℤ) ≤ -((n + 1 : ℕ) : ℤ) by omega), zero_div, add_zero]
    exact pole_negative_band p a ha (n + 1) (by omega) hn

theorem rationalCartier_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc (ZMod p)) :
    rationalCartier p (∑ i ∈ s, f i) = ∑ i ∈ s, rationalCartier p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, rationalCartier_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, rationalCartier_add, ih]

theorem laurent_expansion (A : (ZMod p)[T;T⁻¹]) :
    A = ∑ j ∈ A.coeff.support, C (A.coeff j) * T j := by
  classical
  ext k
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finset.sum_apply']
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _hb hbk
    simp [hbk]
  · intro hk
    simpa using (Finsupp.notMem_support_iff.mp hk)

/-- Evaluation of every retained coefficient, including negative powers. -/
noncomputable def valueAt (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) : ZMod p :=
  ∑ j ∈ A.coeff.support, A.coeff j * a ^ j

/-- The entire negative half; no coefficient is replaced by a first jet. -/
noncomputable def negativeValue (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) : ZMod p :=
  ∑ j ∈ A.coeff.support, if j < 0 then A.coeff j * a ^ j else 0

/-- The entire high half beginning at p, retained before the fixed scalar is collected. -/
noncomputable def highValue (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) : ZMod p :=
  ∑ j ∈ A.coeff.support, if (p : ℤ) ≤ j then A.coeff j * a ^ j else 0

theorem evaluated_quotient_expansion (A : (ZMod p)[T;T⁻¹]) (D : RatFunc (ZMod p)) :
    evaluate p A / D =
      ∑ j ∈ A.coeff.support, RatFunc.C (A.coeff j) * RatFunc.X ^ j / D := by
  conv_lhs => rw [laurent_expansion p A, map_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [evaluate_monomial]

/-- The whole finite Laurent polynomial at a simple pole, including both signed halves. -/
theorem pole_laurent_band (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) (ha : a ≠ 0)
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ)) :
    rationalCartier p (evaluate p A / (RatFunc.X - RatFunc.C a)) =
      RatFunc.C (valueAt p A a) / (RatFunc.X - RatFunc.C a) -
        RatFunc.C (negativeValue p A a) / RatFunc.X +
        RatFunc.C (highValue p A a) / RatFunc.C a := by
  rw [evaluated_quotient_expansion, rationalCartier_sum]
  calc
    _ = ∑ j ∈ A.coeff.support, RatFunc.C (A.coeff j) *
        (RatFunc.C a ^ j / (RatFunc.X - RatFunc.C a) -
          (if j < 0 then RatFunc.C a ^ j else 0) / RatFunc.X +
          (if (p : ℤ) ≤ j then RatFunc.C a ^ j else 0) / RatFunc.C a) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_div_assoc, rationalCartier_const_mul,
        pole_signed_band p a ha j (hband j hj).1 (hband j hj).2]
    _ = _ := by
      unfold valueAt negativeValue highValue
      simp only [map_sum, map_mul, map_zpow₀, apply_ite, map_zero]
      simp_rw [mul_add, mul_sub, ← mul_div_assoc, mul_ite, mul_zero]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.sum_div]

/-- Both omitted resonance slots really vanish in the complete logarithmic x^-1 term. -/
theorem zero_logarithmic_projection (A : (ZMod p)[T;T⁻¹])
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hp : A.coeff (p : ℤ) = 0) :
    rationalCartier p (evaluate p A / RatFunc.X) = 0 := by
  rw [evaluated_quotient_expansion, rationalCartier_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hpz : 0 < (p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnot : ¬(p : ℤ) ∣ (j - 1) + 1 := by
    rintro ⟨b, hb⟩
    have hprod : j = (p : ℤ) * b := by linarith
    have hblow : -1 < b := by have := (hband j hj).1; by_contra h; nlinarith
    have hbhigh : b < 2 := by have := (hband j hj).2; by_contra h; nlinarith
    have hnon := Finsupp.mem_support_iff.mp hj
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · have hj0 : j = 0 := by linarith
      exact hnon (by rw [hj0, h0])
    · have hjp : j = (p : ℤ) := by linarith
      exact hnon (by rw [hjp, hp])
  have hpower : (RatFunc.X : RatFunc (ZMod p)) ^ j / RatFunc.X =
      RatFunc.X ^ (j - 1) := by
    rw [zpow_sub₀ (variable_ne_zero p), zpow_one]
  rw [mul_div_assoc, hpower, rationalCartier_const_mul,
    unselected_power p (j - 1) hnot, mul_zero]

/-- NC65's complete two-pole differential, with both full Laurent projections retained. -/
theorem two_pole_projection (A : (ZMod p)[T;T⁻¹]) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hp : A.coeff (p : ℤ) = 0) :
    rationalCartier p (evaluate p A *
      (2 / (RatFunc.X - RatFunc.C a) + 1 / (RatFunc.X - RatFunc.C b) -
        1 / (2 * RatFunc.X))) =
      2 * RatFunc.C (valueAt p A a) / (RatFunc.X - RatFunc.C a) +
        RatFunc.C (valueAt p A b) / (RatFunc.X - RatFunc.C b) +
        RatFunc.C (-2 * negativeValue p A a - negativeValue p A b) / RatFunc.X +
        RatFunc.C (2 * highValue p A a / a + highValue p A b / b) := by
  have hinput : evaluate p A *
      (2 / (RatFunc.X - RatFunc.C a) + 1 / (RatFunc.X - RatFunc.C b) -
        1 / (2 * RatFunc.X)) =
      RatFunc.C (2 : ZMod p) * (evaluate p A / (RatFunc.X - RatFunc.C a)) +
        evaluate p A / (RatFunc.X - RatFunc.C b) -
        RatFunc.C (1 / 2 : ZMod p) * (evaluate p A / RatFunc.X) := by
    have hhalf : RatFunc.C (1 / 2 : ZMod p) = (1 / 2 : RatFunc (ZMod p)) := by
      rw [map_div₀, map_one, map_ofNat]
    rw [hhalf]
    simp only [map_ofNat, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hinput, rationalCartier_sub, rationalCartier_add, rationalCartier_const_mul,
    rationalCartier_const_mul, zero_logarithmic_projection p A hband h0 hp,
    pole_laurent_band p A a ha hband, pole_laurent_band p A b hb hband]
  simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_div₀,
    mul_zero, sub_zero]
  ring

/-- The literal NC65 locations 1/4 and 4, with c and d computed from the full halves. -/
theorem literal_two_pole_projection (hp : 7 ≤ p) (A : (ZMod p)[T;T⁻¹])
    (hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ))
    (h0 : A.coeff 0 = 0) (hslot : A.coeff (p : ℤ) = 0) :
    rationalCartier p (evaluate p A *
      (2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
        1 / (RatFunc.X - RatFunc.C (4 : ZMod p)) - 1 / (2 * RatFunc.X))) =
      2 * RatFunc.C (valueAt p A (1 / 4)) /
          (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
        RatFunc.C (valueAt p A 4) / (RatFunc.X - RatFunc.C (4 : ZMod p)) +
        RatFunc.C (-2 * negativeValue p A (1 / 4) - negativeValue p A 4) / RatFunc.X +
        RatFunc.C (8 * highValue p A (1 / 4) + highValue p A 4 / 4) := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
    have hle := Nat.le_of_dvd (show 0 < 4 by omega) hd
    omega
  have ha : (1 / 4 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h4
  have h := two_pole_projection p A (1 / 4) 4 ha h4 hband h0 hslot
  have hd : (2 * highValue p A (1 / 4) / (1 / 4) + highValue p A 4 / 4 : ZMod p) =
      8 * highValue p A (1 / 4) + highValue p A 4 / 4 := by
    field_simp [h4]
    ring
  simpa only [hd] using h

end WPCartierPoleProjection
