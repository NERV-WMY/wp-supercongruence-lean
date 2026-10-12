import WPActualCanonicalProjection

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPRationalCartier WPFiniteCartier WPCartierPoleProjection
open WPActualCanonicalSource WPActualCanonicalProjection WPQuadraticRationalCartier

namespace WPActualPositivePair

variable (p : ℕ) [Fact p.Prime]

/-- The literal unit-index Euler primitive, with every supported coefficient retained. -/
noncomputable def eulerPrimitive (G : (ZMod p)[X]) : (ZMod p)[X] :=
  ∑ n ∈ G.support, Polynomial.monomial n (G.coeff n / (n : ZMod p))

theorem eulerPrimitive_coeff (G : (ZMod p)[X]) (n : ℕ) :
    (eulerPrimitive p G).coeff n = G.coeff n / (n : ZMod p) := by
  classical
  simp only [eulerPrimitive, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hn
    simp [Polynomial.notMem_support_iff.mp hn]

theorem eulerPrimitive_derivative (G : (ZMod p)[X])
    (hdeg : G.natDegree < p) (hzero : G.coeff 0 = 0) :
    Polynomial.X * (eulerPrimitive p G).derivative = G := by
  ext n
  cases n with
  | zero => simp [hzero]
  | succ n =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, eulerPrimitive_coeff]
    by_cases hc : G.coeff (n + 1) = 0
    · simp [hc]
    · have hn : n + 1 < p := (Polynomial.le_natDegree_of_ne_zero hc).trans_lt hdeg
      have hunit : ((n + 1 : ℕ) : ZMod p) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff (n + 1) p).mp h
        have := Nat.le_of_dvd (by omega : 0 < n + 1) hd
        omega
      have hu : (n : ZMod p) + 1 ≠ 0 := by simpa using hunit
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hu]

/-- Cartier kills the complete derivative, with no degree restriction on its primitive. -/
theorem cartier_polynomial_derivative (P : (ZMod p)[X]) :
    cartier p (Fact.out : p.Prime).pos (Polynomial.toLaurent P.derivative) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.derivative_add, map_add, cartier_add, hP, hQ, add_zero]
  | monomial n c =>
    cases n with
    | zero => simp [cartier_zero]
    | succ n =>
      rw [Polynomial.derivative_monomial, Polynomial.toLaurent_C_mul_T]
      by_cases hd : p ∣ n + 1
      · have hc : (((n + 1 : ℕ) : ZMod p)) = 0 :=
          (ZMod.natCast_eq_zero_iff (n + 1) p).mpr hd
        simp [hc, cartier_zero]
      · apply cartier_unselected_monomial
        intro h
        apply hd
        exact_mod_cast h

theorem rationalCartier_polynomial_derivative (P : (ZMod p)[X]) :
    rationalCartier p (evaluate p (Polynomial.toLaurent P.derivative)) = 0 := by
  rw [rationalCartier_evaluate, cartier_polynomial_derivative, map_zero]

theorem valueAt_eq_evaluation (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) (ha : a ≠ 0) :
    valueAt p A a = LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (Units.mk0 a ha) A := by
  conv_rhs => rw [laurent_expansion p A, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, Units.mk0]

theorem valueAt_toLaurent (P : (ZMod p)[X]) (a : ZMod p) (ha : a ≠ 0) :
    valueAt p (Polynomial.toLaurent P) a = P.eval a := by
  rw [valueAt_eq_evaluation p _ a ha, eval₂_toLaurent]
  rfl

theorem negativeValue_toLaurent (P : (ZMod p)[X]) (a : ZMod p) :
    negativeValue p (Polynomial.toLaurent P) a = 0 := by
  classical
  unfold negativeValue
  apply Finset.sum_eq_zero
  intro j hj
  rw [support_coeff_toLaurent] at hj
  obtain ⟨n, _, hnj⟩ := Finset.mem_map.mp hj
  change (n : ℤ) = j at hnj
  rw [if_neg (by omega : ¬j < 0)]

theorem polynomial_full_band (P : (ZMod p)[X]) (hdeg : P.natDegree < 2 * p)
    (j : ℤ) (hj : j ∈ (Polynomial.toLaurent P).coeff.support) :
    -(p : ℤ) < j ∧ j < 2 * (p : ℤ) := by
  rw [support_coeff_toLaurent] at hj
  obtain ⟨n, hn, hnj⟩ := Finset.mem_map.mp hj
  have h := Polynomial.le_natDegree_of_mem_supp n hn
  change (n : ℤ) = j at hnj
  have := (Fact.out : p.Prime).pos
  omega

private theorem two_ne_zero (hp : 19 ≤ p) : (2 : RatFunc (ZMod p)) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  simpa only [map_ofNat] using (map_ne_zero RatFunc.C).mpr h2

theorem literal_dlogV (hp : 19 ≤ p) :
    2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
        1 / (RatFunc.X - RatFunc.C (4 : ZMod p)) =
      evaluate p (fieldDerivativeVx p) / evaluate p (fieldVx p) := by
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have h2 := two_ne_zero p hp
  have hV := fieldVx_evaluate_ne_zero p hp
  have h := literal_logarithmicX p hp
  unfold WPNC67ActualSources.logarithmicX at h
  simp only [map_sub, map_mul, map_ofNat, evaluate_T, zpow_one] at h
  simp only [map_ofNat]
  apply (eq_div_iff hV).mpr
  apply mul_left_cancel₀ (mul_ne_zero h2 hx)
  field_simp [h2, hx, hV] at h
  linear_combination h

/-- The whole V pullback is an exact differential before any high-half selection. -/
theorem actual_pullback_exact (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree < p) (hzero : G.coeff 0 = 0) :
    evaluate p (Polynomial.toLaurent (G.comp (WPHasseIntegralTransport.fieldV p))) *
        (2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
          1 / (RatFunc.X - RatFunc.C (4 : ZMod p))) =
      evaluate p (Polynomial.toLaurent
        ((eulerPrimitive p G).comp (WPHasseIntegralTransport.fieldV p)).derivative) := by
  have hG := congrArg (fun Q : (ZMod p)[X] => Q.comp (WPHasseIntegralTransport.fieldV p))
    (eulerPrimitive_derivative p G hdeg hzero)
  rw [Polynomial.mul_comp, Polynomial.X_comp] at hG
  rw [literal_dlogV p hp, ← hG, Polynomial.derivative_comp]
  simp only [map_mul]
  change (evaluate p (fieldVx p) *
      evaluate p (Polynomial.toLaurent
        ((eulerPrimitive p G).derivative.comp (WPHasseIntegralTransport.fieldV p)))) *
      (evaluate p (fieldDerivativeVx p) / evaluate p (fieldVx p)) =
    evaluate p (fieldDerivativeVx p) *
      evaluate p (Polynomial.toLaurent
        ((eulerPrimitive p G).derivative.comp (WPHasseIntegralTransport.fieldV p)))
  field_simp [fieldVx_evaluate_ne_zero p hp]

theorem actual_pullback_cartier_zero (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree < p) (hzero : G.coeff 0 = 0) :
    rationalCartier p
      (evaluate p (Polynomial.toLaurent (G.comp (WPHasseIntegralTransport.fieldV p))) *
        (2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
          1 / (RatFunc.X - RatFunc.C (4 : ZMod p)))) = 0 := by
  rw [actual_pullback_exact p hp G hdeg hzero, rationalCartier_polynomial_derivative]

private theorem four_ne_zero (hp : 19 ≤ p) : (4 : ZMod p) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 4 p).mp h
  have := Nat.le_of_dvd (by omega : 0 < 4) hd
  omega

/-- NC77's complete high pair vanishes for the original cubic pullback space. -/
theorem actual_high_pair_zero (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) (hzero : G.coeff 0 = 0) :
    8 * highValue p (Polynomial.toLaurent (G.comp (WPHasseIntegralTransport.fieldV p))) (1 / 4) +
      highValue p (Polynomial.toLaurent (G.comp (WPHasseIntegralTransport.fieldV p))) 4 / 4 = 0 := by
  let P := G.comp (WPHasseIntegralTransport.fieldV p)
  let A := Polynomial.toLaurent P
  have h4 := four_ne_zero p hp
  have ha : (1 / 4 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h4
  have hsmall : G.natDegree < p := by omega
  have hVdeg : (WPHasseIntegralTransport.fieldV p).natDegree ≤ 3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  have hPdeg : P.natDegree < 2 * p := by
    have h := Polynomial.natDegree_comp_le (p := G) (q := WPHasseIntegralTransport.fieldV p)
    have hh := Nat.mul_le_mul hdeg hVdeg
    change (G.comp (WPHasseIntegralTransport.fieldV p)).natDegree < _
    exact (h.trans hh).trans_lt (by omega)
  have hband : ∀ j ∈ A.coeff.support, -(p : ℤ) < j ∧ j < 2 * (p : ℤ) :=
    polynomial_full_band p P hPdeg
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1 / 4) = 0 := by
    have hcoeff : (((1 / 125 : ℚ) : ZMod p)) = 1 / (125 : ZMod p) := by
      simpa only [one_div, Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 125)
    simp only [WPHasseIntegralTransport.fieldV, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_one, hcoeff]
    field_simp [h4]
    ring
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4 = 0 := by
    simp [WPHasseIntegralTransport.fieldV]
  have hAa : valueAt p A (1 / 4) = 0 := by
    rw [valueAt_toLaurent p P _ ha]
    simp only [P, Polynomial.eval_comp, hVa, ← Polynomial.coeff_zero_eq_eval_zero, hzero]
  have hAb : valueAt p A 4 = 0 := by
    rw [valueAt_toLaurent p P _ h4]
    simp only [P, Polynomial.eval_comp, hVb, ← Polynomial.coeff_zero_eq_eval_zero, hzero]
  have hna : negativeValue p A (1 / 4) = 0 := negativeValue_toLaurent p P _
  have hnb : negativeValue p A 4 = 0 := negativeValue_toLaurent p P _
  have hc := actual_pullback_cartier_zero p hp G hsmall hzero
  have he : evaluate p A *
      (2 / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) +
        1 / (RatFunc.X - RatFunc.C (4 : ZMod p))) =
    RatFunc.C (2 : ZMod p) * (evaluate p A / (RatFunc.X - RatFunc.C (1 / 4 : ZMod p))) +
      evaluate p A / (RatFunc.X - RatFunc.C (4 : ZMod p)) := by
    simp only [map_ofNat, div_eq_mul_inv]
    ring
  change rationalCartier p (evaluate p A * _) = 0 at hc
  rw [he, rationalCartier_add, rationalCartier_const_mul,
    pole_laurent_band p A (1 / 4) ha hband, pole_laurent_band p A 4 h4 hband,
    hAa, hAb, hna, hnb] at hc
  simp only [map_zero, zero_div, sub_zero, zero_add, map_ofNat, map_div₀, map_one] at hc
  have hd : RatFunc.C (8 * highValue p A (1 / 4) + highValue p A 4 / 4) = 0 := by
    simp only [map_add, map_mul, map_inv₀, map_ofNat, div_eq_mul_inv, one_mul, inv_inv] at hc ⊢
    convert hc using 1; ring
  exact RatFunc.C.injective (by simpa only [map_zero] using hd)

/-- The literal full truncation below p, not a separately chosen endpoint representative. -/
noncomputable def lowPart (A : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  ∑ j ∈ A.coeff.support, if j < (p : ℤ) then C (A.coeff j) * T j else 0

theorem lowPart_valueAt (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) (ha : a ≠ 0) :
    valueAt p (lowPart p A) a = valueAt p A a - highValue p A a := by
  rw [valueAt_eq_evaluation p _ a ha, lowPart, map_sum]
  unfold valueAt highValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < (p : ℤ)
  · have hn : ¬(p : ℤ) ≤ j := by omega
    simp [hj, hn, eval₂_C_mul_T, Units.val_zpow_eq_zpow_val, Units.mk0]
  · have hn : (p : ℤ) ≤ j := by omega
    simp [hj, hn]

/-- Original NC77a, including all coefficients below p and both actual endpoints. -/
theorem actual_low_pair_zero (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) (hzero : G.coeff 0 = 0) :
    8 * valueAt p (lowPart p (Polynomial.toLaurent
        (G.comp (WPHasseIntegralTransport.fieldV p)))) (1 / 4) +
      valueAt p (lowPart p (Polynomial.toLaurent
        (G.comp (WPHasseIntegralTransport.fieldV p)))) 4 / 4 = 0 := by
  have h4 := four_ne_zero p hp
  have ha : (1 / 4 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h4
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1 / 4) = 0 := by
    simp only [WPHasseIntegralTransport.fieldV, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_one]
    field_simp [h4]
    ring
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4 = 0 := by
    simp [WPHasseIntegralTransport.fieldV]
  rw [lowPart_valueAt p _ (1 / 4) ha, lowPart_valueAt p _ 4 h4,
    valueAt_toLaurent p _ (1 / 4) ha, valueAt_toLaurent p _ 4 h4]
  simp only [Polynomial.eval_comp, hVa, hVb, ← Polynomial.coeff_zero_eq_eval_zero, hzero, zero_sub]
  linear_combination -actual_high_pair_zero p hp G hdeg hzero

end WPActualPositivePair
