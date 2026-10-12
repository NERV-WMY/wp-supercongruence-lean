import WPActualFieldPrimitive

open scoped BigOperators Polynomial LaurentPolynomial Classical
open LaurentPolynomial WPActualFieldPrimitive WPActualPositivePair
  WPActualEtaFieldCutoff WPActualCanonicalProjection WPCartierPoleProjection

namespace WPActualCanonicalFinitePart

variable (p : ℕ) [Fact p.Prime]

theorem toLaurent_coeff_nat (P : (ZMod p)[X]) (n : ℕ) :
    P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  have h := Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective
    P.toFinsupp.coeff n
  simpa only [Nat.castEmbedding_apply, Polynomial.toFinsupp_apply] using h

theorem fieldPrimitive_sub (P Q : (ZMod p)[T;T⁻¹]) :
    fieldPrimitive p (P - Q) = fieldPrimitive p P - fieldPrimitive p Q := by
  ext j
  simp only [fieldPrimitive_coeff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  split_ifs <;> ring

theorem fieldPrimitive_fieldDerivative_coeff (P : (ZMod p)[T;T⁻¹]) (j : ℤ) :
    (fieldPrimitive p (fieldDerivative p P)).coeff j =
      if (p : ℤ) ∣ j then 0 else P.coeff j := by
  rw [fieldPrimitive_coeff, fieldDerivative_coeff,
    show j - 1 + 1 = j by omega]
  by_cases hd : (p : ℤ) ∣ j
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd]
    have hj : (j : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hd
    field_simp [hj]

theorem fieldDerivative_toLaurent (P : (ZMod p)[X]) :
    fieldDerivative p (Polynomial.toLaurent P) = Polynomial.toLaurent P.derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [Polynomial.toLaurent_C_mul_T, fieldDerivative_monomial]
    cases n with
    | zero => simp
    | succ n =>
      rw [Polynomial.derivative_monomial, Polynomial.toLaurent_C_mul_T]
      apply congrArg₂ (fun a b => C a * T b)
      · push_cast
        ring
      · omega

/-- The whole polynomial primitive deletes exactly its original 0 and p slots. -/
theorem polynomial_unit_primitive (P : (ZMod p)[X]) (hdeg : P.natDegree < 2 * p) :
    fieldPrimitive p (fieldDerivative p (Polynomial.toLaurent P)) =
      Polynomial.toLaurent P - C (P.coeff 0) - C (P.coeff p) * T (p : ℤ) := by
  have hm (c : ZMod p) (n j : ℤ) : (C c * T n).coeff j = if n = j then c else 0 := by
    rw [← single_eq_C_mul_T]
    exact Finsupp.single_apply
  have hc (c : ZMod p) (j : ℤ) : (C c).coeff j = if 0 = j then c else 0 := by
    simpa only [T_zero, mul_one] using hm c 0 j
  ext j
  rw [fieldPrimitive_fieldDerivative_coeff, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finsupp.sub_apply, hc, hm]
  by_cases hj0 : j = 0
  · subst j
    rw [if_pos (dvd_zero (p : ℤ)),
      show (Polynomial.toLaurent P).coeff (0 : ℤ) = P.coeff 0 from toLaurent_coeff_nat p P 0]
    rw [if_neg (by have := (Fact.out : p.Prime).pos; omega : (p : ℤ) ≠ 0)]
    simp only [if_true, sub_self]
  · rw [if_neg (Ne.symm hj0)]
    by_cases hjp : j = (p : ℤ)
    · subst j
      simp only [dvd_refl, if_true, toLaurent_coeff_nat, sub_zero, sub_self]
    · rw [if_neg (Ne.symm hjp), sub_zero, sub_zero]
      by_cases hd : (p : ℤ) ∣ j
      · rw [if_pos hd]
        by_contra hz
        have hs : j ∈ (Polynomial.toLaurent P).coeff.support :=
          Finsupp.mem_support_iff.mpr (Ne.symm hz)
        rw [support_coeff_toLaurent] at hs
        obtain ⟨n, hn, he⟩ := Finset.mem_map.mp hs
        have hnP := Polynomial.le_natDegree_of_mem_supp n hn
        change (n : ℤ) = j at he
        obtain ⟨k, hk⟩ := hd
        have hpos : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
        have hnonneg : 0 ≤ j := by omega
        have hupper : j < 2 * (p : ℤ) := by omega
        have hk0 : 0 ≤ k := by nlinarith
        have hk2 : k < 2 := by nlinarith
        have : k = 0 ∨ k = 1 := by omega
        rcases this with hkz | hko
        · simp only [hkz, mul_zero] at hk
          exact hj0 hk
        · simp only [hko, mul_one] at hk
          exact hjp hk
      · rw [if_neg hd]

/-- The literal original cubic pullback used in NC71. -/
noncomputable def pullbackPolynomial (G : (ZMod p)[X]) : (ZMod p)[X] :=
  G.comp (WPHasseIntegralTransport.fieldV p)

theorem pullbackPolynomial_degree (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) :
    (pullbackPolynomial p G).natDegree < 2 * p := by
  have hV : (WPHasseIntegralTransport.fieldV p).natDegree ≤ 3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  have h := Polynomial.natDegree_comp_le (p := G) (q := WPHasseIntegralTransport.fieldV p)
  have hh := Nat.mul_le_mul hdeg hV
  exact (h.trans hh).trans_lt (by omega)

/-- The remainder is selected from the full actual source, before any endpoint values. -/
noncomputable def literalRemainder (hp : 19 ≤ p) (G : (ZMod p)[X]) :
    (ZMod p)[T;T⁻¹] :=
  fieldPrimitive p (literalFieldPeta p hp - C (1 / 6) *
    fieldDerivative p (Polynomial.toLaurent (pullbackPolynomial p G)))

theorem literalRemainder_resonant_zero (hp : 19 ≤ p) (G : (ZMod p)[X]) (k : ℤ) :
    (literalRemainder p hp G).coeff (k * p) = 0 :=
  fieldPrimitive_resonant_zero p _ k

/-- Original NC71 decomposition, preserving the actual constant and Frobenius coefficients. -/
theorem literal_canonical_decomposition (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) :
    literalFieldAeta p hp = literalRemainder p hp G + C (1 / 6) *
      (Polynomial.toLaurent (pullbackPolynomial p G) -
        C ((pullbackPolynomial p G).coeff 0) -
        C ((pullbackPolynomial p G).coeff p) * T (p : ℤ)) := by
  rw [literalRemainder, fieldPrimitive_sub, fieldPrimitive_C_mul,
    polynomial_unit_primitive p _ (pullbackPolynomial_degree p hp G hdeg),
    ← literal_field_Aeta_primitive, sub_add_cancel]

theorem fieldDerivative_C_mul (c : ZMod p) (P : (ZMod p)[T;T⁻¹]) :
    fieldDerivative p (C c * P) = C c * fieldDerivative p P := by
  have hc (Q : (ZMod p)[T;T⁻¹]) (j : ℤ) : (C c * Q).coeff j = c * Q.coeff j := by
    rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  ext j
  rw [fieldDerivative_coeff, hc, hc, fieldDerivative_coeff]
  ring

theorem fieldDerivative_constant (c : ZMod p) : fieldDerivative p (C c) = 0 := by
  have h := fieldDerivative_monomial p c 0
  simpa only [T_zero, mul_one, Int.cast_zero, mul_zero, map_zero, zero_mul] using h

theorem fieldDerivative_frobenius (c : ZMod p) :
    fieldDerivative p (C c * T (p : ℤ)) = 0 := by
  rw [fieldDerivative_monomial]
  simp

/-- The actual remainder source still retains its central logarithmic coefficient. -/
theorem literalRemainder_source (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) :
    fieldDerivative p (literalRemainder p hp G) =
      literalFieldPeta p hp -
        C (WPActualEtaPrimitive.actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0 : ZMod p) *
          T (-1) - C (1 / 6) *
        fieldDerivative p (Polynomial.toLaurent (pullbackPolynomial p G)) := by
  have h := congrArg (fieldDerivative p) (literal_canonical_decomposition p hp G hdeg)
  rw [literal_field_Aeta_central_source] at h
  rw [map_add, fieldDerivative_C_mul, map_sub, map_sub, fieldDerivative_constant,
    fieldDerivative_frobenius, sub_zero, sub_zero] at h
  rw [h, add_sub_cancel_right]

/-- Linear evaluation on an explicitly specified entire coefficient band. -/
noncomputable def coefficientValue (q : ℤ → Prop) (a : ZMod p) :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p := by
  classical
  exact (Finsupp.linearCombination (ZMod p) (fun j : ℤ => if q j then a ^ j else 0)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem coefficientValue_expansion (q : ℤ → Prop) (a : ZMod p) (A : (ZMod p)[T;T⁻¹]) :
    coefficientValue p q a A =
      ∑ j ∈ A.coeff.support, if q j then A.coeff j * a ^ j else 0 := by
  classical
  change Finsupp.linearCombination (ZMod p) _ A.coeff = _
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : q j <;> simp [hj, smul_eq_mul]

theorem coefficientValue_monomial (q : ℤ → Prop) (a c : ZMod p) (n : ℤ) :
    coefficientValue p q a (C c * T n) = if q n then c * a ^ n else 0 := by
  classical
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single n c) = _
  rw [Finsupp.linearCombination_single]
  by_cases hn : q n <;> simp [hn, smul_eq_mul]

theorem valueAt_linear (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) :
    valueAt p A a = coefficientValue p (fun _ => True) a A := by
  rw [coefficientValue_expansion]
  simp only [if_true, valueAt]

theorem negativeValue_linear (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) :
    negativeValue p A a = coefficientValue p (fun j => j < 0) a A := by
  rw [coefficientValue_expansion]
  unfold negativeValue
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < 0 <;> simp [hj]

theorem highValue_linear (A : (ZMod p)[T;T⁻¹]) (a : ZMod p) :
    highValue p A a = coefficientValue p (fun j => (p : ℤ) ≤ j) a A := by
  rw [coefficientValue_expansion]
  unfold highValue
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (p : ℤ) ≤ j <;> simp [hj]

/-- The entire original four-term NC67 functional, as a coefficient-linear map. -/
noncomputable def canonicalProjection : (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (1044 / 625 : ZMod p) • coefficientValue p (fun _ => True) (1 / 4) -
    (828 / 625 : ZMod p) • coefficientValue p (fun _ => True) 4 +
    (432 / 625 : ZMod p) • ((-2 : ZMod p) • coefficientValue p (fun j => j < 0) (1 / 4) -
      coefficientValue p (fun j => j < 0) 4) +
    (6102 / 4375 : ZMod p) • ((8 : ZMod p) • coefficientValue p (fun j => (p : ℤ) ≤ j) (1 / 4) +
      (1 / 4 : ZMod p) • coefficientValue p (fun j => (p : ℤ) ≤ j) 4)

theorem canonicalProjection_formula (A : (ZMod p)[T;T⁻¹]) :
    canonicalProjection p A = (1044 / 625) * valueAt p A (1 / 4) -
      (828 / 625) * valueAt p A 4 +
      (432 / 625) * (-2 * negativeValue p A (1 / 4) - negativeValue p A 4) +
      (6102 / 4375) * (8 * highValue p A (1 / 4) + highValue p A 4 / 4) := by
  rw [valueAt_linear, valueAt_linear, negativeValue_linear, negativeValue_linear,
    highValue_linear, highValue_linear]
  simp only [canonicalProjection, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

theorem literal_canonicalPeriod_projection (hp : 19 ≤ p) :
    (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      canonicalProjection p (literalFieldAeta p hp) := by
  rw [canonicalProjection_formula, literal_canonicalPeriod_NC67 p hp]

theorem canonicalProjection_monomial (c : ZMod p) (n : ℤ) :
    canonicalProjection p (C c * T n) = c *
      ((1044 / 625) * (1 / 4 : ZMod p) ^ n - (828 / 625) * (4 : ZMod p) ^ n +
        (432 / 625) * (if n < 0 then -2 * (1 / 4 : ZMod p) ^ n - (4 : ZMod p) ^ n else 0) +
        (6102 / 4375) * (if (p : ℤ) ≤ n then
          8 * (1 / 4 : ZMod p) ^ n + (4 : ZMod p) ^ n / 4 else 0)) := by
  simp only [canonicalProjection, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, coefficientValue_monomial, if_true]
  split_ifs <;> ring

private theorem small_unit (n : ℕ) (hn : 0 < n) (hnp : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro h
  have hd := (ZMod.natCast_eq_zero_iff n p).mp h
  have := Nat.le_of_dvd hn hd
  omega

private theorem projection_units (hp : 19 ≤ p) :
    (4 : ZMod p) ≠ 0 ∧ (6 : ZMod p) ≠ 0 ∧ (625 : ZMod p) ≠ 0 ∧
      (4375 : ZMod p) ≠ 0 ∧ (8750 : ZMod p) ≠ 0 := by
  have h2 := small_unit p 2 (by norm_num) (by omega)
  have h3 := small_unit p 3 (by norm_num) (by omega)
  have h5 := small_unit p 5 (by norm_num) (by omega)
  have h7 := small_unit p 7 (by norm_num) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h6 : (6 : ZMod p) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; norm_num
  have h625 : (625 : ZMod p) ≠ 0 := by convert pow_ne_zero 4 h5 using 1; norm_num
  have h4375 : (4375 : ZMod p) ≠ 0 := by convert mul_ne_zero h625 h7 using 1; norm_num
  have h8750 : (8750 : ZMod p) ≠ 0 := by convert mul_ne_zero h2 h4375 using 1; norm_num
  exact ⟨h4, h6, h625, h4375, h8750⟩

theorem canonicalProjection_constant (hp : 19 ≤ p) (c : ZMod p) :
    canonicalProjection p (C c) = (216 / 625) * c := by
  have h := canonicalProjection_monomial p c 0
  have hpos : ¬(p : ℤ) ≤ 0 := by omega
  simp only [T_zero, mul_one, zpow_zero, show ¬(0 : ℤ) < 0 by omega, if_false, hpos, mul_zero,
    add_zero] at h
  rw [h]
  have hu := (projection_units p hp).2.2.1
  field_simp [hu]
  ring

theorem canonicalProjection_frobenius (hp : 19 ≤ p) (c : ZMod p) :
    canonicalProjection p (C c * T (p : ℤ)) = -(3051 / 4375) * c := by
  rw [canonicalProjection_monomial]
  have hnonneg : ¬(p : ℤ) < 0 := by omega
  simp only [if_neg hnonneg, le_refl, if_true, mul_zero, add_zero, zpow_natCast,
    ZMod.pow_card]
  have hu := projection_units p hp
  field_simp [hu.1, hu.2.2.1, hu.2.2.2.1]
  ring

theorem pullback_endpoints (hp : 19 ≤ p) (G : (ZMod p)[X]) (hzero : G.coeff 0 = 0) :
    (pullbackPolynomial p G).eval (1 / 4) = 0 ∧ (pullbackPolynomial p G).eval 4 = 0 := by
  have h4 := (projection_units p hp).1
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1 / 4) = 0 := by
    simp only [WPHasseIntegralTransport.fieldV, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_one]
    field_simp [h4]
    ring
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4 = 0 := by
    simp [WPHasseIntegralTransport.fieldV]
  simp only [pullbackPolynomial, Polynomial.eval_comp, hVa, hVb,
    ← Polynomial.coeff_zero_eq_eval_zero, hzero, and_self]

theorem canonicalProjection_pullback (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) (hzero : G.coeff 0 = 0) :
    canonicalProjection p (Polynomial.toLaurent (pullbackPolynomial p G)) = 0 := by
  have h4 := (projection_units p hp).1
  have ha : (1 / 4 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h4
  have he := pullback_endpoints p hp G hzero
  have hh := actual_high_pair_zero p hp G hdeg hzero
  change 8 * highValue p (Polynomial.toLaurent (pullbackPolynomial p G)) (1 / 4) +
    highValue p (Polynomial.toLaurent (pullbackPolynomial p G)) 4 / 4 = 0 at hh
  rw [canonicalProjection_formula, valueAt_toLaurent p _ _ ha,
    valueAt_toLaurent p _ _ h4, he.1, he.2, negativeValue_toLaurent,
    negativeValue_toLaurent, hh]
  ring

/-- Full NC71 projection: no negative/high part of the actual remainder is discarded. -/
theorem literal_canonicalPeriod_finite_part (hp : 19 ≤ p) (G : (ZMod p)[X])
    (hdeg : G.natDegree ≤ (p - 1) / 2) (hzero : G.coeff 0 = 0) :
    (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      canonicalProjection p (literalRemainder p hp G) -
        (36 / 625) * (pullbackPolynomial p G).coeff 0 +
        (1017 / 8750) * (pullbackPolynomial p G).coeff p := by
  rw [literal_canonicalPeriod_projection p hp, literal_canonical_decomposition p hp G hdeg,
    map_add, ← smul_eq_C_mul, map_smul, smul_eq_mul, map_sub, map_sub,
    canonicalProjection_pullback p hp G hdeg hzero,
    canonicalProjection_constant p hp, canonicalProjection_frobenius p hp]
  have hu := projection_units p hp
  field_simp [hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2]
  ring

end WPActualCanonicalFinitePart
