import WPFieldAssembly.SourceClosureSigmaWholeCarry

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPFieldAssembly.ActualSigmaFiniteEvenSource WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.SourceClosureSigmaProperJ WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureSigmaWholePrimitive WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaProductCarry WPFieldAssembly.SourceClosureSigmaLogCarry
  WPFieldAssembly.SourceClosureSigmaWholeCarry

namespace WPFieldAssembly.SourceClosureSigmaWholeSupport

set_option maxHeartbeats 1500000

/- The bound is obtained before reduction from the original whole rational
primitive and comparison. Canonical holes remove coefficients; reflection
adds the opposite band and the actual endpoints add only constants. -/

theorem constant_coeff_outside {R : Type*} [CommRing R] (c : R) (j : ℤ)
    (hj : j ≠ 0) : (LaurentPolynomial.C c : R[T;T⁻¹]).coeff j = 0 := by
  have h := coeff_unit_monomial c 0 j
  simpa only [T_zero, mul_one, if_neg (Ne.symm hj)] using h

theorem endSym_support {R : Type*} [CommRing R] (u : Rˣ) (M : ℤ) (hM : 0 ≤ M)
    (F : R[T;T⁻¹])
    (hF : ∀ j, j < -M ∨ M < j → F.coeff j = 0) (j : ℤ)
    (hj : j < -M ∨ M < j) : (endSym u F).coeff j = 0 := by
  have h0 : j ≠ 0 := by omega
  have hneg := hF (-j) (by omega)
  simp only [endSym, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, invert_apply,
    hF j hj, hneg, constant_coeff_outside _ j h0, add_zero, sub_zero]

theorem canSlots_support {R : Type*} [CommRing R] (p : ℕ) (M : ℤ) (hM : (p : ℤ) ≤ M)
    (F : R[T;T⁻¹])
    (hF : ∀ j, j < -M ∨ M < j → F.coeff j = 0) (j : ℤ)
    (hj : j < -M ∨ M < j) : (canSlots p F).coeff j = 0 := by
  have h0 : j ≠ 0 := by omega
  have hpj : (p : ℤ) ≠ j := by omega
  simp only [canSlots, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    hF j hj, constant_coeff_outside _ j h0, coeff_unit_monomial,
    if_neg hpj, sub_zero]

theorem originalAbarQ_degree : (WPFiniteZSource.Abar : ℚ[X]).natDegree ≤ 2 := by
  have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by
    change (4 - X : ℚ[X]).natDegree + (4 * X - 1 : ℚ[X]).natDegree ≤ 2
    omega)

theorem originalWbarQ_degree (p : ℕ) [Fact p.Prime] :
    (originalWbarQ p).natDegree ≤ (p - 1) / 2 := by
  have hs : (WPFiniteWSource.squaredCoordinate : ℚ[X]).natDegree ≤ 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_add_le _ _).trans (by norm_num)
  have hs4 : (4 * WPFiniteWSource.squaredCoordinate : ℚ[X]).natDegree ≤ 1 := by
    change (Polynomial.C (4 : ℚ) * WPFiniteWSource.squaredCoordinate).natDegree ≤ 1
    exact (natDegree_C_mul_le _ _).trans hs
  have he := originalFiniteEvenSquaredQ_degree p
  have h1 := (natDegree_comp_le (p := finiteEvenSquaredQ p)
    (q := (WPFiniteWSource.squaredCoordinate : ℚ[X]))).trans (Nat.mul_le_mul he hs)
  have h4 := (natDegree_comp_le (p := finiteEvenSquaredQ p)
    (q := (4 * WPFiniteWSource.squaredCoordinate : ℚ[X]))).trans (Nat.mul_le_mul he hs4)
  have hE1 : (originalE1CenteredQ p).natDegree ≤ (p - 1) / 2 := by
    unfold originalE1CenteredQ
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa only [mul_one] using h1
    · simpa only [natDegree_C] using (Nat.zero_le ((p - 1) / 2))
  have hE4 : (originalE4CenteredQ p).natDegree ≤ (p - 1) / 2 := by
    unfold originalE4CenteredQ
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa only [mul_one] using h4
    · simpa only [natDegree_C] using (Nat.zero_le ((p - 1) / 2))
  unfold originalWbarQ
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_sub_le _ _).trans (max_le hE4 hE1))

theorem shiftedPolynomialQ_support (c : ℚ) (n : ℤ) (P : ℚ[X]) (j : ℤ)
    (hj : j < n ∨ n + (P.natDegree : ℤ) < j) :
    (LaurentPolynomial.C c * T n * P.toLaurent).coeff j = 0 := by
  rw [WPFiniteJCarrier.shifted_coeff]
  have hz : P.toLaurent.coeff (j - n) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside P (j - n) (by omega)
  rw [hz, mul_zero]

/-- The literal Ract numerator has degree N+2(p-1); no coefficient band is discarded. -/
theorem originalRactQ_support_tight (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -(p : ℤ) ∨ (p : ℤ) + ((p - 1) / 2 : ℕ) - 2 < j) :
    (originalRactQ p).coeff j = 0 := by
  let P : ℚ[X] := (X + 1) ^ ((p - 1) / 2) *
    (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)
  have hX : (X + 1 : ℚ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  have hXP := (natDegree_pow_le (p := (X + 1 : ℚ[X])) (n := (p - 1) / 2)).trans
    (Nat.mul_le_mul_left _ hX)
  have hAP := (natDegree_pow_le (p := (WPFiniteZSource.Abar : ℚ[X])) (n := p - 1)).trans
    (Nat.mul_le_mul_left _ originalAbarQ_degree)
  have hP : P.natDegree ≤ ((p - 1) / 2) + 2 * (p - 1) := by
    exact (natDegree_mul_le (p := (X + 1 : ℚ[X]) ^ ((p - 1) / 2))
      (q := (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1))).trans (by omega)
  have heq : originalRactQ p =
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * P.toLaurent := by
    dsimp only [P, originalRactQ]
    rw [_root_.map_mul, _root_.map_pow, _root_.map_pow]
    ring
  rw [heq]
  apply shiftedPolynomialQ_support
  have hp := (Fact.out : p.Prime).pos
  omega

theorem originalPunitQ_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) : (originalPunitQ p).coeff j = 0 := by
  rw [originalPunitQ, originalJQ_coeff,
    originalRactQ_support_tight p (j - 1) (by omega), mul_zero]

theorem originalKbarWbarQ_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) :
    (originalKbarQ p * (originalWbarQ p).toLaurent).coeff j = 0 := by
  let c : ℚ := 1 / (2 * (5 : ℚ) ^ ((p - 1) / 2))
  let W : ℚ[X] := originalWbarQ p
  have hW : W.natDegree ≤ (p - 1) / 2 := originalWbarQ_degree p
  have heq : originalKbarQ p * (originalWbarQ p).toLaurent =
      LaurentPolynomial.C (17 * c) * T 0 * W.toLaurent -
        LaurentPolynomial.C (4 * c) * T (p : ℤ) * W.toLaurent -
        LaurentPolynomial.C (4 * c) * T (-(p : ℤ)) * W.toLaurent := by
    simp only [originalKbarQ, normPhase, W, c, T_zero, mul_one, _root_.map_mul,
      _root_.map_ofNat]
    ring
  have h0 := shiftedPolynomialQ_support (17 * c) 0 W j (by omega)
  have hp := shiftedPolynomialQ_support (4 * c) (p : ℤ) W j (by omega)
  have hm := shiftedPolynomialQ_support (4 * c) (-(p : ℤ)) W j (by omega)
  rw [heq]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h0, hp, hm, sub_zero]

theorem originalZpQ_support (p : ℕ) (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) : (originalZpQ p).coeff j = 0 := by
  rw [originalZpQ]
  apply endSym_support fourUnitQ _ (by omega) _ _ j hj
  intro k hk
  have hkp : (p : ℤ) ≠ k := by omega
  simpa only [_root_.map_one, one_mul, if_neg hkp] using
    coeff_unit_monomial (1 : ℚ) (p : ℤ) k

/-- Both reflected original endpoints and the full p-slot correction stay inside this band. -/
theorem originalSactQ_support (p : ℕ) [Fact p.Prime] (literalC : ℚ) (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) : (originalSactQ p literalC).coeff j = 0 := by
  have hP := endSym_support fourUnitQ _ (by omega) _ (originalPunitQ_support p) j hj
  simp only [originalSactQ, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    C_mul_coeff, hP, originalZpQ_support p j hj, mul_zero, sub_zero]

/-- The comparison retains Wbar's full degree-N band before its canonical holes. -/
theorem originalSbarQ_support (p : ℕ) [Fact p.Prime] (literalC : ℚ) (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) :
    (originalSbarQ p literalC (originalKbarQ p)).coeff j = 0 := by
  have hcan : ∀ k, k < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < k →
      (originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent)).coeff k = 0 := by
    exact canSlots_support p _ (by omega) _ (originalKbarWbarQ_support p)
  have hP := endSym_support fourUnitQ _ (by omega) _ hcan j hj
  simp only [originalSbarQ, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    C_mul_coeff, hP, originalZpQ_support p j hj, mul_zero, sub_zero]

/-- The genuine whole integral quotient inherits the bound from its exact rational p-division. -/
theorem originalWholeVSI_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℤ)
    (hj : j < -((p : ℤ) + ((p - 1) / 2 : ℕ)) ∨
      (p : ℤ) + ((p - 1) / 2 : ℕ) < j) : (originalWholeVSI p hp).coeff j = 0 := by
  let literalC : ℚ := (finiteEvenSquaredQ p).eval (4 / 5) -
    (finiteEvenSquaredQ p).eval (1 / 5)
  have hv := congrArg (fun F : ℚ[T;T⁻¹] => F.coeff j)
    (originalWholeVSI_value p hp literalC)
  rw [coefficientMap_coeff, C_mul_coeff, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, originalSactQ_support p literalC j hj,
    originalSbarQ_support p literalC j hj, sub_self, mul_zero] at hv
  apply Subtype.ext
  exact hv

/-- The canonical positive-p slot is removed before reflection or p-division. -/
theorem canSlots_pivot {R : Type*} [CommRing R] (p : ℕ) (hp : 0 < p)
    (F : R[T;T⁻¹]) : (canSlots p F).coeff (p : ℤ) = 0 := by
  simp only [canSlots, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    constant_coeff_outside _ (p : ℤ) (by omega), coeff_unit_monomial,
    if_true, sub_zero, sub_self]

/-- The actual whole quotient has zero at both p pivots over the integral ring.
The original equal Zp corrections are cancelled before division. -/
theorem originalWholeVSI_pivots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalWholeVSI p hp).coeff (p : ℤ) = 0 ∧
      (originalWholeVSI p hp).coeff (-(p : ℤ)) = 0 := by
  have hPp : (originalPunitQ p).coeff (p : ℤ) = 0 := by
    rw [originalPunitQ, originalJQ_coeff, canonicalInverseQ, if_pos rfl, zero_mul]
  have hPm : (originalPunitQ p).coeff (-(p : ℤ)) = 0 := by
    rw [originalPunitQ, originalJQ_coeff,
      originalRactQ_support p (-(p : ℤ) - 1) (Or.inl (by omega)), mul_zero]
  let W : ℚ[T;T⁻¹] := (originalWbarQ p).toLaurent
  have hW0 : W.coeff 0 = 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      WPFiniteJCarrier.toLaurent_coeff_nat, coeff_zero_eq_eval_zero,
      originalWbarQ_origin]
  have hWm : W.coeff (-(p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hWmm : W.coeff (-2 * (p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hKm : (originalKbarQ p * W).coeff (-(p : ℤ)) = 0 := by
    have heq : originalKbarQ p * W =
        LaurentPolynomial.C (17 / (2 * (5 : ℚ) ^ ((p - 1) / 2))) * T 0 * W -
          LaurentPolynomial.C (4 / (2 * (5 : ℚ) ^ ((p - 1) / 2))) * T (p : ℤ) * W -
          LaurentPolynomial.C (4 / (2 * (5 : ℚ) ^ ((p - 1) / 2))) * T (-(p : ℤ)) * W := by
      simp only [originalKbarQ, normPhase, T_zero, mul_one, div_eq_mul_inv,
        _root_.map_mul, _root_.map_ofNat, _root_.map_one]
      ring
    rw [heq]
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      WPFiniteJCarrier.shifted_coeff, sub_zero, sub_self,
      show -(p : ℤ) - p = -2 * p by omega, hWm, hWmm, hW0, mul_zero]
  have hCp : (originalCanQ p (originalKbarQ p * W)).coeff (p : ℤ) = 0 :=
    canSlots_pivot p (by omega) _
  have hCm : (originalCanQ p (originalKbarQ p * W)).coeff (-(p : ℤ)) = 0 := by
    simp only [originalCanQ, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hKm,
      constant_coeff_outside _ (-(p : ℤ)) (by omega), coeff_unit_monomial,
      if_neg (by omega : (p : ℤ) ≠ -(p : ℤ)), sub_zero]
  have hEnd (F : ℚ[T;T⁻¹]) (hFp : F.coeff (p : ℤ) = 0)
      (hFm : F.coeff (-(p : ℤ)) = 0) (j : ℤ)
      (hj : j = (p : ℤ) ∨ j = -(p : ℤ)) : (endSym fourUnitQ F).coeff j = 0 := by
    have h0 : j ≠ 0 := by rcases hj with rfl | rfl <;> omega
    have hjF : F.coeff j = 0 := by
      rcases hj with rfl | rfl
      · exact hFp
      · exact hFm
    have hmF : F.coeff (-j) = 0 := by
      rcases hj with rfl | rfl
      · exact hFm
      · simpa only [neg_neg] using hFp
    simp only [endSym, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, invert_apply, hjF, hmF,
      constant_coeff_outside _ j h0, add_zero, sub_zero]
  have hWhole (j : ℤ) (hj : j = (p : ℤ) ∨ j = -(p : ℤ)) :
      (originalWholeVSI p hp).coeff j = 0 := by
    let literalC : ℚ := (finiteEvenSquaredQ p).eval (4 / 5) -
      (finiteEvenSquaredQ p).eval (1 / 5)
    have hv := congrArg (fun F : ℚ[T;T⁻¹] => F.coeff j)
      (originalWholeVSI_value p hp literalC)
    rw [coefficientMap_coeff, C_mul_coeff, AddMonoidAlgebra.coeff_sub,
      Finsupp.sub_apply] at hv
    have hCanEnd : (endSym fourUnitQ
        (originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent))).coeff j = 0 :=
      hEnd _ hCp hCm j hj
    simp only [originalSactQ, originalSbarQ, AddMonoidAlgebra.coeff_sub,
      Finsupp.sub_apply, hEnd _ hPp hPm j hj, hCanEnd,
      sub_self, mul_zero] at hv
    apply Subtype.ext
    exact hv
  exact ⟨hWhole _ (Or.inl rfl), hWhole _ (Or.inr rfl)⟩

/-- Every nonzero Frobenius slot is fixed before residue differentiation.
The zeroth coefficient retains its separate endpoint-centering formula. -/
theorem originalWholeVSI_nonzero_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) (hj0 : j ≠ 0) :
    (originalWholeVSI p hp).coeff j = 0 := by
  obtain ⟨k, rfl⟩ := hj
  have hpz : (0 : ℤ) < p := by omega
  have hN : (((p - 1) / 2 : ℕ) : ℤ) < p := by omega
  obtain ⟨hpos, hneg⟩ := originalWholeVSI_pivots p hp
  by_cases hlow : k ≤ -2
  · apply originalWholeVSI_support p hp _ (Or.inl _)
    have hmul := mul_le_mul_of_nonneg_left hlow (le_of_lt hpz)
    omega
  · by_cases hhigh : 2 ≤ k
    · apply originalWholeVSI_support p hp _ (Or.inr _)
      have hmul := mul_le_mul_of_nonneg_left hhigh (le_of_lt hpz)
      omega
    · have hk : k = -1 ∨ k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl | rfl
      · simpa only [mul_neg_one] using hneg
      · exact False.elim (hj0 (by simp))
      · simpa only [mul_one] using hpos

/-- Endpoint centering retains the actual zeroth coefficient. -/
theorem endSym_origin_coefficient {R : Type*} [CommRing R] (u : Rˣ) (F : R[T;T⁻¹]) :
    (endSym u F).coeff 0 = 2 * F.coeff 0 -
      LaurentPolynomial.eval₂ (RingHom.id R) u F -
      LaurentPolynomial.eval₂ (RingHom.id R) u⁻¹ F := by
  have hc (c : R) : (LaurentPolynomial.C c : R[T;T⁻¹]).coeff 0 = c := by
    simpa only [T_zero, mul_one, if_true] using coeff_unit_monomial c 0 0
  simp only [endSym, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, invert_apply, neg_zero, hc]
  ring

theorem canSlots_origin {R : Type*} [CommRing R] (p : ℕ) (hp : 0 < p)
    (F : R[T;T⁻¹]) : (canSlots p F).coeff 0 = 0 := by
  have hc (c : R) : (LaurentPolynomial.C c : R[T;T⁻¹]).coeff 0 = c := by
    simpa only [T_zero, mul_one, if_true] using coeff_unit_monomial c 0 0
  simp only [canSlots, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hc,
    coeff_unit_monomial, if_neg (by omega : (p : ℤ) ≠ 0), sub_self]

/-- The invisible zeroth coefficient is the original endpoint difference divided over Q.
It is retained explicitly, rather than inferred from the two zero endpoints. -/
theorem originalWholeVSI_constant_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype ((originalWholeVSI p hp).coeff 0) =
      -(LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ (originalPunitQ p) +
        LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹ (originalPunitQ p) -
        LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ
          (originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent)) -
        LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹
          (originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent))) / (p : ℚ) := by
  let literalC : ℚ := (finiteEvenSquaredQ p).eval (4 / 5) -
    (finiteEvenSquaredQ p).eval (1 / 5)
  have hP0 : (originalPunitQ p).coeff 0 = 0 := by
    rw [originalPunitQ, originalJQ_coeff, canonicalInverseQ,
      if_neg (by omega : (0 : ℤ) ≠ (p : ℤ))]
    norm_num
  have hC0 : (originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent)).coeff 0 = 0 :=
    canSlots_origin p (by omega) _
  have hv := congrArg (fun F : ℚ[T;T⁻¹] => F.coeff 0)
    (originalWholeVSI_value p hp literalC)
  rw [coefficientMap_coeff, C_mul_coeff, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply] at hv
  simp only [originalSactQ, originalSbarQ, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, endSym_origin_coefficient, hP0, hC0] at hv
  linear_combination hv

end WPFieldAssembly.SourceClosureSigmaWholeSupport
