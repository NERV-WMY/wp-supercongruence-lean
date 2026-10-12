import WPFieldAssembly.SourceClosureSigmaProperJ
import WPFieldAssembly.ActualUW16PrimitiveSource
import WPFieldAssembly.SourceClosureSigmaProperEndpoint

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureSigmaProperJ
  WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.SourceClosureSigmaProperEndpoint

namespace WPFieldAssembly.SourceClosureSigmaWholePrimitive

set_option maxHeartbeats 1500000

/- This is the original rational integration operator, before field
reduction.  It omits precisely the ordinary residue and positive-p pivot;
the source support proves every surviving actual pivot is a p-unit. -/

noncomputable def canonicalInverseQ (p : ℕ) (j : ℤ) : ℚ :=
  if j = (p : ℤ) then 0 else (j : ℚ)⁻¹

noncomputable def originalJQ (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹] :=
  primitiveWith (canonicalInverseQ p)

noncomputable def originalCanQ (p : ℕ) (F : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  F - LaurentPolynomial.C (F.coeff 0) - LaurentPolynomial.C (F.coeff (p : ℤ)) * T (p : ℤ)

theorem originalJQ_coeff (p : ℕ) (F : ℚ[T;T⁻¹]) (j : ℤ) :
    (originalJQ p F).coeff j = canonicalInverseQ p j * F.coeff (j - 1) :=
  primitiveWith_coeff _ _ _

theorem originalJQ_C_mul (p : ℕ) (c : ℚ) (F : ℚ[T;T⁻¹]) :
    originalJQ p (LaurentPolynomial.C c * F) =
      LaurentPolynomial.C c * originalJQ p F := by
  simpa only [LaurentPolynomial.smul_eq_C_mul] using (originalJQ p).map_smul c F

theorem originalJQ_derivative (p : ℕ) (hp : 0 < p) (F : ℚ[T;T⁻¹]) :
    originalJQ p (D F) = originalCanQ p F := by
  ext j
  rw [originalJQ_coeff, D_coeff, sub_add_cancel]
  have hC : (LaurentPolynomial.C (F.coeff 0) : ℚ[T;T⁻¹]).coeff j =
      if (0 : ℤ) = j then F.coeff 0 else 0 := by
    simpa only [T_zero, mul_one] using coeff_unit_monomial (F.coeff 0) 0 j
  simp only [originalCanQ, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    hC, coeff_unit_monomial]
  by_cases hj0 : j = 0
  · subst j
    simp [canonicalInverseQ, show p ≠ 0 by omega]
  · by_cases hjp : j = (p : ℤ)
    · subst j
      simp [canonicalInverseQ, show (0 : ℤ) ≠ (p : ℤ) by omega]
    · have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
      rw [canonicalInverseQ, if_neg hjp, ← mul_assoc, inv_mul_cancel₀ hjq,
        if_neg (by omega : (0 : ℤ) ≠ j), if_neg (by omega : (p : ℤ) ≠ j)]
      ring

theorem originalJQ_proper (p : ℕ) [Fact p.Prime] :
    originalJQ p (properDensityQ p) = properJQ p := by
  ext j
  rw [originalJQ_coeff, properJQ, unitPrimitive_coeff]
  by_cases hj : -(p : ℤ) < j ∧ j < (p : ℤ)
  · rw [canonicalInverseQ, if_neg (by omega), unitInverse, if_pos hj]
  · by_cases hjp : j = (p : ℤ)
    · subst j
      simp [canonicalInverseQ, unitInverse]
    · have hc : (properDensityQ p).coeff (j - 1) = 0 :=
        properDensityQ_support p _ (by omega)
      rw [hc, mul_zero, mul_zero]

theorem originalJQ_unitBand (p : ℕ) (F : ℚ[T;T⁻¹])
    (hF : ∀ j, j < -(p : ℤ) ∨ (p : ℤ) - 1 < j → F.coeff j = 0) :
    originalJQ p F = unitPrimitive p F := by
  ext j
  rw [originalJQ_coeff, unitPrimitive_coeff]
  by_cases hj : -(p : ℤ) < j ∧ j < (p : ℤ)
  · rw [canonicalInverseQ, if_neg (by omega), unitInverse, if_pos hj]
  · by_cases hjp : j = (p : ℤ)
    · subst j
      simp [canonicalInverseQ, unitInverse]
    · rw [hF (j - 1) (by omega), mul_zero, mul_zero]

/-- In the actual whole source band, the original 0,p prescription is the existing canonical operator. -/
theorem originalJQ_existing_canonical (p : ℕ) (hp : 0 < p) (F : ℚ[T;T⁻¹])
    (hF : ∀ j, j < -(p : ℤ) ∨ 2 * (p : ℤ) - 2 < j → F.coeff j = 0) :
    originalJQ p F = WPActualEtaPrimitive.canonicalPrimitive p F := by
  ext j
  rw [originalJQ_coeff, WPActualEtaPrimitive.canonicalPrimitive_coeff]
  by_cases hband : -(p : ℤ) < j ∧ j < 2 * (p : ℤ)
  · have hres : (p : ℤ) ∣ j ↔ j = 0 ∨ j = (p : ℤ) := by
      constructor
      · rintro ⟨k, hk⟩
        have hpz : 0 < (p : ℤ) := by omega
        have hk0 : 0 ≤ k := by
          by_contra h
          have : k ≤ -1 := by omega
          nlinarith
        have hk1 : k ≤ 1 := by
          by_contra h
          have : 2 ≤ k := by omega
          nlinarith
        rcases (by omega : k = 0 ∨ k = 1) with hk0 | hk1
        · left
          simpa only [hk0, mul_zero] using hk
        · right
          simpa only [hk1, mul_one] using hk
      · rintro (rfl | rfl)
        · exact dvd_zero _
        · exact dvd_refl _
    by_cases hj0 : j = 0
    · subst j
      simp [canonicalInverseQ]
    · by_cases hjp : j = (p : ℤ)
      · subst j
        simp [canonicalInverseQ]
      · rw [if_neg (by simpa only [hres] using not_or.mpr ⟨hj0, hjp⟩),
          canonicalInverseQ, if_neg hjp, div_eq_mul_inv]
        ring
  · have hc := hF (j - 1) (by omega)
    rw [hc, mul_zero, zero_div]
    split_ifs <;> rfl

noncomputable def originalKactQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p

noncomputable def originalRactQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
    T (-(p : ℤ)) * (X + 1 : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1)

noncomputable def originalRlogQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 2 : ℚ) * T (-(p : ℤ)) *
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1)

noncomputable def originalLogProductQ (p : ℕ) [Fact p.Prime] : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
      (originalWactQ p).toLaurent * (WPFiniteZSource.Abar : ℚ[X]).derivative.toLaurent -
    originalKactQ p * (originalWactQ p).toLaurent * T (-1)

noncomputable def originalHactQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1 / 5 : ℚ) ^ (4 * ((p - 1) / 2))) *
    (originalRlogQ p +
      LaurentPolynomial.C (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) * properDensityQ p)

noncomputable def originalPunitQ (p : ℕ) : ℚ[T;T⁻¹] := originalJQ p (originalRactQ p)

theorem originalRactQ_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -(p : ℤ) ∨ 2 * (p : ℤ) - 2 < j) : (originalRactQ p).coeff j = 0 := by
  let P : ℚ[X] := (X + 1) ^ ((p - 1) / 2) *
    (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)
  have hA : (WPFiniteZSource.Abar : ℚ[X]).natDegree ≤ 2 := by
    have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by
      change (4 - X : ℚ[X]).natDegree + (4 * X - 1 : ℚ[X]).natDegree ≤ 2
      omega)
  have hX : (X + 1 : ℚ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  have hXP := (natDegree_pow_le (p := (X + 1 : ℚ[X])) (n := (p - 1) / 2)).trans
    (Nat.mul_le_mul_left _ hX)
  have hAP := (natDegree_pow_le (p := (WPFiniteZSource.Abar : ℚ[X])) (n := p - 1)).trans
    (Nat.mul_le_mul_left _ hA)
  have hP : P.natDegree ≤ ((p - 1) / 2) + 2 * (p - 1) := by
    exact (natDegree_mul_le (p := (X + 1 : ℚ[X]) ^ ((p - 1) / 2))
      (q := (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1))).trans (by omega)
  have heq : originalRactQ p =
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * P.toLaurent := by
    dsimp only [P, originalRactQ]
    rw [_root_.map_mul, _root_.map_pow, _root_.map_pow]
    ring
  rw [heq, WPFiniteJCarrier.shifted_coeff]
  have hz : P.toLaurent.coeff (j - -(p : ℤ)) = 0 := by
    apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inl (by omega)
    · exact Or.inr (by have := (Fact.out : p.Prime).pos; omega)
  rw [hz, mul_zero]

theorem originalPunitQ_existing_canonical (p : ℕ) [Fact p.Prime] :
    originalPunitQ p = WPActualEtaPrimitive.canonicalPrimitive p (originalRactQ p) :=
  originalJQ_existing_canonical p (Fact.out : p.Prime).pos _ (originalRactQ_support p)

theorem originalKactQ_derivative (p : ℕ) [Fact p.Prime] :
    D (originalKactQ p) = LaurentPolynomial.C (p : ℚ) *
      (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
          (WPFiniteZSource.Abar : ℚ[X]).derivative.toLaurent -
        originalKactQ p * T (-1)) := by
  have hpD : D ((WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p) =
      LaurentPolynomial.C (p : ℚ) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
        (WPFiniteZSource.Abar : ℚ[X]).derivative.toLaurent := by
    rw [← _root_.map_pow, D_toLaurent, derivative_pow]
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_natCast]
  have hT : D (T (-(p : ℤ)) : ℚ[T;T⁻¹]) =
      -LaurentPolynomial.C (p : ℚ) * T (-(p : ℤ) - 1) := by
    simpa only [_root_.map_one, one_mul, Int.cast_neg, Int.cast_natCast, _root_.map_neg, neg_mul] using
      D_monomial (1 : ℚ) (-(p : ℤ))
  have ht : (T (-(p : ℤ)) : ℚ[T;T⁻¹]) * T (-1) = T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
  rw [originalKactQ, mul_assoc, D_C_mul, D_mul, hT, hpD]
  linear_combination
    LaurentPolynomial.C (p : ℚ) *
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p * ht

theorem originalHactQ_residues (p : ℕ) [Fact p.Prime] :
    originalHactQ p =
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
          (LaurentPolynomial.C (4 * (5 : ℚ) ^ ((p - 1) / 2) /
              (15 * (4 : ℚ) ^ ((p - 1) / 2))) * (4 - T 1) +
            LaurentPolynomial.C ((5 : ℚ) ^ ((p - 1) / 2) / 15) * (4 * T 1 - 1)) := by
  let N := (p - 1) / 2
  have h5 : (5 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5wide : (5 : ℚ) ^ (4 * N) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4 : (4 : ℚ) ^ N ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpower : (5 : ℚ) ^ (5 * N) = (5 : ℚ) ^ (4 * N) * (5 : ℚ) ^ N := by
    rw [← pow_add]
    congr 1
    omega
  have h5invpow : (1 / 5 : ℚ) ^ (4 * N) = ((5 : ℚ) ^ (4 * N))⁻¹ := by
    rw [one_div, inv_pow]
  have hs4 : (1 / (2 * (5 : ℚ) ^ (5 * N))) *
        (4 * (5 : ℚ) ^ N / (15 * (4 : ℚ) ^ N)) =
      (1 / 5 : ℚ) ^ (4 * N) * (4 / 30) * ((4 : ℚ) ^ N)⁻¹ := by
    rw [hpower, h5invpow]
    field_simp [h5, h5wide, h4]
    ring
  have hs1 : (1 / (2 * (5 : ℚ) ^ (5 * N))) * ((5 : ℚ) ^ N / 15) =
      (1 / 5 : ℚ) ^ (4 * N) * (1 / 30) := by
    rw [hpower, h5invpow]
    field_simp [h5, h5wide]
    ring
  have hC4 := congrArg (fun q : ℚ => (LaurentPolynomial.C q : ℚ[T;T⁻¹])) hs4
  have hC1 := congrArg (fun q : ℚ => (LaurentPolynomial.C q : ℚ[T;T⁻¹])) hs1
  simp only [_root_.map_mul] at hC4 hC1
  have hb : (LaurentPolynomial.C (4 / 30 : ℚ) : ℚ[T;T⁻¹]) * 4 -
      LaurentPolynomial.C (1 / 30 : ℚ) = LaurentPolynomial.C (1 / 2 : ℚ) := by
    change LaurentPolynomial.C (4 / 30 : ℚ) * LaurentPolynomial.C (4 : ℚ) -
      LaurentPolynomial.C (1 / 30 : ℚ) = _
    rw [← _root_.map_mul, ← _root_.map_sub]
    congr 1
    norm_num
  have hl : (LaurentPolynomial.C (1 / 30 : ℚ) : ℚ[T;T⁻¹]) * 4 =
      LaurentPolynomial.C (4 / 30 : ℚ) := by
    change LaurentPolynomial.C (1 / 30 : ℚ) * LaurentPolynomial.C (4 : ℚ) = _
    rw [← _root_.map_mul]
    congr 1
    norm_num
  have hr : (LaurentPolynomial.C (4 / 30 : ℚ) : ℚ[T;T⁻¹]) *
        LaurentPolynomial.C (((4 : ℚ) ^ N)⁻¹) * (4 - T 1) +
      LaurentPolynomial.C (1 / 30 : ℚ) * (4 * T 1 - 1) =
      LaurentPolynomial.C (1 / 2 : ℚ) +
        LaurentPolynomial.C (((4 : ℚ) ^ N)⁻¹ - 1) *
          LaurentPolynomial.C (4 / 30 : ℚ) * (4 - T 1) := by
    rw [_root_.map_sub, _root_.map_one]
    linear_combination hb + T 1 * hl
  have hnum : (properNumeratorQ p).toLaurent =
      LaurentPolynomial.C (4 / 30 : ℚ) * (4 - T 1) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) := by
    simp only [properNumeratorQ, _root_.map_mul, _root_.map_pow,
      _root_.map_sub, _root_.map_ofNat, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  rw [originalHactQ, originalRlogQ, properDensityQ, hnum]
  linear_combination
    -T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
      LaurentPolynomial.C ((1 / 5 : ℚ) ^ (4 * N)) * hr -
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * (4 - T 1) * hC4 -
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * (4 * T 1 - 1) * hC1

theorem originalRactQ_division (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalRactQ p = originalKactQ p * D (originalWactQ p).toLaurent + originalHactQ p := by
  have h := congrArg Polynomial.toLaurent (originalWactQ_division p hp)
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_pow, _root_.map_add,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, _root_.map_ofNat,
    _root_.map_one, ← D_toLaurent] at h
  have hA : (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p =
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [originalHactQ_residues, originalRactQ, originalKactQ, hA]
  simp only [_root_.map_add, Polynomial.toLaurent_X, _root_.map_one]
  linear_combination
    -LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
      T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * h

theorem originalRactQ_integration_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalRactQ p = D (originalKactQ p * (originalWactQ p).toLaurent) +
      originalHactQ p - LaurentPolynomial.C (p : ℚ) * originalLogProductQ p := by
  rw [D_mul, originalKactQ_derivative, originalLogProductQ]
  linear_combination originalRactQ_division p hp

/-- UW16b with the literal original rational source and its two canonical holes. -/
theorem originalPunitQ_integration (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalPunitQ p = originalCanQ p (originalKactQ p * (originalWactQ p).toLaurent) +
      LaurentPolynomial.C ((1 / 5 : ℚ) ^ (4 * ((p - 1) / 2))) *
        (originalJQ p (originalRlogQ p) +
          LaurentPolynomial.C (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) * properJQ p) -
      LaurentPolynomial.C (p : ℚ) * originalJQ p (originalLogProductQ p) := by
  have h := congrArg (originalJQ p) (originalRactQ_integration_source p hp)
  rw [_root_.map_sub, _root_.map_add, originalJQ_derivative p (by omega), originalJQ_C_mul,
    originalHactQ, originalJQ_C_mul, _root_.map_add, originalJQ_C_mul,
    originalJQ_proper] at h
  exact h

theorem originalRlogQ_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -(p : ℤ) ∨ (p : ℤ) - 2 < j) : (originalRlogQ p).coeff j = 0 := by
  have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hA : (WPFiniteZSource.Abar : ℚ[X]).natDegree ≤ 2 := by
    unfold WPFiniteZSource.Abar
    exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by omega)
  have hpow : ((WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)).natDegree ≤ 2 * (p - 1) := by
    have hd := (natDegree_pow_le (p := (WPFiniteZSource.Abar : ℚ[X])) (n := p - 1)).trans
      (Nat.mul_le_mul_left (p - 1) hA)
    omega
  rw [originalRlogQ, ← _root_.map_pow, WPFiniteJCarrier.shifted_coeff]
  have hz : ((WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)).toLaurent.coeff (j + p) = 0 := by
    apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inl (by omega)
    · exact Or.inr (by have := (Fact.out : p.Prime).pos; omega)
  simp only [sub_neg_eq_add, hz, mul_zero]

theorem originalRlogQ_reflection (p : ℕ) [Fact p.Prime] :
    T (-2) * invert (originalRlogQ p) = originalRlogQ p := by
  have hp1 : 1 ≤ p := by have := (Fact.out : p.Prime).pos; omega
  have ht : (T (-2) : ℚ[T;T⁻¹]) * T (p : ℤ) * T (-2) ^ (p - 1) = T (-(p : ℤ)) := by
    rw [T_pow, ← T_add, ← T_add]
    congr 1
    omega
  rw [originalRlogQ, _root_.map_mul, _root_.map_mul, invert_C, invert_T, _root_.map_pow,
    WPFiniteZSource.invert_Abar, mul_pow]
  simp only [neg_neg]
  linear_combination LaurentPolynomial.C (1 / 2 : ℚ) *
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1) * ht

theorem originalRlogPrimitiveQ_source (p : ℕ) [Fact p.Prime] :
    D (originalJQ p (originalRlogQ p)) = originalRlogQ p -
      LaurentPolynomial.C ((originalRlogQ p).coeff (-1)) * T (-1) := by
  rw [originalJQ_unitBand p _ (by intro j hj; exact originalRlogQ_support p j (by omega))]
  have hd := unitPrimitive_source p (Fact.out : p.Prime).pos (originalRlogQ p)
    (by intro j hj; exact originalRlogQ_support p j (by omega))
    (by intro j _ hj; exact_mod_cast hj)
  rw [originalRlogQ_support p ((p : ℤ) - 1) (Or.inr (by omega)),
    _root_.map_zero, zero_mul, sub_zero] at hd
  exact hd

theorem derivative_zero_origin_uniqueQ (F : ℚ[T;T⁻¹]) (hD : D F = 0) (h0 : F.coeff 0 = 0) :
    F = 0 := by
  ext j
  by_cases hj : j = 0
  · simpa [hj] using h0
  · have h := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff (j - 1)) hD
    rw [D_coeff, sub_add_cancel] at h
    have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj
    change (j : ℚ) * F.coeff j = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hjq

/-- The full original Rlog primitive is odd over Q before any endpoint or p-division. -/
theorem originalRlogPrimitiveQ_odd (p : ℕ) [Fact p.Prime] :
    invert (originalJQ p (originalRlogQ p)) = -originalJQ p (originalRlogQ p) := by
  let J := originalJQ p (originalRlogQ p)
  have hD : D (J + invert J) = 0 := by
    rw [_root_.map_add, D_invert]
    dsimp only [J]
    rw [originalRlogPrimitiveQ_source, _root_.map_sub, _root_.map_mul, invert_C, invert_T]
    simp only [neg_neg]
    have ht : (T (-2) : ℚ[T;T⁻¹]) * T 1 = T (-1) := by
      rw [← T_add]
      norm_num
    linear_combination -originalRlogQ_reflection p +
      LaurentPolynomial.C ((originalRlogQ p).coeff (-1)) * ht
  have h0 : (J + invert J).coeff 0 = 0 := by
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, invert_apply, neg_zero]
    dsimp only [J]
    rw [originalJQ_unitBand p _ (by intro j hj; exact originalRlogQ_support p j (by omega)),
      unitPrimitive_zero, add_zero]
  have hz := derivative_zero_origin_uniqueQ _ hD h0
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)

/-- UW16j cancels this unsymmetrized primitive only in the original whole EndSym. -/
theorem originalRlogPrimitiveQ_endSym (p : ℕ) [Fact p.Prime] :
    endSym fourUnitQ (originalJQ p (originalRlogQ p)) = 0 := by
  have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ)
    (originalRlogPrimitiveQ_odd p)
  rw [WPFiniteJWeightedResidue.inversion_eval, _root_.map_neg] at he
  rw [endSym, originalRlogPrimitiveQ_odd, add_neg_cancel, he, _root_.map_neg]
  ring

noncomputable def originalZpQ (p : ℕ) : ℚ[T;T⁻¹] :=
  endSym fourUnitQ (T (p : ℤ))

noncomputable def originalSactQ (p : ℕ) [Fact p.Prime] (literalC : ℚ) : ℚ[T;T⁻¹] :=
  endSym fourUnitQ (originalPunitQ p) -
    LaurentPolynomial.C (8 * literalC / 15) * originalZpQ p

/-- UW16k keeps the same whole rational source, both actual ends, and positive-p hole. -/
theorem originalSactQ_integration (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (literalC : ℚ) :
    originalSactQ p literalC =
      endSym fourUnitQ (originalCanQ p (originalKactQ p * (originalWactQ p).toLaurent)) +
        LaurentPolynomial.C ((1 / 5 : ℚ) ^ (4 * ((p - 1) / 2))) *
          LaurentPolynomial.C (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) * properEndSymQ p -
        LaurentPolynomial.C (p : ℚ) *
          endSym fourUnitQ (originalJQ p (originalLogProductQ p)) -
        LaurentPolynomial.C (8 * literalC / 15) * originalZpQ p := by
  rw [originalSactQ, originalPunitQ_integration p hp, endSym_sub,
    endSym_add, endSym_C_mul, endSym_add, endSym_C_mul,
    originalRlogPrimitiveQ_endSym, zero_add, endSym_C_mul, properEndSymQ]
  ring

theorem originalCanQ_endSym (p : ℕ) (F : ℚ[T;T⁻¹]) :
    endSym fourUnitQ (originalCanQ p F) = endSym fourUnitQ F -
      LaurentPolynomial.C (F.coeff (p : ℤ)) * originalZpQ p := by
  rw [originalCanQ, endSym_sub, endSym_sub, endSym_C, sub_zero,
    endSym_C_mul, originalZpQ]

noncomputable def originalSbarQ (p : ℕ) [Fact p.Prime] (literalC : ℚ)
    (Kbar : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  endSym fourUnitQ (originalCanQ p (Kbar * (originalWbarQ p).toLaurent)) -
    LaurentPolynomial.C (8 * literalC / 15) * originalZpQ p

/-- The comparison is subtracted before rational p-division; its actual phases cancel exactly. -/
theorem originalSactQ_first_difference (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (literalC : ℚ) (Kbar : ℚ[T;T⁻¹]) :
    LaurentPolynomial.C (1 / (p : ℚ)) *
        (originalSactQ p literalC - originalSbarQ p literalC Kbar) =
      LaurentPolynomial.C (1 / (p : ℚ)) *
        (endSym fourUnitQ
            (originalCanQ p (originalKactQ p * (originalWactQ p).toLaurent)) -
          endSym fourUnitQ (originalCanQ p (Kbar * (originalWbarQ p).toLaurent))) +
      LaurentPolynomial.C (properCarryQ p / (p : ℚ)) * properEndSymQ p -
      endSym fourUnitQ (originalJQ p (originalLogProductQ p)) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hinv : (LaurentPolynomial.C (1 / (p : ℚ)) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C (p : ℚ) = 1 := by
    rw [← _root_.map_mul, one_div_mul_cancel hpq, _root_.map_one]
  have hexp : 4 * ((p - 1) / 2) = 2 * (p - 1) := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have hcarry : (1 / (p : ℚ)) * (1 / 5 : ℚ) ^ (4 * ((p - 1) / 2)) *
        (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) = properCarryQ p / (p : ℚ) := by
    rw [hexp, properCarryQ]
    ring
  have hC := congrArg (fun c : ℚ => (LaurentPolynomial.C c : ℚ[T;T⁻¹])) hcarry
  simp only [_root_.map_mul] at hC
  rw [originalSactQ_integration p hp, originalSbarQ]
  linear_combination
    properEndSymQ p * hC -
      endSym fourUnitQ (originalJQ p (originalLogProductQ p)) * hinv

end WPFieldAssembly.SourceClosureSigmaWholePrimitive
