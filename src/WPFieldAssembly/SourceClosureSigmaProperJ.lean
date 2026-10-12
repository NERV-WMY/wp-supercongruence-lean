import WPFieldAssembly.ActualSigmaNormCarrySource
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualSigmaNormCarrySource

namespace WPFieldAssembly.SourceClosureSigmaProperJ

set_option maxHeartbeats 1500000

/- UW16's proper rational source is first cancelled as a whole.  Its
ordinary residue and positive-p integration pivot are retained separately.
The canonical integral operator below keeps every remaining signed unit
coefficient and fixes the zeroth coefficient before reduction. -/

noncomputable def primitiveWith {R : Type*} [CommRing R] (u : ℤ → R) :
    R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  (Finsupp.linearCombination R (fun n : ℤ => LaurentPolynomial.C (u (n + 1)) * T (n + 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem primitiveWith_monomial {R : Type*} [CommRing R] (u : ℤ → R)
    (a : R) (n : ℤ) :
    primitiveWith u (LaurentPolynomial.C a * T n) = LaurentPolynomial.C (a * u (n + 1)) * T (n + 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination R _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← _root_.map_mul]

theorem primitiveWith_coeff {R : Type*} [CommRing R] (u : ℤ → R)
    (F : R[T;T⁻¹]) (j : ℤ) :
    (primitiveWith u F).coeff j = u j * F.coeff (j - 1) := by
  have hc (c : R) (n k : ℤ) : (LaurentPolynomial.C c * T n).coeff k = if n = k then c else 0 := by
    rw [← single_eq_C_mul_T]
    exact Finsupp.single_apply
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hF, hG]
    ring
  | C_mul_T n c =>
    rw [primitiveWith_monomial, hc, hc]
    by_cases hn : n + 1 = j
    · have hnj : n = j - 1 := by omega
      rw [if_pos hn, if_pos hnj, hn]
      ring
    · have hnj : n ≠ j - 1 := by omega
      rw [if_neg hn, if_neg hnj, mul_zero]

theorem primitiveWith_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : ℤ → R) (v : ℤ → S)
    (hu : ∀ j, f (u j) = v j) (F : R[T;T⁻¹]) :
    coefficientMap f (primitiveWith u F) = primitiveWith v (coefficientMap f F) := by
  ext j
  rw [coefficientMap_coeff, primitiveWith_coeff, primitiveWith_coeff,
    coefficientMap_coeff, _root_.map_mul, hu]

noncomputable def unitInverse {K : Type*} [Field K] (p : ℕ) (j : ℤ) : K :=
  if -(p : ℤ) < j ∧ j < (p : ℤ) then (j : K)⁻¹ else 0

noncomputable def unitInverseI (p : ℕ) [Fact p.Prime] (j : ℤ) : integralRationals p :=
  if 0 < j ∧ j < (p : ℤ) then smallIntegralInverse p j.toNat else
  if -(p : ℤ) < j ∧ j < 0 then -smallIntegralInverse p (-j).toNat else 0

theorem unitInverseI_value (p : ℕ) [Fact p.Prime] (j : ℤ) :
    (integralRationals p).subtype (unitInverseI p j) = unitInverse (K := ℚ) p j := by
  by_cases hpos : 0 < j ∧ j < (p : ℤ)
  · have hn : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hc : (j.toNat : ℚ) = (j : ℚ) := by exact_mod_cast hn
    rw [unitInverseI, if_pos hpos]
    change (smallIntegralInverse p j.toNat).val = _
    rw [smallIntegralInverse_value p j.toNat (by omega) (by omega),
      unitInverse, if_pos (by omega), hc, one_div]
  · rw [unitInverseI, if_neg hpos]
    by_cases hneg : -(p : ℤ) < j ∧ j < 0
    · have hn : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      have hc : ((-j).toNat : ℚ) = -(j : ℚ) := by exact_mod_cast hn
      rw [if_pos hneg, _root_.map_neg]
      change -(smallIntegralInverse p (-j).toNat).val = _
      rw [smallIntegralInverse_value p (-j).toNat (by omega) (by omega),
        unitInverse, if_pos (by omega), hc, one_div, inv_neg, neg_neg]
    · rw [if_neg hneg, _root_.map_zero, unitInverse]
      by_cases hj : j = 0
      · simp [hj]
      · rw [if_neg (by omega)]

theorem unitInverseI_field (p : ℕ) [Fact p.Prime] (j : ℤ) :
    residueHom p (unitInverseI p j) = unitInverse (K := ZMod p) p j := by
  by_cases hpos : 0 < j ∧ j < (p : ℤ)
  · have hn : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    have hc : (j.toNat : ZMod p) = (j : ZMod p) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod p)) hn
    rw [unitInverseI, if_pos hpos, smallIntegralInverse_field p _ (by omega) (by omega),
      unitInverse, if_pos (by omega), hc]
  · rw [unitInverseI, if_neg hpos]
    by_cases hneg : -(p : ℤ) < j ∧ j < 0
    · have hn : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
      have hc : ((-j).toNat : ZMod p) = -(j : ZMod p) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using
          congrArg (fun z : ℤ => (z : ZMod p)) hn
      rw [if_pos hneg, _root_.map_neg, smallIntegralInverse_field p _ (by omega) (by omega),
        unitInverse, if_pos (by omega), hc, inv_neg, neg_neg]
    · rw [if_neg hneg, _root_.map_zero, unitInverse]
      by_cases hj : j = 0
      · simp [hj]
      · rw [if_neg (by omega)]

noncomputable def unitPrimitive {K : Type*} [Field K] (p : ℕ)
    (F : K[T;T⁻¹]) : K[T;T⁻¹] := primitiveWith (unitInverse p) F

theorem unitPrimitive_coeff {K : Type*} [Field K] (p : ℕ)
    (F : K[T;T⁻¹]) (j : ℤ) :
    (unitPrimitive p F).coeff j = unitInverse p j * F.coeff (j - 1) :=
  primitiveWith_coeff _ _ _

theorem unitPrimitive_zero {K : Type*} [Field K] (p : ℕ) (F : K[T;T⁻¹]) :
    (unitPrimitive p F).coeff 0 = 0 := by simp [unitPrimitive_coeff, unitInverse]

theorem unitPrimitive_outside {K : Type*} [Field K] (p : ℕ)
    (F : K[T;T⁻¹]) (j : ℤ) (hj : j ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j) :
    (unitPrimitive p F).coeff j = 0 := by
  rw [unitPrimitive_coeff, unitInverse, if_neg (by omega), zero_mul]

theorem unitPrimitive_derivative {K : Type*} [Field K] (p : ℕ)
    (F : K[T;T⁻¹]) (j : ℤ) :
    (D (unitPrimitive p F)).coeff j =
      ((j + 1 : ℤ) : K) * unitInverse p (j + 1) * F.coeff j := by
  rw [D_coeff, unitPrimitive_coeff, add_sub_cancel_right, mul_assoc]

theorem coeff_unit_monomial {R : Type*} [CommRing R] (c : R) (n j : ℤ) :
    (LaurentPolynomial.C c * T n : R[T;T⁻¹]).coeff j = if n = j then c else 0 := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_apply

theorem unitPrimitive_source {K : Type*} [Field K] (p : ℕ) (hp : 0 < p)
    (F : K[T;T⁻¹])
    (hF : ∀ j, j < -(p : ℤ) ∨ (p : ℤ) - 1 < j → F.coeff j = 0)
    (hu : ∀ j : ℤ, -(p : ℤ) < j ∧ j < (p : ℤ) → j ≠ 0 → (j : K) ≠ 0) :
    D (unitPrimitive p F) = F - LaurentPolynomial.C (F.coeff (-1)) * T (-1) -
      LaurentPolynomial.C (F.coeff ((p : ℤ) - 1)) * T ((p : ℤ) - 1) := by
  ext j
  simp only [unitPrimitive_derivative, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, coeff_unit_monomial]
  by_cases hj0 : j = -1
  · subst j
    simp [unitInverse, show (p : ℤ) - 1 ≠ -1 by omega]
  · by_cases hjp : j = (p : ℤ) - 1
    · subst j
      simp [unitInverse, show (-1 : ℤ) ≠ (p : ℤ) - 1 by omega]
    · rw [if_neg (by omega : (-1 : ℤ) ≠ j),
        if_neg (by omega : (p : ℤ) - 1 ≠ j), sub_zero, sub_zero]
      by_cases hband : -(p : ℤ) < j + 1 ∧ j + 1 < (p : ℤ)
      · rw [unitInverse, if_pos hband, mul_inv_cancel₀ (hu _ hband (by omega)), one_mul]
      · rw [unitInverse, if_neg hband, mul_zero, zero_mul, hF j (by omega)]

theorem signed_unit_nonzero (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : -(p : ℤ) < j ∧ j < (p : ℤ)) (hj0 : j ≠ 0) : (j : ZMod p) ≠ 0 := by
  by_cases hpos : 0 < j
  · exact integer_unit_in_band p j ⟨hpos, hj.2⟩
  · have hn := integer_unit_in_band (K := ZMod p) p (-j) (by omega)
    simpa only [Int.cast_neg, neg_ne_zero] using hn

theorem unitPrimitive_unique (p : ℕ) [Fact p.Prime]
    (F G : (ZMod p)[T;T⁻¹]) (h0 : F.coeff 0 = G.coeff 0)
    (hF : ∀ j, j ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j → F.coeff j = 0)
    (hG : ∀ j, j ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j → G.coeff j = 0)
    (hD : D F = D G) : F = G := by
  ext j
  by_cases hj0 : j = 0
  · simpa only [hj0] using h0
  · by_cases hj : -(p : ℤ) < j ∧ j < (p : ℤ)
    · have hd := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (j - 1)) hD
      rw [D_coeff, D_coeff, sub_add_cancel] at hd
      exact mul_left_cancel₀ (signed_unit_nonzero p j hj hj0) hd
    · rw [hF j (by omega), hG j (by omega)]

noncomputable def properNumeratorQ (p : ℕ) : ℚ[X] :=
  Polynomial.C (4 / 30 : ℚ) * (4 - X) * (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)

noncomputable def properDensityQ (p : ℕ) : ℚ[T;T⁻¹] :=
  T (-(p : ℤ)) * (properNumeratorQ p).toLaurent

noncomputable def properNumeratorI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  Polynomial.C (4 * smallIntegralInverse p 2 * smallIntegralInverse p 3 *
    smallIntegralInverse p 5) * (4 - X) * (normAbarI p) ^ (p - 1)

noncomputable def properDensityI (p : ℕ) [Fact p.Prime] : (integralRationals p)[T;T⁻¹] :=
  T (-(p : ℤ)) * (properNumeratorI p).toLaurent

noncomputable def properJQ (p : ℕ) : ℚ[T;T⁻¹] := unitPrimitive p (properDensityQ p)

noncomputable def properJI (p : ℕ) [Fact p.Prime] : (integralRationals p)[T;T⁻¹] :=
  primitiveWith (unitInverseI p) (properDensityI p)

theorem properDensityI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (properDensityI p) = properDensityQ p := by
  have h2 : (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ) :=
    smallIntegralInverse_value p 2 (by omega) (by omega)
  have h3 : (integralRationals p).subtype (smallIntegralInverse p 3) = (1 / 3 : ℚ) :=
    smallIntegralInverse_value p 3 (by omega) (by omega)
  have h5 : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  have hA : (normAbarI p).map (integralRationals p).subtype =
      (WPFiniteZSource.Abar : ℚ[X]) := by
    simp only [normAbarI, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  have hc : (integralRationals p).subtype
      (4 * smallIntegralInverse p 2 * smallIntegralInverse p 3 * smallIntegralInverse p 5) =
      (4 / 30 : ℚ) := by
    simp only [_root_.map_mul, _root_.map_ofNat, h2, h3, h5]
    norm_num
  have hnum : (properNumeratorI p).map (integralRationals p).subtype =
      properNumeratorQ p := by
    simp only [properNumeratorI, properNumeratorQ, Polynomial.map_mul,
      Polynomial.map_C, hc, Polynomial.map_sub, Polynomial.map_ofNat,
      Polynomial.map_X, Polynomial.map_pow, hA]
  rw [properDensityI, _root_.map_mul, coefficientMap_T, coefficientMap_toLaurent, hnum]
  rfl

theorem properJI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (properJI p) = properJQ p := by
  rw [properJI, primitiveWith_map _ _ _ (unitInverseI_value p), properDensityI_value p hp]
  rfl

noncomputable def properDensityField (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (4 / 30 : ZMod p) * T (-(p : ℤ)) *
    (4 - T 1) * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ (p - 1)

theorem properDensityI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (properDensityI p) = properDensityField p := by
  have hc : (4 : ZMod p) * (2 : ZMod p)⁻¹ * (3 : ZMod p)⁻¹ * (5 : ZMod p)⁻¹ =
      (4 / 30 : ZMod p) := by
    rw [show (30 : ZMod p) = 2 * 3 * 5 by norm_num]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hA : (normAbarI p).map (residueHom p) =
      (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    simp only [normAbarI, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  have hscalar : residueHom p
      (4 * smallIntegralInverse p 2 * smallIntegralInverse p 3 * smallIntegralInverse p 5) =
      (4 / 30 : ZMod p) := by
    simp only [_root_.map_mul, _root_.map_ofNat,
      smallIntegralInverse_field p 2 (by omega) (by omega),
      smallIntegralInverse_field p 3 (by omega) (by omega),
      smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat, hc]
  have hnum : (properNumeratorI p).map (residueHom p) =
      Polynomial.C (4 / 30 : ZMod p) * (4 - X) *
        (WPFiniteZSource.Abar : (ZMod p)[X]) ^ (p - 1) := by
    simp only [properNumeratorI, Polynomial.map_mul, Polynomial.map_C, hscalar,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_pow, hA]
  rw [properDensityI, _root_.map_mul, coefficientMap_T, coefficientMap_toLaurent, hnum]
  simp only [properDensityField, _root_.map_mul, _root_.map_sub,
    _root_.map_pow, _root_.map_ofNat, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  ring

theorem properJI_field_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (properJI p) = unitPrimitive p (properDensityField p) := by
  rw [properJI, primitiveWith_map _ _ _ (unitInverseI_field p), properDensityI_field p hp]
  rfl

theorem properNumeratorQ_degree (p : ℕ) (hp : 1 ≤ p) :
    (properNumeratorQ p).natDegree ≤ 2 * p - 1 := by
  have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hA : (WPFiniteZSource.Abar : ℚ[X]).natDegree ≤ 2 := by
    unfold WPFiniteZSource.Abar
    exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by omega)
  have hpow : ((WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)).natDegree ≤ (p - 1) * 2 :=
    (natDegree_pow_le (p := (WPFiniteZSource.Abar : ℚ[X])) (n := p - 1)).trans
      (Nat.mul_le_mul_left _ hA)
  unfold properNumeratorQ
  have hm := natDegree_mul_le
    (p := Polynomial.C (4 / 30 : ℚ) * (4 - X))
    (q := (WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1))
  have hc := natDegree_mul_le (p := Polynomial.C (4 / 30 : ℚ)) (q := 4 - X)
  simp only [natDegree_C] at hc
  omega

theorem properDensityQ_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j < -(p : ℤ) ∨ (p : ℤ) - 1 < j) : (properDensityQ p).coeff j = 0 := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ℚ) (-(p : ℤ)) j
    (properNumeratorQ p).toLaurent
  simp only [_root_.map_one, one_mul] at hs
  rw [properDensityQ, hs]
  apply WPFiniteJCarrier.toLaurent_coeff_outside
  rcases hj with hj | hj
  · exact Or.inl (by omega)
  · have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
    have hd := properNumeratorQ_degree p hp1
    exact Or.inr (by omega)

theorem properJQ_source (p : ℕ) [Fact p.Prime] :
    D (properJQ p) = properDensityQ p -
      LaurentPolynomial.C ((properDensityQ p).coeff (-1)) * T (-1) -
      LaurentPolynomial.C ((properDensityQ p).coeff ((p : ℤ) - 1)) * T ((p : ℤ) - 1) := by
  exact unitPrimitive_source p (Fact.out : p.Prime).pos (properDensityQ p)
    (properDensityQ_support p) (by intro j _ hj; exact_mod_cast hj)

noncomputable def logFourField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (WPFiniteAffineLog.LP p).comp (4 * X)

noncomputable def properJField (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 15 : ZMod p) *
    (T (-(p : ℤ)) - LaurentPolynomial.C (1 / 4 : ZMod p)) *
    (logFourField p).toLaurent

private theorem four_nonzero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)

private theorem fifteen_nonzero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (15 : ZMod p) ≠ 0 := by
  rw [show (15 : ZMod p) = 3 * 5 by norm_num]
  exact mul_ne_zero
    (WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega))
    (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))

theorem properDensityField_factored (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    properDensityField p = LaurentPolynomial.C (2 / 15 : ZMod p) *
      (4 * T (-(p : ℤ)) - 1) * (1 - 4 * T 1) ^ (p - 1) := by
  have hC : LaurentPolynomial.C (4 / 30 : ZMod p) =
      (LaurentPolynomial.C (2 / 15 : ZMod p) : (ZMod p)[T;T⁻¹]) := by
    congr 1
    have h30 : (30 : ZMod p) ≠ 0 := by
      rw [show (30 : ZMod p) = 2 * 15 by norm_num]
      exact mul_ne_zero (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
        (fifteen_nonzero p hp)
    apply (div_eq_div_iff h30 (fifteen_nonzero p hp)).mpr
    ring
  have hleft : (4 - T 1 : (ZMod p)[T;T⁻¹]) ^ p = 4 - T (p : ℤ) := by
    have hpoly : (4 - X : (ZMod p)[X]) ^ p = 4 - X ^ p := by
      rw [sub_pow_char]
      have hfour : (4 : (ZMod p)[X]) ^ p = 4 := by
        change Polynomial.C (4 : ZMod p) ^ p = Polynomial.C (4 : ZMod p)
        rw [← Polynomial.C_pow, ZMod.pow_card]
      rw [hfour]
    have h := congrArg Polynomial.toLaurent hpoly
    simpa only [_root_.map_pow, _root_.map_sub, _root_.map_ofNat,
      Polynomial.toLaurent_X, T_pow, mul_one] using h
  have heven : Even (p - 1) := by
    have hhalf := WPFiniteWSource.half_exponent p hp
    exact ⟨(p - 1) / 2, by omega⟩
  have hright : (4 * T 1 - 1 : (ZMod p)[T;T⁻¹]) ^ (p - 1) =
      (1 - 4 * T 1) ^ (p - 1) := by
    rw [show (4 * T 1 - 1 : (ZMod p)[T;T⁻¹]) = -(1 - 4 * T 1) by ring,
      heven.neg_pow]
  have hpow : (4 - T 1 : (ZMod p)[T;T⁻¹]) * (4 - T 1) ^ (p - 1) =
      (4 - T 1) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) * T (p : ℤ) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  rw [properDensityField, hC]
  simp only [WPFiniteZSource.Abar, _root_.map_mul, _root_.map_sub, _root_.map_ofNat,
    _root_.map_one, Polynomial.toLaurent_X, mul_pow]
  calc
    _ = LaurentPolynomial.C (2 / 15 : ZMod p) * T (-(p : ℤ)) *
      ((4 - T 1) * (4 - T 1) ^ (p - 1)) * (4 * T 1 - 1) ^ (p - 1) := by ring
    _ = _ := by
      rw [hpow, hleft, hright]
      linear_combination -LaurentPolynomial.C (2 / 15 : ZMod p) *
        (1 - 4 * T 1) ^ (p - 1) * ht

theorem logFourField_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (logFourField p).toLaurent =
      4 * ((1 - 4 * T 1) ^ (p - 1) - T ((p : ℤ) - 1)) := by
  have hfour : (4 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (four_nonzero p hp)
  have hpow : (4 * T 1 : (ZMod p)[T;T⁻¹]) ^ (p - 1) = T ((p : ℤ) - 1) := by
    rw [mul_pow]
    change LaurentPolynomial.C (4 : ZMod p) ^ (p - 1) * T 1 ^ (p - 1) = _
    rw [← _root_.map_pow, hfour, _root_.map_one, one_mul, T_pow]
    congr 1
    omega
  rw [D_toLaurent, logFourField, derivative_comp,
    WPFiniteAffineLog.LP_derivative_closed_eq]
  have hd : (4 * X : (ZMod p)[X]).derivative = 4 := by
    rw [show (4 : (ZMod p)[X]) = Polynomial.C (4 : ZMod p) from rfl,
      derivative_C_mul, derivative_X, mul_one]
  rw [hd]
  simp only [sub_comp, pow_comp, sub_comp, one_comp, X_comp,
    _root_.map_mul, _root_.map_sub, _root_.map_pow, _root_.map_ofNat, _root_.map_one, Polynomial.toLaurent_X]
  rw [hpow]

theorem properJField_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (properJField p) = properDensityField p -
      LaurentPolynomial.C (8 / 15 : ZMod p) * T (-1) +
      LaurentPolynomial.C (2 / 15 : ZMod p) * T ((p : ℤ) - 1) := by
  have hphase : D (T (-(p : ℤ)) - LaurentPolynomial.C (1 / 4 : ZMod p) :
      (ZMod p)[T;T⁻¹]) = 0 := by
    have ht := D_frobenius_shift p (1 : (ZMod p)[T;T⁻¹]) (-(p : ℤ))
      (dvd_neg.mpr (dvd_refl _))
    have h1 : D (1 : (ZMod p)[T;T⁻¹]) = 0 := by simpa only [_root_.map_one] using D_C (1 : ZMod p)
    simp only [mul_one, h1, mul_zero] at ht
    rw [_root_.map_sub, ht, D_C, sub_self]
  have hunit : (4 : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (1 / 4 : ZMod p) = 1 := by
    change LaurentPolynomial.C (4 : ZMod p) * LaurentPolynomial.C (1 / 4 : ZMod p) = 1
    rw [← _root_.map_mul, mul_one_div_cancel (four_nonzero p hp), _root_.map_one]
  have hc : (LaurentPolynomial.C (2 / 15 : ZMod p) : (ZMod p)[T;T⁻¹]) * 4 =
      LaurentPolynomial.C (8 / 15 : ZMod p) := by
    change LaurentPolynomial.C (2 / 15 : ZMod p) * LaurentPolynomial.C (4 : ZMod p) = _
    rw [← _root_.map_mul]
    congr 1
    ring
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) * T ((p : ℤ) - 1) = T (-1) := by
    rw [← T_add]
    congr 1
    omega
  rw [properJField, mul_assoc, D_C_mul, D_mul, hphase, zero_mul, zero_add,
    logFourField_derivative p hp, properDensityField_factored p hp]
  linear_combination
    -LaurentPolynomial.C (2 / 15 : ZMod p) *
      ((1 - 4 * T 1) ^ (p - 1) - T ((p : ℤ) - 1)) * hunit -
    4 * LaurentPolynomial.C (2 / 15 : ZMod p) * ht - T (-1) * hc

theorem properDensityField_omitted (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properDensityField p).coeff (-1) = 8 / 15 ∧
      (properDensityField p).coeff ((p : ℤ) - 1) = -2 / 15 := by
  have h := properJField_derivative p hp
  have h0 := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (-1)) h
  have hpos := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff ((p : ℤ) - 1)) h
  simp only [D_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_unit_monomial] at h0 hpos
  have hnot : (p : ℤ) - 1 ≠ -1 := by omega
  have hpz : ((p : ℤ) : ZMod p) = 0 := by simp
  simp only [show (-1 : ℤ) + 1 = 0 by omega, Int.cast_zero, zero_mul,
    if_true, if_neg hnot] at h0
  simp only [sub_add_cancel, hpz, zero_mul, if_true, if_neg hnot.symm,
    sub_zero] at hpos
  constructor
  · linear_combination -h0
  · linear_combination -hpos

theorem properDensityField_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : j < -(p : ℤ) ∨ (p : ℤ) - 1 < j) :
    (properDensityField p).coeff j = 0 := by
  have hv := congrArg (fun L : ℚ[T;T⁻¹] => L.coeff j) (properDensityI_value p hp)
  rw [coefficientMap_coeff, properDensityQ_support p j hj] at hv
  have hi : (properDensityI p).coeff j = 0 := by
    apply Subtype.ext
    exact hv
  rw [← properDensityI_field p hp, coefficientMap_coeff, hi, _root_.map_zero]

theorem logFourField_degree (p : ℕ) [Fact p.Prime] :
    (logFourField p).natDegree ≤ p - 1 := by
  have he := Polynomial.natDegree_comp_le (p := (WPFiniteAffineLog.LP p : (ZMod p)[X]))
    (q := 4 * X)
  have h4 : (4 * X : (ZMod p)[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hL := WPFiniteAffineLog.LP_natDegree_le (K := ZMod p) p
  unfold logFourField
  exact he.trans (by nlinarith)

theorem logFourField_zero (p : ℕ) [Fact p.Prime] : (logFourField p).eval 0 = 0 := by
  simp only [logFourField, eval_comp, eval_mul, eval_ofNat, eval_X, mul_zero,
    WPFiniteAffineLog.LP, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
  simp [hj0]

theorem logFourField_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j ≤ 0 ∨ (p : ℤ) ≤ j) : (logFourField p).toLaurent.coeff j = 0 := by
  by_cases hj0 : j = 0
  · subst j
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, WPFiniteJCarrier.toLaurent_coeff_nat,
      coeff_zero_eq_eval_zero, logFourField_zero]
  · apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inl (by omega)
    · exact Or.inr (by have := logFourField_degree p; omega)

theorem C_mul_coeff {R : Type*} [CommRing R] (c : R)
    (F : R[T;T⁻¹]) (j : ℤ) : (LaurentPolynomial.C c * F).coeff j = c * F.coeff j := by
  rw [← LaurentPolynomial.smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]

theorem properJField_coeff (p : ℕ) [Fact p.Prime] (j : ℤ) :
    (properJField p).coeff j = (2 / 15 : ZMod p) *
      ((logFourField p).toLaurent.coeff (j + p) -
        (1 / 4 : ZMod p) * (logFourField p).toLaurent.coeff j) := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (-(p : ℤ)) j
    (logFourField p).toLaurent
  simp only [_root_.map_one, one_mul, sub_neg_eq_add] at hs
  rw [properJField, mul_assoc, C_mul_coeff, sub_mul, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, hs, C_mul_coeff]

theorem properJField_zero (p : ℕ) [Fact p.Prime] : (properJField p).coeff 0 = 0 := by
  rw [properJField_coeff, logFourField_support p _ (Or.inr (by omega)),
    logFourField_support p _ (Or.inl (by omega)), mul_zero, sub_self, mul_zero]

theorem properJField_support (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j) : (properJField p).coeff j = 0 := by
  have hp := (Fact.out : p.Prime).pos
  rw [properJField_coeff,
    logFourField_support p _ (by omega), logFourField_support p _ (by omega),
    mul_zero, sub_self, mul_zero]

/-- The same rational canonical proper primitive has its complete finite-log reduction. -/
theorem properJI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (properJI p) = properJField p := by
  rw [properJI_field_source p hp]
  apply unitPrimitive_unique p
  · rw [unitPrimitive_zero, properJField_zero]
  · exact unitPrimitive_outside p _
  · exact properJField_support p
  · have hD := unitPrimitive_source p (Fact.out : p.Prime).pos (properDensityField p)
      (properDensityField_support p hp) (signed_unit_nonzero p)
    obtain ⟨h0, hpos⟩ := properDensityField_omitted p hp
    rw [h0, hpos] at hD
    rw [hD, properJField_derivative p hp]
    simp only [neg_div, _root_.map_neg, neg_mul, sub_neg_eq_add]

end WPFieldAssembly.SourceClosureSigmaProperJ
