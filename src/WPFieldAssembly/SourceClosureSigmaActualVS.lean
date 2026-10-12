import WPFieldAssembly.SourceClosureSigmaActualCounterterm
import WPFieldAssembly.ActualSigmaSourceAttachment
import WPFieldAssembly.SourceClosureSigmaComparisonTransport
import WPFieldAssembly.SourceClosureSigmaWholeCarry
import WPFieldAssembly.SourceClosureSigmaWholeSupport
import WPFieldAssembly.SourceClosureSigmaAlphaContract
import WPFieldAssembly.SourceClosureSigmaRingDerivative

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureSigmaActualCounterterm
  WPFieldAssembly.ActualSigmaSourceAttachment
  WPFieldAssembly.ActualSigmaClearedSource
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualHFTransmutation
  WPFieldAssembly.SourceClosureSigmaWholeCarry
  WPFieldAssembly.SourceClosureSigmaComparisonTransport
  WPFieldAssembly.SourceClosureSigmaAlphaContract
  WPFieldAssembly.ActualUW16PrimitiveSource

namespace WPFieldAssembly.SourceClosureSigmaActualVS

set_option maxHeartbeats 1500000

/-- The finite derivative keeps its coefficient formula over the integral ring. -/
theorem ringD_coeff {R : Type*} [CommRing R] (F : R[T;T⁻¹]) (j : ℤ) :
    (ringD F).coeff j = ((j + 1 : ℤ) : R) * F.coeff (j + 1) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      hF, hG, mul_add]
  | C_mul_T n a =>
    rw [ringD_monomial]
    by_cases hn : n = j + 1
    · subst n
      have hs : j + 1 - 1 = j := by omega
      simp only [SourceClosureSigmaProperJ.coeff_unit_monomial, hs, if_true]
      ring
    · have hn1 : n - 1 ≠ j := by omega
      simp only [SourceClosureSigmaProperJ.coeff_unit_monomial,
        if_neg hn, if_neg hn1, mul_zero]

/- This quotient subtracts the existing actual comparison over Q.
The two endpoint powers and literal C are carried by SB86 before
division. Integral and field attachment require the entire first carry. -/

noncomputable def actualVSQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (literalC : ℚ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (p : ℚ)) *
    (actualSB86CountertermQ p literalC - comparisonRational p hp)

/-- The exact actual rational divided source, with no derivative identification premise. -/
theorem actualVSQ_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (literalC : ℚ) :
    D (actualVSQ p hp literalC) = -actualSigmaQ p hp -
      LaurentPolynomial.C (actualAlphaQ p literalC) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : (LaurentPolynomial.C (1 / (p : ℚ)) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C ((p : ℚ) * actualAlphaQ p literalC) =
        LaurentPolynomial.C (actualAlphaQ p literalC) := by
    rw [← _root_.map_mul]
    congr 1
    field_simp [hpq]
  rw [actualVSQ, D_C_mul, _root_.map_sub,
    actualSB86CountertermQ_derivative p hp, ← actual_Bsource_original,
    actualSigmaQ]
  linear_combination
    -(T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * hc

/-- The original counterterm is recovered by genuine rational multiplication by p. -/
theorem actualVSQ_whole_division (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (literalC : ℚ) :
    actualSB86CountertermQ p literalC = comparisonRational p hp +
      LaurentPolynomial.C (p : ℚ) * actualVSQ p hp literalC := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C (1 / (p : ℚ)) = 1 := by
    rw [← _root_.map_mul, mul_one_div_cancel hpq, _root_.map_one]
  unfold actualVSQ
  linear_combination
    -(actualSB86CountertermQ p literalC - comparisonRational p hp) * hc

theorem actualComparisonQ_reflection_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (comparisonRational p hp) = comparisonRational p hp ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) SourceClosureSigmaProperEndpoint.fourUnitQ
        (comparisonRational p hp) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) SourceClosureSigmaProperEndpoint.fourUnitQ⁻¹
        (comparisonRational p hp) = 0 := by
  rw [← originalSbarQ_actual_comparison p hp, SourceClosureSigmaWholePrimitive.originalSbarQ]
  have hP := endSym_endpoints
    (SourceClosureSigmaWholePrimitive.originalCanQ p
      (SourceClosureSigmaKCarry.originalKbarQ p * (originalWbarQ p).toLaurent))
  have hZ := endSym_endpoints (T (p : ℤ) : ℚ[T;T⁻¹])
  constructor
  · rw [_root_.map_sub, _root_.map_mul, invert_C, endSym_inversion,
      SourceClosureSigmaWholePrimitive.originalZpQ, endSym_inversion]
  · simp only [_root_.map_sub, _root_.map_mul, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, SourceClosureSigmaWholePrimitive.originalZpQ,
      hP.1, hP.2, hZ.1, hZ.2, mul_zero, sub_zero, and_self]

/-- The actual rational divided counterterm retains both original endpoints and reflection. -/
theorem actualVSQ_reflection_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (literalC : ℚ) :
    invert (actualVSQ p hp literalC) = actualVSQ p hp literalC ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) SourceClosureSigmaProperEndpoint.fourUnitQ
        (actualVSQ p hp literalC) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) SourceClosureSigmaProperEndpoint.fourUnitQ⁻¹
        (actualVSQ p hp literalC) = 0 := by
  obtain ⟨hS, hSb, hSa⟩ := actualSB86CountertermQ_reflection_endpoints p literalC
  obtain ⟨hB, hBb, hBa⟩ := actualComparisonQ_reflection_endpoints p hp
  constructor
  · rw [actualVSQ, _root_.map_mul, _root_.map_sub, invert_C, hS, hB]
  · simp only [actualVSQ, _root_.map_mul, _root_.map_sub, hSb, hSa, hBb, hBa,
      sub_self, mul_zero, and_self]

/-- The actual whole quotient has the explicit original integral first-carry realization. -/
theorem actualVSIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
      (originalWholeVSI p hp) = actualVSQ p hp (originalLiteralCQ p) := by
  rw [originalWholeVSI_value p hp (originalLiteralCQ p),
    originalSbarQ_actual_comparison p hp, actualVSQ,
    actualSB86CountertermQ_identification]

theorem actualVSIntegral_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (WPPIntegralReduction.integralRationals p))
      (SourceClosureSigmaProperEndpoint.fourUnitI p hp) (originalWholeVSI p hp) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (WPPIntegralReduction.integralRationals p))
        (SourceClosureSigmaProperEndpoint.fourUnitI p hp)⁻¹ (originalWholeVSI p hp) = 0 := by
  obtain ⟨_, hb, ha⟩ := actualVSQ_reflection_endpoints p hp (originalLiteralCQ p)
  constructor
  · apply Subtype.ext
    change (WPPIntegralReduction.integralRationals p).subtype
      (LaurentPolynomial.eval₂ (RingHom.id (WPPIntegralReduction.integralRationals p))
        (SourceClosureSigmaProperEndpoint.fourUnitI p hp) (originalWholeVSI p hp)) =
      (WPPIntegralReduction.integralRationals p).subtype (0 : WPPIntegralReduction.integralRationals p)
    rw [SourceClosureSigmaProperEndpoint.eval₂_map,
      SourceClosureSigmaProperEndpoint.fourUnitI_value p hp, actualVSIntegral_value p hp,
      hb, _root_.map_zero]
  · apply Subtype.ext
    change (WPPIntegralReduction.integralRationals p).subtype
      (LaurentPolynomial.eval₂ (RingHom.id (WPPIntegralReduction.integralRationals p))
        (SourceClosureSigmaProperEndpoint.fourUnitI p hp)⁻¹ (originalWholeVSI p hp)) =
      (WPPIntegralReduction.integralRationals p).subtype (0 : WPPIntegralReduction.integralRationals p)
    rw [SourceClosureSigmaProperEndpoint.eval₂_map, map_inv,
      SourceClosureSigmaProperEndpoint.fourUnitI_value p hp, actualVSIntegral_value p hp,
      ha, _root_.map_zero]

theorem actualVSIntegral_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (originalWholeVSI p hp) = originalWholeVSI p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
  rw [invert_coefficientMap, actualVSIntegral_value p hp,
    (actualVSQ_reflection_endpoints p hp (originalLiteralCQ p)).1]

noncomputable def actualAlphaIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPPIntegralReduction.integralRationals p :=
  -(ActualSigmaIntegral.actualSigmaIntegral p hp).coeff ((p : ℤ) - 1) -
    (p : WPPIntegralReduction.integralRationals p) * (originalWholeVSI p hp).coeff (p : ℤ)

/-- The actual resonant scalar is integral by the same whole quotient, without assigning its residue. -/
theorem actualAlphaIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p).subtype (actualAlphaIntegral p hp) =
      actualAlphaQ p (originalLiteralCQ p) := by
  have hd := congrArg (fun F : ℚ[T;T⁻¹] => F.coeff ((p : ℤ) - 1))
    (actualVSQ_derivative p hp (originalLiteralCQ p))
  rw [D_coeff] at hd
  simp only [sub_add_cancel, Int.cast_natCast, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_neg, Finsupp.sub_apply, Finsupp.neg_apply,
    SourceClosureSigmaProperJ.C_mul_coeff] at hd
  have hT1 : (T ((p : ℤ) - 1) : ℚ[T;T⁻¹]).coeff ((p : ℤ) - 1) = 1 := by
    simpa only [_root_.map_one, one_mul, if_true] using
      SourceClosureSigmaProperJ.coeff_unit_monomial (1 : ℚ) ((p : ℤ) - 1) ((p : ℤ) - 1)
  have hT2 : (T (-(p : ℤ) - 1) : ℚ[T;T⁻¹]).coeff ((p : ℤ) - 1) = 0 := by
    simpa only [_root_.map_one, one_mul, if_neg (by omega : -(p : ℤ) - 1 ≠ (p : ℤ) - 1)] using
      SourceClosureSigmaProperJ.coeff_unit_monomial (1 : ℚ) (-(p : ℤ) - 1) ((p : ℤ) - 1)
  rw [hT1, hT2, sub_zero, mul_one] at hd
  simp only [actualAlphaIntegral, _root_.map_sub, _root_.map_neg, _root_.map_mul,
    _root_.map_natCast, ← WPActualChiSource.coefficientMap_coeff,
    ActualSigmaIntegral.actualSigmaIntegral_value, actualVSIntegral_value]
  linear_combination -hd

theorem actualVSIntegral_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ringD (originalWholeVSI p hp) = -ActualSigmaIntegral.actualSigmaIntegral p hp -
      LaurentPolynomial.C (actualAlphaIntegral p hp) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
  rw [ringD_coefficientMap, ringD_field, actualVSIntegral_value, actualVSQ_derivative]
  simp only [_root_.map_sub, _root_.map_neg, _root_.map_mul,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    ActualSigmaIntegral.actualSigmaIntegral_value, actualAlphaIntegral_value]

noncomputable def actualVSField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) (originalWholeVSI p hp)

theorem actualVSField_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
      (SourceClosureSigmaProperEndpoint.fourUnitField p hp) (actualVSField p hp) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
        (SourceClosureSigmaProperEndpoint.fourUnitField p hp)⁻¹ (actualVSField p hp) = 0 := by
  obtain ⟨hb, ha⟩ := actualVSIntegral_endpoints p hp
  have hbf := congrArg (WPPIntegralReduction.residueHom p) hb
  have haf := congrArg (WPPIntegralReduction.residueHom p) ha
  rw [SourceClosureSigmaProperEndpoint.eval₂_map,
    SourceClosureSigmaProperEndpoint.fourUnitI_field p hp, _root_.map_zero] at hbf
  rw [SourceClosureSigmaProperEndpoint.eval₂_map, map_inv,
    SourceClosureSigmaProperEndpoint.fourUnitI_field p hp, _root_.map_zero] at haf
  exact ⟨hbf, haf⟩

theorem actualVSField_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (actualVSField p hp) = actualVSField p hp := by
  rw [actualVSField, ← invert_coefficientMap, actualVSIntegral_reflection p hp]

/-- Genuine field reduction of the actual integral derivative; alpha's closed residue is separate. -/
theorem actualVSField_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (actualVSField p hp) =
      -WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
        (ActualSigmaIntegral.actualSigmaIntegral p hp) -
      LaurentPolynomial.C (WPPIntegralReduction.residueHom p (actualAlphaIntegral p hp)) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  rw [actualVSField, ← ringD_field, ← ringD_coefficientMap, actualVSIntegral_derivative]
  simp only [_root_.map_sub, _root_.map_neg, _root_.map_mul,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T]

/-- The resonant scalar obtained from the actual divided source is the original SB86 scalar. -/
theorem actualAlphaIntegral_from_original_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualAlphaIntegral p hp = actualAlphaFromSourceI p := by
  apply Subtype.ext
  change (WPPIntegralReduction.integralRationals p).subtype (actualAlphaIntegral p hp) =
    (WPPIntegralReduction.integralRationals p).subtype (actualAlphaFromSourceI p)
  rw [actualAlphaIntegral_value p hp, actualAlphaFromSourceI_value p hp]
  rfl

/-- The complete actual integral Frobenius density family is fixed before
reduction. The derivative's zero multiplier at j=0 uses no value for VS[0]. -/
theorem actualSigmaIntegral_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (ActualSigmaIntegral.actualSigmaIntegral p hp).coeff (j - 1) =
      if j = (p : ℤ) then -actualAlphaFromSourceI p
      else if j = -(p : ℤ) then actualAlphaFromSourceI p else 0 := by
  have hD0 : (ringD (originalWholeVSI p hp)).coeff (j - 1) = 0 := by
    rw [ringD_coeff, sub_add_cancel]
    by_cases hj0 : j = 0
    · subst j
      simp only [Int.cast_zero, zero_mul]
    · rw [SourceClosureSigmaWholeSupport.originalWholeVSI_nonzero_frobenius
        p hp j hj hj0, mul_zero]
  have hd := congrArg (fun F : (WPPIntegralReduction.integralRationals p)[T;T⁻¹] =>
      F.coeff (j - 1)) (actualVSIntegral_derivative p hp)
  rw [hD0] at hd
  have hT (n : ℤ) : (T (n - 1) :
      (WPPIntegralReduction.integralRationals p)[T;T⁻¹]).coeff (j - 1) =
        if j = n then 1 else 0 := by
    by_cases hjn : j = n
    · subst j
      simpa only [_root_.map_one, one_mul, if_true] using
        SourceClosureSigmaProperJ.coeff_unit_monomial
          (1 : WPPIntegralReduction.integralRationals p) (n - 1) (n - 1)
    · have hn : n - 1 ≠ j - 1 := by omega
      simpa only [_root_.map_one, one_mul, if_neg hn, if_neg hjn] using
        SourceClosureSigmaProperJ.coeff_unit_monomial
          (1 : WPPIntegralReduction.integralRationals p) (n - 1) (j - 1)
  simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_neg,
    Finsupp.sub_apply, Finsupp.neg_apply, SourceClosureSigmaProperJ.C_mul_coeff,
    hT, actualAlphaIntegral_from_original_source p hp] at hd
  by_cases hpos : j = (p : ℤ)
  · have hneg : j ≠ -(p : ℤ) := by omega
    simp only [if_pos hpos, if_neg hneg] at hd ⊢
    linear_combination hd
  · by_cases hneg : j = -(p : ℤ)
    · simp only [if_neg hpos, if_pos hneg] at hd ⊢
      linear_combination hd
    · simp only [if_neg hpos, if_neg hneg] at hd ⊢
      linear_combination hd

/-- Both original integral resonances are the specializations of the same family. -/
theorem actualSigmaIntegral_resonant_pair (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ActualSigmaIntegral.actualSigmaIntegral p hp).coeff ((p : ℤ) - 1) =
        -actualAlphaFromSourceI p ∧
      (ActualSigmaIntegral.actualSigmaIntegral p hp).coeff (-(p : ℤ) - 1) =
        actualAlphaFromSourceI p := by
  constructor
  · simpa only [if_true] using actualSigmaIntegral_frobenius p hp p (dvd_refl _)
  · simpa only [if_neg (by omega : -(p : ℤ) ≠ (p : ℤ)), if_true] using
      actualSigmaIntegral_frobenius p hp (-(p : ℤ)) (dvd_neg.mpr (dvd_refl _))

theorem actualAlphaIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPPIntegralReduction.residueHom p (actualAlphaIntegral p hp) =
      -(2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 15 := by
  rw [actualAlphaIntegral_from_original_source p hp, actualAlphaFromSourceI_field p hp]

/-- The same actual sigma has its full field Frobenius density, with closed alpha. -/
theorem actualSigmaField_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (ActualSigmaIntegral.actualSigmaIntegral p hp)).coeff (j - 1) =
      if j = (p : ℤ) then
        (2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
          3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 15
      else if j = -(p : ℤ) then
        -(2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
          3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 15
      else 0 := by
  rw [WPActualChiSource.coefficientMap_coeff, actualSigmaIntegral_frobenius p hp j hj]
  by_cases hpos : j = (p : ℤ)
  · simp only [if_pos hpos, _root_.map_neg, actualAlphaFromSourceI_field p hp]
    ring
  · by_cases hneg : j = -(p : ℤ)
    · simp only [if_neg hpos, if_pos hneg, actualAlphaFromSourceI_field p hp]
    · simp only [if_neg hpos, if_neg hneg, _root_.map_zero]

/-- Sigma's logarithmic residue is zero; VS retains its own endpoint origin. -/
theorem actualSigmaField_log_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (ActualSigmaIntegral.actualSigmaIntegral p hp)).coeff (-1) = 0 := by
  simpa only [zero_sub, if_neg (by omega : (0 : ℤ) ≠ (p : ℤ)),
    if_neg (by omega : (0 : ℤ) ≠ -(p : ℤ))] using
      actualSigmaField_frobenius p hp 0 (dvd_zero _)

/-- The full actual VS has its unconditional derivative with the original closed alpha. -/
theorem actualVSField_derivative_closed (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (actualVSField p hp) =
      -WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
        (ActualSigmaIntegral.actualSigmaIntegral p hp) -
      LaurentPolynomial.C
        (-(2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
          3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 15) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  rw [actualVSField_derivative p hp, actualAlphaIntegral_field p hp]

end WPFieldAssembly.SourceClosureSigmaActualVS
