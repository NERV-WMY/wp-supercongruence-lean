import WPFieldAssembly.SourceClosureSigmaProductCarry
import WPFieldAssembly.SourceClosureSigmaWholePrimitive
import WPFieldAssembly.SourceClosureSigmaCanonicalTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualSigmaFiniteEvenSource WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.ActualUW16PrimitiveSource WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaProductCarry WPFieldAssembly.SourceClosureSigmaWholePrimitive
  WPFieldAssembly.SourceClosureSigmaCanonicalTransport WPFieldAssembly.SourceClosureSigmaProperEndpoint

namespace WPFieldAssembly.SourceClosureSigmaLogCarry

set_option maxHeartbeats 1500000

theorem originalFiniteEvenSquaredQ_degree (p : ℕ) :
    (finiteEvenSquaredQ p).natDegree ≤ (p - 1) / 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [finiteEvenSquaredQ, coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  apply coeff_eq_zero_of_natDegree_lt
  have hd := rationalEvenLog_degree p
  omega

theorem originalWactQ_degree (p : ℕ) [Fact p.Prime] :
    (originalWactQ p).natDegree ≤ (p - 1) / 2 := by
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
  unfold originalWactQ
  apply (natDegree_C_mul_le _ _).trans
  exact (natDegree_sub_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans hE4) hE1)

/- The logarithmic factor is cancelled as one Laurent polynomial before
canonical integration. In particular its whole positive band above p
uses actual nonresonant unit inverses, not a truncated field primitive. -/

noncomputable def originalKactI (p : ℕ) [Fact p.Prime] : (integralRationals p)[T;T⁻¹] :=
  originalKbarI p + LaurentPolynomial.C (p : integralRationals p) * originalKcarryI p

theorem originalKactI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalKactI p) = originalKactQ p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc : (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C (1 / (p : ℚ)) = 1 := by
    rw [← _root_.map_mul, mul_one_div_cancel hpq, _root_.map_one]
  rw [originalKactI, _root_.map_add, _root_.map_mul, coefficientMap_C,
    _root_.map_natCast, originalKbarI_value p hp, originalKcarryI_value p hp]
  unfold originalKactQ
  linear_combination
    (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
      T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p - originalKbarQ p) * hc

theorem originalKactI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalKactI p) = originalK0Field p := by
  have hpC : coefficientMap (residueHom p)
      (LaurentPolynomial.C (p : integralRationals p)) =
      (0 : (ZMod p)[T;T⁻¹]) := by
    rw [coefficientMap_C, _root_.map_natCast, ZMod.natCast_self, _root_.map_zero]
  simp only [originalKactI, _root_.map_add, _root_.map_mul, hpC, zero_mul, add_zero,
    originalKbarI_field p hp]

noncomputable def originalLogProductI (p : ℕ) [Fact p.Prime] : (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C (smallIntegralInverse p 2 *
      (smallIntegralInverse p 5) ^ (5 * ((p - 1) / 2))) *
    T (-(p : ℤ)) * (normAbarI p).toLaurent ^ (p - 1) *
      (originalWactI p).toLaurent * (normAbarI p).derivative.toLaurent -
    originalKactI p * (originalWactI p).toLaurent * T (-1)

theorem originalLogProductI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalLogProductI p) = originalLogProductQ p := by
  have hA : (normAbarI p).map (integralRationals p).subtype =
      (WPFiniteZSource.Abar : ℚ[X]) := by
    simp only [normAbarI, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  have hc : (integralRationals p).subtype (smallIntegralInverse p 2 *
      (smallIntegralInverse p 5) ^ (5 * ((p - 1) / 2))) =
      1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2))) := by
    have h2 : (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ) :=
      smallIntegralInverse_value p 2 (by omega) (by omega)
    have h5 : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
      smallIntegralInverse_value p 5 (by omega) (by omega)
    rw [_root_.map_mul, _root_.map_pow, h2, h5]
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  have hAD : (normAbarI p).derivative.map (integralRationals p).subtype =
      (WPFiniteZSource.Abar : ℚ[X]).derivative := by
    rw [← Polynomial.derivative_map, hA]
  have hC := congrArg (LaurentPolynomial.C : ℚ → ℚ[T;T⁻¹]) hc
  simp only [_root_.map_mul, _root_.map_pow] at hC
  simp only [originalLogProductI, _root_.map_sub, _root_.map_mul, _root_.map_pow,
    coefficientMap_C, coefficientMap_T, coefficientMap_toLaurent,
    hA, hAD, originalWactI_value p hp, originalKactI_value p hp,
    originalLogProductQ]
  rw [hC]

theorem originalWactI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalWactI p).map (residueHom p) = (WPFiniteWSource.W p : (ZMod p)[X]) := by
  have hpC : (Polynomial.C (p : integralRationals p)).map (residueHom p) =
      (0 : (ZMod p)[X]) := by
    rw [Polynomial.map_C, _root_.map_natCast, ZMod.natCast_self, Polynomial.C_0]
  rw [originalWactI, Polynomial.map_add, Polynomial.map_mul, hpC,
    zero_mul, add_zero, originalWbarI_field p hp]

noncomputable def originalLogProductField (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) *
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ (p - 1) *
      (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent *
      (WPFiniteZSource.Abar : (ZMod p)[X]).derivative.toLaurent -
    originalK0Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent * T (-1)

theorem originalLogProductI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalLogProductI p) = originalLogProductField p := by
  have hA : (normAbarI p).map (residueHom p) =
      (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    simp only [normAbarI, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  have h5 : ((5 : ZMod p)⁻¹) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one
      (inv_ne_zero (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)))
  have hN : 5 * ((p - 1) / 2) = ((p - 1) / 2) + 2 * (p - 1) := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have h5pow : ((5 : ZMod p)⁻¹) ^ (5 * ((p - 1) / 2)) =
      ((5 : ZMod p)⁻¹) ^ ((p - 1) / 2) := by
    rw [hN, pow_add, show 2 * (p - 1) = (p - 1) * 2 by omega, pow_mul, h5,
      one_pow, mul_one]
  have hc : residueHom p (smallIntegralInverse p 2 *
      (smallIntegralInverse p 5) ^ (5 * ((p - 1) / 2))) =
      1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2)) := by
    have h2 : residueHom p (smallIntegralInverse p 2) = (1 / 2 : ZMod p) := by
      simpa only [Nat.cast_ofNat, one_div] using
        smallIntegralInverse_field p 2 (by omega) (by omega)
    have h5v : residueHom p (smallIntegralInverse p 5) = (1 / 5 : ZMod p) := by
      simpa only [Nat.cast_ofNat, one_div] using
        smallIntegralInverse_field p 5 (by omega) (by omega)
    rw [_root_.map_mul, _root_.map_pow, h2, h5v]
    simp only [one_div]
    rw [h5pow]
    simp only [inv_pow, mul_inv_rev]
    ring
  have hAD : (normAbarI p).derivative.map (residueHom p) =
      (WPFiniteZSource.Abar : (ZMod p)[X]).derivative := by
    rw [← Polynomial.derivative_map, hA]
  have hC := congrArg (LaurentPolynomial.C : ZMod p → (ZMod p)[T;T⁻¹]) hc
  simp only [_root_.map_mul, _root_.map_pow] at hC
  simp only [originalLogProductI, _root_.map_sub, _root_.map_mul, _root_.map_pow,
    coefficientMap_C, coefficientMap_T, coefficientMap_toLaurent,
    hA, hAD, originalWactI_field p hp, originalKactI_field p hp,
    originalLogProductField]
  rw [hC]

noncomputable def originalLogPrimitiveI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] := nonresonantPrimitiveI p (originalLogProductI p)

noncomputable def originalLogEndSymI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] := endSym (fourUnitI p hp) (originalLogPrimitiveI p)

/-- Full existing canonical integration, before any actual endpoint or field reduction. -/
theorem originalLogEndSymI_canonical_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalLogEndSymI p hp) =
      endSym fourUnitQ (WPActualEtaPrimitive.canonicalPrimitive p (originalLogProductQ p)) := by
  rw [originalLogEndSymI, endSym_map, fourUnitI_value p hp, originalLogPrimitiveI,
    nonresonantPrimitiveI_value, originalLogProductI_value p hp]

theorem originalLogProductQ_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : j < -(p : ℤ) ∨ 2 * (p : ℤ) - 2 < j) :
    (originalLogProductQ p).coeff j = 0 := by
  let A : ℚ[X] := WPFiniteZSource.Abar
  let W : ℚ[X] := originalWactQ p
  let P1 : ℚ[X] := A ^ (p - 1) * W * A.derivative
  let P2 : ℚ[X] := A ^ p * W
  have hA : A.natDegree ≤ 2 := by
    have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by
      change (4 - X : ℚ[X]).natDegree + (4 * X - 1 : ℚ[X]).natDegree ≤ 2
      omega)
  have hAD : A.derivative.natDegree ≤ 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have hW := originalWactQ_degree p
  have hA1 := (natDegree_pow_le (p := A) (n := p - 1)).trans
    (Nat.mul_le_mul_left (p - 1) hA)
  have hAp := (natDegree_pow_le (p := A) (n := p)).trans
    (Nat.mul_le_mul_left p hA)
  have hP1 : P1.natDegree ≤ 2 * (p - 1) + (p - 1) / 2 + 1 := by
    have hmul := natDegree_mul_le (p := A ^ (p - 1)) (q := W)
    have hmul2 := natDegree_mul_le (p := A ^ (p - 1) * W) (q := A.derivative)
    change W.natDegree ≤ (p - 1) / 2 at hW
    exact hmul2.trans (by omega)
  have hP2 : P2.natDegree ≤ 2 * p + (p - 1) / 2 := by
    exact (natDegree_mul_le (p := A ^ p) (q := W)).trans (by
      change W.natDegree ≤ (p - 1) / 2 at hW
      omega)
  have hP20 : P2.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [P2, eval_mul, eval_pow, W, originalWactQ_origin, mul_zero]
  have ht : (T (-(p : ℤ)) : ℚ[T;T⁻¹]) * T (-1) = T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
  have hrepr : originalLogProductQ p =
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * P1.toLaurent -
      LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ) - 1) * P2.toLaurent := by
    simp only [originalLogProductQ, originalKactQ, P1, P2, A, W,
      _root_.map_mul, _root_.map_pow]
    linear_combination
      -LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p *
        (originalWactQ p).toLaurent * ht
  have h1 : P1.toLaurent.coeff (j + p) = 0 := by
    apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have h2 : P2.toLaurent.coeff (j + p + 1) = 0 := by
    rcases hj with hj | hj
    · by_cases hz : j + p + 1 = 0
      · rw [hz, show (0 : ℤ) = (0 : ℕ) by rfl,
          WPFiniteJCarrier.toLaurent_coeff_nat, hP20]
      · exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
    · exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  rw [hrepr]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    WPFiniteJCarrier.shifted_coeff, sub_neg_eq_add]
  simp only [show j - (-(p : ℤ) - 1) = j + p + 1 by omega, h1, h2, mul_zero,
    sub_self]

/-- UW16's literal 0,p operator equals the existing whole canonical transport on this source. -/
theorem originalLogEndSymI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalLogEndSymI p hp) =
      endSym fourUnitQ (originalJQ p (originalLogProductQ p)) := by
  rw [originalLogEndSymI_canonical_value,
    ← originalJQ_existing_canonical p (by omega) _ (originalLogProductQ_support p hp)]

/-- UW16l's entire logarithmic unit carry, including both reduced endpoints. -/
theorem originalLogEndSymI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalLogEndSymI p hp) =
      endSym (fourUnitField p hp) (nonresonantPrimitiveField p (originalLogProductField p)) := by
  rw [originalLogEndSymI, endSym_map, fourUnitI_field p hp, originalLogPrimitiveI,
    nonresonantPrimitiveI_field, originalLogProductI_field p hp]

end WPFieldAssembly.SourceClosureSigmaLogCarry
