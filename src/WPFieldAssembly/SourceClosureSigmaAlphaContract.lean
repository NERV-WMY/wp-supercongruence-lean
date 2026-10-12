import WPFieldAssembly.SourceClosureSigmaResidueCoefficient
import WPFieldAssembly.SourceClosureSigmaLogCarry
import WPFieldAssembly.SourceClosureSigmaActualCounterterm
import WPFieldAssembly.SourceClosureWEndpoint

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction WPActualRankTwoHatLift
  WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSigmaFiniteEvenSource WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.ActualUW16PrimitiveSource WPFieldAssembly.SourceClosureSigmaProperJ
  WPFieldAssembly.SourceClosureSigmaProperEndpoint WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaProductCarry WPFieldAssembly.SourceClosureSigmaWholePrimitive
  WPFieldAssembly.SourceClosureSigmaLogCarry WPFieldAssembly.SourceClosureSigmaActualCounterterm
  WPFieldAssembly.SourceClosureSigmaResidueCoefficient WPFieldAssembly.SourceClosureWEndpoint

namespace WPFieldAssembly.SourceClosureSigmaAlphaContract

set_option maxHeartbeats 1500000

noncomputable def literalEntropyI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (finiteEvenSquaredIntegral p).eval (4 * smallIntegralInverse p 5) -
    (finiteEvenSquaredIntegral p).eval (smallIntegralInverse p 5)

noncomputable def literalEntropyQ (p : ℕ) : ℚ :=
  (finiteEvenSquaredQ p).eval (4 / 5) - (finiteEvenSquaredQ p).eval (1 / 5)

theorem literalEntropyI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype (literalEntropyI p) = literalEntropyQ p := by
  have h5 : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  simp only [literalEntropyI, literalEntropyQ, _root_.map_sub, ← eval_map_apply,
    _root_.map_mul, _root_.map_ofNat, finiteEvenSquaredIntegral_value p hp,
    h5, mul_one_div]

theorem literalEntropyI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (literalEntropyI p) = squaredEntropyC p := by
  simp only [literalEntropyI, squaredEntropyC, _root_.map_sub, ← eval_map_apply,
    _root_.map_mul, _root_.map_ofNat, finiteEvenSquaredIntegral_field p hp,
    smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat,
    ← one_div, mul_one_div]

theorem originalRlogQ_resonance (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalRlogQ p).coeff ((p : ℤ) - 1) = 0 := by
  have hA : (WPFiniteZSource.Abar : ℚ[X]).natDegree ≤ 2 := by
    have hl : (4 - (X : ℚ[X])).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    have hr : (4 * (X : ℚ[X]) - 1).natDegree ≤ 1 :=
      (natDegree_sub_le _ _).trans (by simp)
    exact (natDegree_mul_le (p := (4 - X : ℚ[X])) (q := 4 * X - 1)).trans (by omega)
  have hd := (natDegree_pow_le (p := (WPFiniteZSource.Abar : ℚ[X])) (n := p - 1)).trans
    (Nat.mul_le_mul_left (p - 1) hA)
  have hz : ((WPFiniteZSource.Abar : ℚ[X]) ^ (p - 1)).toLaurent.coeff
      ((p : ℤ) - 1 + p) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  rw [originalRlogQ, ← _root_.map_pow, WPFiniteJCarrier.shifted_coeff,
    sub_neg_eq_add, hz, mul_zero]

/-- Extract the actual rational resonant coefficient from UW16b before reduction. -/
theorem actualKappaQ_integration (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualKappaQ p =
      (originalKactQ p * (originalWactQ p).toLaurent).coeff (p : ℤ) +
      properCarryQ p / (p : ℚ) * (properDensityQ p).coeff ((p : ℤ) - 1) -
      (originalLogProductQ p).coeff ((p : ℤ) - 1) := by
  have hN : 4 * ((p - 1) / 2) = 2 * (p - 1) := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have h := congrArg (fun F : ℚ[T;T⁻¹] => F.coeff ((p : ℤ) - 1))
    (originalRactQ_integration_source p hp)
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, D_coeff, sub_add_cancel, Int.cast_natCast,
    C_mul_coeff, originalHactQ, originalRlogQ_resonance p hp, zero_add, hN] at h
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold actualKappaQ
  apply (div_eq_iff hpq).2
  calc
    _ = (p : ℚ) * (originalKactQ p * (originalWactQ p).toLaurent).coeff (p : ℤ) +
        properCarryQ p * (properDensityQ p).coeff ((p : ℤ) - 1) -
        (p : ℚ) * (originalLogProductQ p).coeff ((p : ℤ) - 1) := by
      simpa only [properCarryQ, mul_assoc] using h
    _ = _ := by field_simp [hpq]

noncomputable def actualKappaI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (originalKactI p * (originalWactI p).toLaurent).coeff (p : ℤ) +
    properCarryDigitI p * (properDensityI p).coeff ((p : ℤ) - 1) -
    (originalLogProductI p).coeff ((p : ℤ) - 1)

theorem actualKappaI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype (actualKappaI p) = actualKappaQ p := by
  rw [actualKappaQ_integration p hp]
  simp only [actualKappaI, _root_.map_sub, _root_.map_add, _root_.map_mul,
    ← coefficientMap_coeff, coefficientMap_toLaurent,
    originalKactI_value p hp, originalWactI_value p hp, properCarryDigitI_value p hp,
    properDensityI_value p hp, originalLogProductI_value p hp]

theorem originalK0W_resonance (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalK0Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent).coeff
      (p : ℤ) = 0 := by
  let W := (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent
  have hw (j : ℤ) (hj : ((p - 1) / 2 - 1 : ℕ) < j) : W.coeff j = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by
      have := WPFiniteWSource.W_degree (K := ZMod p) p hp
      omega))
  have h0 : W.coeff 0 = 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, WPFiniteJCarrier.toLaurent_coeff_nat,
      WPFiniteWSource.W_origin]
  have hphase : (normPhase p * W : (ZMod p)[T;T⁻¹]).coeff (p : ℤ) =
      17 * W.coeff p - 4 * W.coeff 0 - 4 * W.coeff (2 * p) := by
    simp only [normPhase, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [show (17 : (ZMod p)[T;T⁻¹]) = LaurentPolynomial.C (17 : ZMod p) by
          simp only [_root_.map_ofNat],
      show (4 : (ZMod p)[T;T⁻¹]) = LaurentPolynomial.C (4 : ZMod p) by
          simp only [_root_.map_ofNat]]
    simp only [C_mul_coeff, WPFiniteJCarrier.shifted_coeff, sub_self, sub_neg_eq_add,
      show (p : ℤ) + p = 2 * p by omega]
  rw [originalK0Field, mul_assoc, C_mul_coeff, hphase, h0,
    hw _ (by omega), hw _ (by omega)]
  ring

/-- The cancelled logarithmic source sees both original endpoints at its resonant coefficient. -/
theorem originalLogProductField_resonance (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalLogProductField p).coeff ((p : ℤ) - 1) =
      -(2 / WPFiniteABSourceTail.epsilon p : ZMod p) *
        ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have heps : (5 : ZMod p) ^ ((p - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hscalar : (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) * (-4) =
      -(2 / (5 : ZMod p) ^ ((p - 1) / 2)) := by
    field_simp [h2, heps]
    ring
  have hc4 : (Polynomial.C (4 : ZMod p) : (ZMod p)[X]) * Polynomial.C (1 / 4) = 1 := by
    rw [← Polynomial.C_mul, mul_one_div_cancel h4, Polynomial.C_1]
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]) =
      Polynomial.C (-4) * (X - Polynomial.C (1 / 4)) * (X - Polynomial.C 4) := by
    unfold WPFiniteZSource.Abar
    rw [Polynomial.C_neg]
    change (4 - X) * (4 * X - 1) = -4 * (X - Polynomial.C (1 / 4)) * (X - 4)
    simp only [_root_.map_ofNat] at hc4
    linear_combination -(X - 4) * hc4
  have hW : (WPFiniteWSource.W p : (ZMod p)[X]).natDegree < p := by
    have := WPFiniteWSource.W_degree (K := ZMod p) p hp
    omega
  have hhigh := quadratic_log_high_coeff (K := ZMod p) p (by omega)
    (1 / 4) 4 (-4) (neg_ne_zero.mpr h4) (ZMod.pow_card _) (ZMod.pow_card _)
    (ZMod.pow_card _) (WPFiniteWSource.W p) hW
  rw [← hA] at hhigh
  let P : (ZMod p)[X] := (WPFiniteZSource.Abar : (ZMod p)[X]) ^ (p - 1) *
    (WPFiniteWSource.W p) * (WPFiniteZSource.Abar : (ZMod p)[X]).derivative
  have hP : P.coeff (2 * p - 1) = -4 *
      ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) := by
    have hcomm : P = (WPFiniteZSource.Abar : (ZMod p)[X]) ^ (p - 1) *
        (WPFiniteZSource.Abar : (ZMod p)[X]).derivative * WPFiniteWSource.W p := by
      dsimp only [P]
      ring
    rw [hcomm]
    exact hhigh
  have hrepr : originalLogProductField p =
      LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) * T (-(p : ℤ)) *
        P.toLaurent -
      LaurentPolynomial.C (1 : ZMod p) * T (-1) *
        (originalK0Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent) := by
    dsimp only [originalLogProductField, P]
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_one]
    ring
  rw [hrepr, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    WPFiniteJCarrier.shifted_coeff, WPFiniteJCarrier.shifted_coeff,
    sub_neg_eq_add, show (p : ℤ) - 1 + p = ((2 * p - 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat, hP,
    show (p : ℤ) - 1 - (-1) = p by omega, originalK0W_resonance p hp, mul_zero,
    sub_zero, WPFiniteABSourceTail.epsilon]
  rw [← mul_assoc, hscalar]

/-- Kappa is the original rational residue divided by p, with its exact integral realization. -/
theorem actualKappaI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (actualKappaI p) =
      2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15 +
      2 / WPFiniteABSourceTail.epsilon p *
        ((WPFiniteWSource.W p).eval (1 / 4) + (WPFiniteWSource.W p).eval 4) := by
  simp only [actualKappaI, _root_.map_sub, _root_.map_add, _root_.map_mul,
    ← coefficientMap_coeff, coefficientMap_toLaurent,
    originalKactI_field p hp, originalWactI_field p hp, properCarryDigitI_field p hp,
    properDensityI_field p hp, originalLogProductI_field p hp,
    originalK0W_resonance p hp, (properDensityField_omitted p hp).2,
    originalLogProductField_resonance p hp]
  ring

noncomputable def actualAlphaFromSourceI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  actualKappaI p + 8 * literalEntropyI p * smallIntegralInverse p 15

theorem actualAlphaFromSourceI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype (actualAlphaFromSourceI p) =
      actualAlphaQ p (literalEntropyQ p) := by
  have h15 : (integralRationals p).subtype (smallIntegralInverse p 15) = (1 / 15 : ℚ) :=
    smallIntegralInverse_value p 15 (by omega) (by omega)
  simp only [actualAlphaFromSourceI, actualAlphaQ, _root_.map_add, _root_.map_mul,
    _root_.map_ofNat, actualKappaI_value p hp, literalEntropyI_value p hp,
    h15]
  ring

/-- SB86's actual alpha contracts uniformly, including the full original literal entropy. -/
theorem actualAlphaFromSourceI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (actualAlphaFromSourceI p) =
      -(2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 15 := by
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p) ≠ 0 :=
    pow_ne_zero _ (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have h15 : (15 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 15 (by omega) (by omega)
  have h30 : (30 : ZMod p) ≠ 0 := by
    rw [show (30 : ZMod p) = 2 * 15 by ring]
    exact mul_ne_zero
      (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)) h15
  have hends := actual_W_endpoint_balance (K := ZMod p) p hp
  unfold WPFiniteNC122.q at hends
  have hsum : (WPFiniteWSource.W p : (ZMod p)[X]).eval (1 / 4) +
      (WPFiniteWSource.W p).eval 4 =
        -(WPFiniteABSourceTail.epsilon p : ZMod p) *
          (4 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
            3 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) / 30 -
        4 * WPFiniteABSourceTail.epsilon p * squaredEntropyC p / 15 := by
    linear_combination hends
  simp only [actualAlphaFromSourceI, _root_.map_add, _root_.map_mul, _root_.map_ofNat,
    actualKappaI_field p hp, literalEntropyI_field p hp,
    smallIntegralInverse_field p 15 (by omega) (by omega), Nat.cast_ofNat, ← one_div]
  rw [hsum]
  field_simp [heps, h15, h30]
  ring

end WPFieldAssembly.SourceClosureSigmaAlphaContract
