import WPFieldAssembly.SourceClosureSigmaKCarry
import WPFieldAssembly.SourceClosureSigmaProperEndpoint
import WPFieldAssembly.ActualUW16PrimitiveSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPActualRankTwoHatLift WPFieldAssembly.ActualSigmaFiniteEvenSource
  WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaProperJ
  WPFieldAssembly.SourceClosureSigmaProperEndpoint

namespace WPFieldAssembly.SourceClosureSigmaProductCarry

set_option maxHeartbeats 1400000

noncomputable def originalE1CenteredI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  (finiteEvenSquaredIntegral p).comp (originalSquaredCoordinateI p) -
    Polynomial.C ((finiteEvenSquaredIntegral p).eval (smallIntegralInverse p 5))

noncomputable def originalWbarI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  Polynomial.C (2 * (5 : integralRationals p) ^ ((p - 1) / 2) * smallIntegralInverse p 15) *
    (originalE4CenteredI p - originalE1CenteredI p)

noncomputable def originalWactI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  originalWbarI p + Polynomial.C (p : integralRationals p) * originalW1Integral p

theorem originalE1CenteredI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalE1CenteredI p).map (integralRationals p).subtype = originalE1CenteredQ p := by
  have hs : (originalSquaredCoordinateI p).map (integralRationals p).subtype =
      (WPFiniteWSource.squaredCoordinate : ℚ[X]) := by
    simp only [originalSquaredCoordinateI, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
    change Polynomial.C (smallIntegralInverse p 5).val * (X + 1) = _
    rw [smallIntegralInverse_value p 5 (by omega) (by omega)]
    simp only [WPFiniteWSource.squaredCoordinate, one_div, Nat.cast_ofNat]
  have he : (integralRationals p).subtype
      ((finiteEvenSquaredIntegral p).eval (smallIntegralInverse p 5)) =
        (finiteEvenSquaredQ p).eval (1 / 5) := by
    rw [← eval_map_apply, finiteEvenSquaredIntegral_value p hp]
    congr 1
    exact smallIntegralInverse_value p 5 (by omega) (by omega)
  simp only [originalE1CenteredI, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_C, finiteEvenSquaredIntegral_value p hp, hs, he, originalE1CenteredQ]

theorem originalE1CenteredI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalE1CenteredI p).map (residueHom p) =
      (WPFiniteLVSource.evenSquared p).comp WPFiniteWSource.squaredCoordinate -
        Polynomial.C ((WPFiniteLVSource.evenSquared p).eval (1 / 5)) := by
  have hs : (originalSquaredCoordinateI p).map (residueHom p) =
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]) := by
    simp only [originalSquaredCoordinateI, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
      smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat,
      WPFiniteWSource.squaredCoordinate]
  have he : residueHom p
      ((finiteEvenSquaredIntegral p).eval (smallIntegralInverse p 5)) =
        (WPFiniteLVSource.evenSquared p).eval (1 / 5) := by
    rw [← eval_map_apply, finiteEvenSquaredIntegral_field p hp,
      smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [Nat.cast_ofNat, one_div]
  simp only [originalE1CenteredI, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_C, finiteEvenSquaredIntegral_field p hp, hs, he]

theorem originalWbarI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalWbarI p).map (integralRationals p).subtype = originalWbarQ p := by
  have h15 : (integralRationals p).subtype (smallIntegralInverse p 15) = (1 / 15 : ℚ) :=
    smallIntegralInverse_value p 15 (by omega) (by omega)
  have hc : (integralRationals p).subtype
      (2 * (5 : integralRationals p) ^ ((p - 1) / 2) * smallIntegralInverse p 15) =
      2 * (5 : ℚ) ^ ((p - 1) / 2) / 15 := by
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_ofNat, h15]
    ring
  rw [originalWbarI, Polynomial.map_mul, Polynomial.map_C, hc, Polynomial.map_sub,
    originalE4CenteredI_value p hp, originalE1CenteredI_value p hp]
  rfl

/-- Wact is the actual rational polynomial, with Wbar's p-divisible degree-N band retained. -/
theorem originalWactI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalWactI p).map (integralRationals p).subtype = originalWactQ p := by
  rw [originalWactI, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    _root_.map_natCast, originalWbarI_value p hp, originalW1Integral_value p hp]
  linear_combination -originalWactQ_first_difference p

theorem evenSquared_difference (p : ℕ) [Fact p.Prime] :
    (WPFiniteLVSource.evenSquared p : (ZMod p)[X]).comp (4 * X) -
      WPFiniteLVSource.evenSquared p = WPFiniteWSource.deltaE p := by
  simp only [WPFiniteLVSource.evenSquared, WPFiniteWSource.deltaE, sum_comp,
    mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (4 : (ZMod p)[X]) ^ j = Polynomial.C ((4 : ZMod p) ^ j) by
    rw [Polynomial.C_pow, _root_.map_ofNat]]
  simp only [div_eq_mul_inv, _root_.map_sub, _root_.map_mul, _root_.map_one]
  ring

theorem originalWbarI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalWbarI p).map (residueHom p) = (WPFiniteWSource.W p : (ZMod p)[X]) := by
  have hdelta := evenSquared_difference p
  have hs := congrArg (fun F : (ZMod p)[X] => F.comp WPFiniteWSource.squaredCoordinate) hdelta
  have he := congrArg (fun F : (ZMod p)[X] => F.eval (1 / 5)) hdelta
  simp only [sub_comp, comp_assoc, mul_comp, ofNat_comp, X_comp] at hs
  simp only [eval_sub, eval_comp, eval_mul, eval_ofNat, eval_X] at he
  have harg : (4 : ZMod p) * (1 / 5) = 4 / 5 := by ring
  rw [harg] at he
  have hC := congrArg Polynomial.C he
  simp only [_root_.map_sub] at hC
  have hc : residueHom p
      (2 * (5 : integralRationals p) ^ ((p - 1) / 2) * smallIntegralInverse p 15) =
      2 * (5 : ZMod p) ^ ((p - 1) / 2) / 15 := by
    simp only [_root_.map_mul, _root_.map_pow, _root_.map_ofNat,
      smallIntegralInverse_field p 15 (by omega) (by omega), Nat.cast_ofNat]
    ring
  rw [originalWbarI, Polynomial.map_mul, Polynomial.map_C, hc, Polynomial.map_sub,
    originalE4CenteredI_field p hp, originalE1CenteredI_field p hp]
  unfold originalE4CenteredField WPFiniteWSource.W WPFiniteABSourceTail.epsilon
  linear_combination
    Polynomial.C (2 * (5 : ZMod p) ^ ((p - 1) / 2) / 15) * (hs - hC)

noncomputable def originalKbarI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C
      (smallIntegralInverse p 2 * (smallIntegralInverse p 5) ^ ((p - 1) / 2)) * normPhase p

noncomputable def originalProductCarryI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  originalKcarryI p * (originalWbarI p).toLaurent +
    originalKbarI p * (originalW1Integral p).toLaurent +
      LaurentPolynomial.C (p : integralRationals p) *
        originalKcarryI p * (originalW1Integral p).toLaurent

theorem originalKbarI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalKbarI p) = originalKbarQ p := by
  have h2 : (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ) :=
    smallIntegralInverse_value p 2 (by omega) (by omega)
  have h5 : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  have hc : (integralRationals p).subtype
      (smallIntegralInverse p 2 * (smallIntegralInverse p 5) ^ ((p - 1) / 2)) =
      1 / (2 * (5 : ℚ) ^ ((p - 1) / 2)) := by
    rw [_root_.map_mul, _root_.map_pow, h2, h5]
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  rw [originalKbarI, _root_.map_mul, coefficientMap_C, hc, originalKbarQ]
  simp only [normPhase, _root_.map_sub, _root_.map_mul,
    _root_.map_ofNat, coefficientMap_T]

theorem originalKbarI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalKbarI p) = originalK0Field p := by
  have hc : residueHom p
      (smallIntegralInverse p 2 * (smallIntegralInverse p 5) ^ ((p - 1) / 2)) =
      1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2)) := by
    simp only [_root_.map_mul, _root_.map_pow,
      smallIntegralInverse_field p 2 (by omega) (by omega),
      smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat]
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  rw [originalKbarI, _root_.map_mul, coefficientMap_C, hc, originalK0Field]
  simp only [normPhase, _root_.map_sub, _root_.map_mul,
    _root_.map_ofNat, coefficientMap_T]

/-- The entire original product carry, before either canonical slot or endpoint is removed. -/
theorem originalProductCarryI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalProductCarryI p) =
      LaurentPolynomial.C (1 / (p : ℚ)) *
        (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
          T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p *
            (originalWactQ p).toLaurent - originalKbarQ p * (originalWbarQ p).toLaurent) := by
  have hw := congrArg Polynomial.toLaurent (originalWactQ_first_difference p)
  simp only [_root_.map_sub, _root_.map_mul, Polynomial.toLaurent_C] at hw
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : (LaurentPolynomial.C (1 / (p : ℚ)) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C (p : ℚ) = 1 := by
    rw [← _root_.map_mul, one_div_mul_cancel hpq, _root_.map_one]
  have hpC : coefficientMap (integralRationals p).subtype
      (LaurentPolynomial.C (p : integralRationals p)) =
      (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹]) := by
    rw [coefficientMap_C, _root_.map_natCast]
  rw [originalProductCarryI]
  simp only [_root_.map_add, _root_.map_mul, hpC,
    originalKcarryI_value p hp, originalKbarI_value p hp, coefficientMap_toLaurent,
    originalWbarI_value p hp, originalW1Integral_value p hp]
  linear_combination
    -LaurentPolynomial.C (1 / (p : ℚ)) *
      (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
        T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p) * hw -
    originalKbarQ p * (originalW1Q p).toLaurent * hu

theorem originalProductCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalProductCarryI p) =
      originalK1Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent +
        originalK0Field p *
          (Polynomial.C (-2 * (5 : ZMod p) ^ ((p - 1) / 2) *
            (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) *
              originalE4CenteredField p).toLaurent := by
  have hpC : coefficientMap (residueHom p)
      (LaurentPolynomial.C (p : integralRationals p)) =
      (0 : (ZMod p)[T;T⁻¹]) := by
    rw [coefficientMap_C, _root_.map_natCast, ZMod.natCast_self, _root_.map_zero]
  simp only [originalProductCarryI, _root_.map_add, _root_.map_mul,
    hpC,
    zero_mul, add_zero, coefficientMap_toLaurent, originalWbarI_field p hp,
    originalW1Integral_field p hp, originalKcarryI_field p hp, originalKbarI_field p hp]

noncomputable def canSlots {R : Type*} [CommRing R] (p : ℕ) (F : R[T;T⁻¹]) : R[T;T⁻¹] :=
  F - LaurentPolynomial.C (F.coeff 0) - LaurentPolynomial.C (F.coeff (p : ℤ)) * T (p : ℤ)

theorem canSlots_sub {R : Type*} [CommRing R] (p : ℕ) (F G : R[T;T⁻¹]) :
    canSlots p (F - G) = canSlots p F - canSlots p G := by
  simp only [canSlots, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, _root_.map_sub]
  ring

theorem canSlots_C_mul {R : Type*} [CommRing R] (p : ℕ) (c : R) (F : R[T;T⁻¹]) :
    canSlots p (LaurentPolynomial.C c * F) = LaurentPolynomial.C c * canSlots p F := by
  simp only [canSlots, C_mul_coeff, _root_.map_mul]
  ring

theorem canSlots_map {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* S) (F : R[T;T⁻¹]) :
    coefficientMap f (canSlots p F) = canSlots p (coefficientMap f F) := by
  simp only [canSlots, _root_.map_sub, _root_.map_mul, coefficientMap_C,
    coefficientMap_T, coefficientMap_coeff]

noncomputable def originalProductEndSymI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  endSym (fourUnitI p hp) (canSlots p (originalProductCarryI p))

/-- Both canonical holes and actual rational ends are transported after the whole p-division. -/
theorem originalProductEndSymI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalProductEndSymI p hp) =
      LaurentPolynomial.C (1 / (p : ℚ)) *
        (endSym fourUnitQ (canSlots p
            (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
              T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p *
                (originalWactQ p).toLaurent)) -
          endSym fourUnitQ (canSlots p (originalKbarQ p * (originalWbarQ p).toLaurent))) := by
  rw [originalProductEndSymI, endSym_map, fourUnitI_value p hp, canSlots_map,
    originalProductCarryI_value p hp, canSlots_C_mul, canSlots_sub,
    endSym_C_mul, endSym_sub]

theorem originalProductEndSymI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalProductEndSymI p hp) =
      endSym (fourUnitField p hp) (canSlots p
        (originalK1Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent +
          originalK0Field p *
            (Polynomial.C (-2 * (5 : ZMod p) ^ ((p - 1) / 2) *
              (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) *
                originalE4CenteredField p).toLaurent)) := by
  rw [originalProductEndSymI, endSym_map, fourUnitI_field p hp, canSlots_map,
    originalProductCarryI_field p hp]

theorem canSlots_endSym {R : Type*} [CommRing R] (p : ℕ) (u : Rˣ) (F : R[T;T⁻¹]) :
    endSym u (canSlots p F) = endSym u F -
      LaurentPolynomial.C (F.coeff (p : ℤ)) * endSym u (T (p : ℤ)) := by
  rw [canSlots, endSym_sub, endSym_sub, endSym_C, sub_zero, endSym_C_mul]

end WPFieldAssembly.SourceClosureSigmaProductCarry
