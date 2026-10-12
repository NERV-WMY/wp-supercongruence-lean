import WPFieldAssembly.ActualSigmaNormCarrySource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPActualRankTwoHatLift WPFieldAssembly.ActualSigmaNormCarrySource

namespace WPFieldAssembly.SourceClosureSigmaKCarry

set_option maxHeartbeats 1400000

noncomputable def originalKbarQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ ((p - 1) / 2))) * normPhase p

noncomputable def originalKcarryI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  -LaurentPolynomial.C
      (smallIntegralInverse p 2 * (smallIntegralInverse p 5) ^ ((p - 1) / 2)) *
    normCarryI p

noncomputable def originalK0Field (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (2 * (5 : ZMod p) ^ ((p - 1) / 2))) * normPhase p

noncomputable def originalK1Field (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C
      (2 * ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))) * originalK0Field p +
    LaurentPolynomial.C
      (15 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) /
        (5 : ZMod p) ^ ((p - 1) / 2)) +
    LaurentPolynomial.C (2 / (5 : ZMod p) ^ ((p - 1) / 2)) * normEntropyField p

/-- The exact K digit is obtained from the already checked full norm carrier. -/
theorem originalKcarryI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (originalKcarryI p) =
      LaurentPolynomial.C (1 / (p : ℚ)) *
        (LaurentPolynomial.C (1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2)))) *
          T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p -
          originalKbarQ p) := by
  have hN : ((p - 1) / 2) + 2 * (p - 1) = 5 * ((p - 1) / 2) := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have hscalar : (1 / (2 : ℚ)) * (1 / 5 : ℚ) ^ ((p - 1) / 2) *
      (1 / 5 : ℚ) ^ (2 * (p - 1)) =
        1 / (2 * (5 : ℚ) ^ (5 * ((p - 1) / 2))) := by
    rw [mul_assoc, ← pow_add, hN]
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  have hscale : (1 / (2 : ℚ)) * (1 / 5 : ℚ) ^ ((p - 1) / 2) =
      1 / (2 * (5 : ℚ) ^ ((p - 1) / 2)) := by
    simp only [one_div, inv_pow, mul_inv_rev]
    ring
  rw [hscale] at hscalar
  have hC := congrArg (fun c : ℚ => (LaurentPolynomial.C c : ℚ[T;T⁻¹])) hscalar
  simp only [_root_.map_mul] at hC
  have h2v : (integralRationals p).subtype (smallIntegralInverse p 2) = (1 / 2 : ℚ) :=
    smallIntegralInverse_value p 2 (by omega) (by omega)
  have h5v : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  rw [originalKcarryI, _root_.map_mul, _root_.map_neg, coefficientMap_C,
    _root_.map_mul, _root_.map_pow, h2v, h5v,
    normCarryI_value p hp, originalKbarQ]
  rw [hscale]
  dsimp only [normPhase]
  linear_combination
    LaurentPolynomial.C (1 / (p : ℚ)) * T (-(p : ℤ)) *
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p * hC

/-- UW16h's complete K1, including its original phase and entropy constants. -/
theorem originalKcarryI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalKcarryI p) = originalK1Field p := by
  rw [originalKcarryI, _root_.map_mul, _root_.map_neg, coefficientMap_C,
    _root_.map_mul, _root_.map_pow,
    smallIntegralInverse_field p 2 (by omega) (by omega),
    smallIntegralInverse_field p 5 (by omega) (by omega), normCarryI_field p hp,
    originalK1Field, originalK0Field]
  simp only [normPhase, _root_.map_add, _root_.map_sub, _root_.map_mul,
    _root_.map_ofNat, _root_.map_neg, _root_.map_one, Nat.cast_ofNat,
    div_eq_mul_inv, inv_pow, mul_inv_rev]
  have h2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
  have hC2 := congrArg (fun c : ZMod p => (LaurentPolynomial.C c : (ZMod p)[T;T⁻¹])) h2
  simp only [_root_.map_mul, _root_.map_ofNat, _root_.map_one] at hC2
  linear_combination
    (2 * normEntropyField p +
      15 * LaurentPolynomial.C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)) *
      LaurentPolynomial.C (((5 : ZMod p) ^ ((p - 1) / 2))⁻¹) * hC2

end WPFieldAssembly.SourceClosureSigmaKCarry
