import WPFieldAssembly.NativeChiFieldSource
import WPFieldAssembly.ActualConicProper

open scoped Polynomial
open Polynomial WPPIntegralReduction WPHasseCubicSource
  WPFieldAssembly.NativeChiFieldSource WPFieldAssembly.ActualConicProper

namespace WPFieldAssembly.ConicCoefficients

set_option maxHeartbeats 1000000

noncomputable def B {K : Type*} [CommRing K] : K[X] := 5 * X ^ 2 - 1

theorem rational_c2_conic :
    WPFieldAssembly.NativeChiCovariance.c2.comp B =
      100 * X ^ 2 * (conicA : ℚ[X]) ^ 2 := by
  apply Polynomial.funext
  intro x
  simp [WPFieldAssembly.NativeChiCovariance.c2, cubicDiscriminant, B, conicA]
  ring

theorem rational_c1_conic :
    WPFieldAssembly.NativeChiCovariance.c1.comp B =
      10 * (conicA : ℚ[X]) ^ 2 + 10 * X * conicA * conicA.derivative := by
  apply Polynomial.funext
  intro x
  simp [WPFieldAssembly.NativeChiCovariance.c1, cubicDiscriminant, B, conicA,
    derivative_mul, derivative_pow_succ]
  ring

theorem rational_c0_conic :
    WPFieldAssembly.NativeChiCovariance.c0.comp B =
      -5 * (1 - X ^ 2) * (4 * X ^ 2 - 1) ^ 2 := by
  apply Polynomial.funext
  intro x
  simp [WPFieldAssembly.NativeChiCovariance.c0, cubicNumerator, B]
  ring

theorem actual_c2_conic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c2Field p hp).comp B = 100 * X ^ 2 * (conicA : (ZMod p)[X]) ^ 2 := by
  have hi : (c2Integral p hp).comp B =
      100 * X ^ 2 * (conicA : (integralRationals p)[X]) ^ 2 := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [Polynomial.map_comp, c2Integral_mapQ]
    simp only [B, conicA, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one]
    exact rational_c2_conic
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simpa only [c2Field, B, conicA, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one] using hf

theorem actual_c1_conic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c1Field p hp).comp B =
      10 * (conicA : (ZMod p)[X]) ^ 2 + 10 * X * conicA * conicA.derivative := by
  have hi : (c1Integral p hp).comp B =
      10 * (conicA : (integralRationals p)[X]) ^ 2 + 10 * X * conicA * conicA.derivative := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [Polynomial.map_comp, c1Integral_mapQ]
    simp only [B, conicA, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one,
      ← derivative_map]
    exact rational_c1_conic
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simpa only [c1Field, B, conicA, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, ← derivative_map] using hf

theorem actual_c0_conic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c0Field p hp).comp B = -5 * (1 - X ^ 2) * (4 * X ^ 2 - 1) ^ 2 := by
  have hi : (c0Integral p hp).comp B =
      -5 * (1 - X ^ 2 : (integralRationals p)[X]) * (4 * X ^ 2 - 1) ^ 2 := by
    apply Polynomial.map_injective (integralRationals p).subtype
      (Subring.subtype_injective (integralRationals p))
    rw [Polynomial.map_comp, c0Integral_mapQ]
    simp only [B, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_neg]
    exact rational_c0_conic
  have hf := congrArg (Polynomial.map (residueHom p)) hi
  simpa only [c0Field, B, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, Polynomial.map_one, Polynomial.map_neg] using hf

end WPFieldAssembly.ConicCoefficients
