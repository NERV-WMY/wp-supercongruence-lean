import WPFieldAssembly.NativeChiFieldSource
import WPFieldAssembly.ConicDivision

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteJCarrier
  WPPIntegralReduction WPFieldAssembly.NativeChiFieldSource
  WPFieldAssembly.NativeShiftedChi WPFieldAssembly.ConicDivision

namespace WPFieldAssembly.ConicChart

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

noncomputable def polynomialConcomitant {K : Type*} [CommRing K]
    (a2 a1 a0 f g : K[X]) : K[X] :=
  a2 * (f * g.derivative.derivative + g * f.derivative.derivative -
      f.derivative * g.derivative) +
    a1 * (f * g.derivative + g * f.derivative) + a0 * f * g

theorem concomitant_toLaurent {K : Type*} [Field K]
    (a2 a1 a0 f g : K[X]) :
    (polynomialConcomitant a2 a1 a0 f g).toLaurent =
      laurentConcomitant a2.toLaurent a1.toLaurent a0.toLaurent f.toLaurent g.toLaurent := by
  simp only [polynomialConcomitant, laurentConcomitant, map_add, map_sub, map_mul,
    D_toLaurent]

theorem frobenius_shift_concomitant {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a2 a1 a0 f χ : K[T;T⁻¹]) :
    laurentConcomitant a2 a1 a0 f (T (p : ℤ) * χ) =
      T (p : ℤ) * laurentConcomitant a2 a1 a0 f χ := by
  simp only [laurentConcomitant,
    D_frobenius_shift p _ (p : ℤ) (dvd_refl _)]
  ring

theorem unit_half_clearing {R : Type*} [CommRing R]
    (x u t k a2 a1 f g h : R) (hx : x * u = 1) (hh : 2 * h = 1)
    (hs : k + h * (u * a1 - u ^ 2 * a2) * f ^ 2 + h * u * a2 * f * g = 0) :
    2 * x ^ 2 * t * k + t * ((x * a1 - a2) * f ^ 2 + x * a2 * f * g) = 0 := by
  have hc : 2 * x ^ 2 *
      (h * (u * a1 - u ^ 2 * a2) * f ^ 2 + h * u * a2 * f * g) =
      (x * a1 - a2) * f ^ 2 + x * a2 * f * g := by
    calc
      _ = x ^ 2 * (2 * h) *
        ((u * a1 - u ^ 2 * a2) * f ^ 2 + u * a2 * f * g) := by ring
      _ = x ^ 2 * ((u * a1 - u ^ 2 * a2) * f ^ 2 + u * a2 * f * g) := by
        rw [hh, mul_one]
      _ = _ := by
        linear_combination (x * (a1 * f ^ 2 + a2 * f * g) -
          a2 * f ^ 2 * (x * u + 1)) * hx
  linear_combination 2 * x ^ 2 * t * hs - t * hc

/-- Denominators are cleared after the actual integral source is reduced. -/
theorem actual_half_chi_polynomial_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := halfPullbackField p hp
    let H := shiftedChiField p hp
    2 * X ^ 2 * polynomialConcomitant (c2Field p hp) (c1Field p hp)
        (c0Field p hp) f H +
      X ^ p * ((X * c1Field p hp - c2Field p hp) * f ^ 2 +
        X * c2Field p hp * f * f.derivative) = 0 := by
  let f := halfPullbackField p hp
  let χ := halfChiField p hp
  have hs := actual_half_chi_field_laurent_source p hp
  have hx : (T 1 : (ZMod p)[T;T⁻¹]) * T (-1) = 1 := by
    rw [← T_add]
    norm_num
  have hh : (2 : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (halfField p hp) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (LaurentPolynomial.C : ZMod p → (ZMod p)[T;T⁻¹]) (two_mul_halfField p hp)
  have hc := unit_half_clearing (T 1) (T (-1)) (T (p : ℤ))
    (laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
      (c0Field p hp).toLaurent f.toLaurent χ)
    (c2Field p hp).toLaurent (c1Field p hp).toLaurent f.toLaurent
      (D f.toLaurent) (LaurentPolynomial.C (halfField p hp)) hx hh hs
  simp only [LaurentPolynomial.T_pow, mul_one] at hc
  have hshift : laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
      (c0Field p hp).toLaurent f.toLaurent (shiftedChiField p hp).toLaurent =
      T (p : ℤ) * laurentConcomitant (c2Field p hp).toLaurent (c1Field p hp).toLaurent
        (c0Field p hp).toLaurent f.toLaurent χ := by
    rw [shiftedChiField_toLaurent]
    exact frobenius_shift_concomitant p _ _ _ _ _
  have hzero : (2 * X ^ 2 * polynomialConcomitant (c2Field p hp) (c1Field p hp)
      (c0Field p hp) f (shiftedChiField p hp) +
      X ^ p * ((X * c1Field p hp - c2Field p hp) * f ^ 2 +
        X * c2Field p hp * f * f.derivative)).toLaurent = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one,
      concomitant_toLaurent, ← D_toLaurent, hshift]
    linear_combination hc
  dsimp only
  ext n
  have hn := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (n : ℤ)) hzero
  rw [toLaurent_coeff_nat] at hn
  change _ = 0 at hn
  exact hn

theorem polynomial_conic_transport {K : Type*} [CommRing K]
    (a2 a1 a0 A B f g : K[X])
    (h2 : a2.comp B = B.derivative ^ 2 * A ^ 2)
    (h1 : a1.comp B = B.derivative.derivative * A ^ 2 + B.derivative * A * A.derivative) :
    (polynomialConcomitant a2 a1 a0 f g).comp B =
      conicC A (a0.comp B) (f.comp B) (g.comp B) := by
  simp only [polynomialConcomitant, conicC, add_comp, sub_comp, mul_comp,
    derivative_comp, derivative_mul]
  rw [h2, h1]
  ring

end WPFieldAssembly.ConicChart
