import WPFieldAssembly.ConicChart
import WPFieldAssembly.ConicCoefficients

open scoped Polynomial
open Polynomial WPFieldAssembly.ConicChart WPFieldAssembly.ConicCoefficients
  WPFieldAssembly.ConicDivision WPFieldAssembly.ActualConicProper
  WPFieldAssembly.NativeChiFieldSource WPFieldAssembly.NativeShiftedChi
  WPActualRankTwoLegendreField WPFiniteCubicLog

namespace WPFieldAssembly.ActualConicSource

set_option maxHeartbeats 1000000

noncomputable def forcingE (p : ℕ) : (ZMod p)[X] :=
  5 * X * conicA * B ^ (p - 1)

theorem B_derivative {K : Type*} [CommRing K] : (B : K[X]).derivative = 10 * X := by
  simp [B, derivative_pow_succ]
  ring

theorem actual_conic_coefficient_chain (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (c2Field p hp).comp B = B.derivative ^ 2 * conicA ^ 2 ∧
    (c1Field p hp).comp B =
      B.derivative.derivative * conicA ^ 2 + B.derivative * conicA * conicA.derivative := by
  rw [actual_c2_conic, actual_c1_conic, B_derivative]
  simp only [derivative_mul, derivative_ofNat, zero_mul, derivative_X, mul_one, zero_add]
  constructor
  · ring
  · trivial

theorem actual_forcingE_identities (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * B ^ 2 * conicA * (forcingE p).derivative =
      B ^ p * (B * (c1Field p hp).comp B - (c2Field p hp).comp B) ∧
    2 * B ^ 2 * conicA * forcingE p * B.derivative =
      B ^ p * B * (c2Field p hp).comp B := by
  have hm : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have hn : ((p - 1 : ℕ) : ZMod p) + 1 = (p : ZMod p) := by
      have he : p - 1 + 1 = p := by omega
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun j : ℕ => (j : ZMod p)) he
    have hz : (p : ZMod p) = 0 := by simp
    linear_combination hn + hz
  have hD : (B ^ (p - 1) : (ZMod p)[X]).derivative =
      -(B ^ (p - 2) * B.derivative) := by
    rw [derivative_pow, hm, show p - 1 - 1 = p - 2 by omega]
    simp
  have hpower1 : (B : (ZMod p)[X]) ^ (p - 1) * B = B ^ p := by
    rw [← pow_succ, show p - 1 + 1 = p by omega]
  have hpower2 : (B : (ZMod p)[X]) ^ (p - 2) * B ^ 2 = B ^ p := by
    rw [← pow_add, show p - 2 + 2 = p by omega]
  have hDE : (forcingE p).derivative =
      5 * (conicA + X * conicA.derivative) * B ^ (p - 1) -
        5 * X * conicA * B ^ (p - 2) * B.derivative := by
    simp only [forcingE, derivative_mul, derivative_ofNat, zero_mul,
      derivative_X, mul_one, zero_add, hD]
    ring
  rw [actual_c1_conic, actual_c2_conic, hDE, B_derivative]
  constructor
  · calc
      _ = 10 * conicA * (conicA + X * conicA.derivative) *
          (B ^ (p - 1) * B) * B -
        100 * X ^ 2 * conicA ^ 2 * (B ^ (p - 2) * B ^ 2) := by ring
      _ = _ := by rw [hpower1, hpower2]; ring
  · unfold forcingE
    calc
      _ = 100 * X ^ 2 * conicA ^ 2 * (B ^ (p - 1) * B) * B := by ring
      _ = _ := by rw [hpower1]; ring

theorem actual_half_chi_conic_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let y := (actualLegendreJacobi p).comp Tc
    let H := (shiftedChiField p hp).comp B
    conicC conicA ((c0Field p hp).comp B) (y ^ 2) H +
      conicA * ((forcingE p).derivative * y ^ 4 +
        forcingE p * y ^ 2 * (y ^ 2).derivative) = 0 := by
  let f := halfPullbackField p hp
  let H := (shiftedChiField p hp).comp B
  let F := f.comp B
  let y := (actualLegendreJacobi p).comp Tc
  have hc := congrArg (fun P : (ZMod p)[X] => P.comp B)
    (actual_half_chi_polynomial_source p hp)
  simp only [add_comp, mul_comp, sub_comp, pow_comp, X_comp, ofNat_comp, zero_comp] at hc
  have hchain := actual_conic_coefficient_chain p hp
  rw [polynomial_conic_transport _ _ _ _ _ _ _ hchain.1 hchain.2] at hc
  have hE := actual_forcingE_identities p hp
  have hz : 2 * B ^ 2 *
      (conicC conicA ((c0Field p hp).comp B) F H +
        conicA * ((forcingE p).derivative * F ^ 2 + forcingE p * F * F.derivative)) = 0 := by
    dsimp only [F, H]
    rw [derivative_comp]
    linear_combination hc + (f.comp B) ^ 2 * hE.1 +
      f.comp B * f.derivative.comp B * hE.2
  have h2 : (2 : (ZMod p)[X]) ≠ 0 := by
    change C (2 : ZMod p) ≠ 0
    exact C_ne_zero.mpr (WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega))
  have hB : (B : (ZMod p)[X]) ≠ 0 := by
    intro h
    have hh := congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
    simp [B] at hh
  have hcancel := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 (pow_ne_zero 2 hB))
  have hF : F = y ^ 2 := by
    dsimp only [F, f]
    rw [halfPullbackField_eq]
    exact actual_full_native_conic_square p hp
  change conicC conicA ((c0Field p hp).comp B) (y ^ 2) H +
    conicA * ((forcingE p).derivative * y ^ 4 +
      forcingE p * y ^ 2 * (y ^ 2).derivative) = 0
  rw [hF] at hcancel
  have hsquare : (y ^ 2) ^ 2 = y ^ 4 := by ring
  rw [hsquare] at hcancel
  exact hcancel

end WPFieldAssembly.ActualConicSource
