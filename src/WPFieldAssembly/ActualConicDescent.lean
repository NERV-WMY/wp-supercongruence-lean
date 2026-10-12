import WPFieldAssembly.ActualConicNormalization
import WPFiniteZSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteWSource
  WPFieldAssembly.NativeChiFieldSource WPFieldAssembly.NativeShiftedChi
  WPFieldAssembly.ConicCoefficients WPFieldAssembly.ActualConicProper
  WPFieldAssembly.ActualConicSource WPFieldAssembly.ActualConicNormalization
  WPFieldAssembly.ConicDivision WPFieldAssembly.ConicKernel
  WPActualRankTwoLegendreField WPFiniteCubicLog

namespace WPFieldAssembly.ActualConicDescent

set_option maxHeartbeats 1200000

theorem Abar_conic {K : Type*} [Field K] :
    (WPFiniteZSource.Abar : K[X]).comp B = 25 * conicA := by
  simp only [WPFiniteZSource.Abar, B, conicA, sub_comp, mul_comp, ofNat_comp, one_comp, X_comp]
  ring

theorem squaredCoordinate_conic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (squaredCoordinate : (ZMod p)[X]).comp B = X ^ 2 := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  simp only [squaredCoordinate, B, mul_comp, C_comp, add_comp, one_comp, X_comp]
  ext n
  have he : (Polynomial.C ((5 : ZMod p)⁻¹) * (5 * X ^ 2 - 1 + 1) : (ZMod p)[X]) = X ^ 2 := by
    rw [sub_add_cancel]
    change Polynomial.C ((5 : ZMod p)⁻¹) * (Polynomial.C (5 : ZMod p) * X ^ 2) = _
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h5, map_one, one_mul]
  exact congrArg (fun P : (ZMod p)[X] => P.coeff n) he

theorem actual_conic_Wronskian_cleared (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := halfPullbackField p hp
    let H := shiftedChiField p hp
    2 * ((f * H.derivative - f.derivative * H).comp B) =
      X ^ (p - 1) * conicA ^ (p - 1) * f.comp B -
        B ^ (p - 1) * (f.comp B) ^ 2 := by
  let y := (actualLegendreJacobi p).comp Tc
  let f := halfPullbackField p hp
  let H := shiftedChiField p hp
  have hF : f.comp B = y ^ 2 := by
    change (halfPullbackField p hp).comp B = y ^ 2
    rw [halfPullbackField_eq]
    exact actual_full_native_conic_square p hp
  have hn := actual_conic_firstNumerator_normalized p hp
  have hm := congrArg (fun P : (ZMod p)[X] => y * P) hn
  have hrew : y * firstNumerator conicA y (H.comp B) (forcingE p) =
      conicA * ((f.comp B) * (H.comp B).derivative -
        (f.comp B).derivative * (H.comp B)) + forcingE p * (f.comp B) ^ 2 := by
    rw [hF]
    simp only [firstNumerator, derivative_sq, C_ofNat]
    ring
  change y * firstNumerator conicA y (H.comp B) (forcingE p) =
    y * (y * (Polynomial.C (5 : ZMod p) * X ^ p * conicA ^ p)) at hm
  rw [hrew] at hm
  have hpowerX : (X : (ZMod p)[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, show p - 1 + 1 = p by omega]
  have hpowerA : (conicA : (ZMod p)[X]) ^ (p - 1) * conicA = conicA ^ p := by
    rw [← pow_succ, show p - 1 + 1 = p by omega]
  have hz : (5 * X * conicA : (ZMod p)[X]) *
      (2 * ((f * H.derivative - f.derivative * H).comp B) -
        (X ^ (p - 1) * conicA ^ (p - 1) * f.comp B -
          B ^ (p - 1) * (f.comp B) ^ 2)) = 0 := by
    simp only [mul_comp, sub_comp, derivative_comp, B_derivative] at hm ⊢
    have hr : (5 * X * conicA : (ZMod p)[X]) *
        (X ^ (p - 1) * conicA ^ (p - 1) * f.comp B) =
      y * (y * (Polynomial.C (5 : ZMod p) * X ^ p * conicA ^ p)) := by
      simp only [C_ofNat]
      rw [hF]
      calc
        _ = 5 * (X ^ (p - 1) * X) *
          (conicA ^ (p - 1) * conicA) * y ^ 2 := by ring
        _ = _ := by rw [hpowerX, hpowerA]; ring
    dsimp only [forcingE] at hm
    linear_combination hm - hr
  have h5 : (5 : (ZMod p)[X]) ≠ 0 := by
    change Polynomial.C (5 : ZMod p) ≠ 0
    exact C_ne_zero.mpr (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  have hA : (conicA : (ZMod p)[X]) ≠ 0 := by
    intro h
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) h
    simp [conicA] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (mul_ne_zero h5 X_ne_zero) hA))

theorem actual_half_chi_polynomial_Wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := halfPullbackField p hp
    let H := shiftedChiField p hp
    2 * (f * H.derivative - f.derivative * H) =
      WPFiniteZSource.Abar ^ (p - 1) * squaredCoordinate ^ ((p - 1) / 2) * f -
        X ^ (p - 1) * f ^ 2 := by
  let f := halfPullbackField p hp
  let H := shiftedChiField p hp
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h25 : (25 : ZMod p) ≠ 0 := by
    have he : (25 : ZMod p) = 5 ^ 2 := by norm_num
    rw [he]
    exact pow_ne_zero _ h5
  have hB : (B : (ZMod p)[X]).natDegree ≠ 0 := by
    have ht : (B : (ZMod p)[X]).coeff 2 = 5 := by simp [B, coeff_one]
    have hh : 2 ≤ (B : (ZMod p)[X]).natDegree :=
      le_natDegree_of_ne_zero (by rw [ht]; exact h5)
    omega
  apply comp_injective_nonconstant B hB
  simp only [mul_comp, sub_comp, pow_comp, ofNat_comp, X_comp]
  rw [Abar_conic, squaredCoordinate_conic p hp, mul_pow]
  have h25P : (25 : (ZMod p)[X]) ^ (p - 1) = 1 := by
    change Polynomial.C (25 : ZMod p) ^ (p - 1) = 1
    rw [← map_pow, ZMod.pow_card_sub_one_eq_one h25, map_one]
  rw [h25P, one_mul, ← pow_mul]
  have hh := half_exponent p hp
  rw [show 2 * ((p - 1) / 2) = p - 1 by omega]
  have hc := actual_conic_Wronskian_cleared p hp
  simp only [mul_comp, sub_comp] at hc
  convert hc using 1 <;> ring

theorem actual_half_chi_Laurent_Wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := (halfPullbackField p hp).toLaurent
    let χ := halfChiField p hp
    f * D χ - D f * χ =
      f * WPFiniteZSource.R p - LaurentPolynomial.C (1 / 2 : ZMod p) * T (-1) * f ^ 2 := by
  let f := (halfPullbackField p hp).toLaurent
  let χ := halfChiField p hp
  have he := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (actual_half_chi_polynomial_Wronskian p hp)
  simp only [map_mul, map_sub, map_pow, map_ofNat, Polynomial.toLaurent_X,
    T_pow, mul_one, ← D_toLaurent, shiftedChiField_toLaurent,
    D_frobenius_shift p _ (p : ℤ) (dvd_refl _)] at he
  change 2 * (f * (T (p : ℤ) * D χ) - D f * (T (p : ℤ) * χ)) =
    WPFiniteZSource.Abar.toLaurent ^ (p - 1) *
      squaredCoordinate.toLaurent ^ ((p - 1) / 2) * f -
      T ((p - 1 : ℕ) : ℤ) * f ^ 2 at he
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : (ZMod p)[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have htm : (T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ) : (ZMod p)[T;T⁻¹]) = T (-1) := by
    rw [← T_add]
    congr 1
    omega
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (1 / 2 : ZMod p) = 1 := by
    rw [show (2 : (ZMod p)[T;T⁻¹]) = LaurentPolynomial.C (2 : ZMod p) by rfl,
      ← map_mul]
    norm_num [h2]
  have hc : 2 * (f * D χ - D f * χ -
      (f * WPFiniteZSource.R p - LaurentPolynomial.C (1 / 2 : ZMod p) * T (-1) * f ^ 2)) = 0 := by
    dsimp only [WPFiniteZSource.R]
    linear_combination T (-(p : ℤ)) * he -
      2 * (f * D χ - D f * χ) * ht -
      f ^ 2 * htm -
      (f * T (-(p : ℤ)) * WPFiniteZSource.Abar.toLaurent ^ (p - 1) *
        squaredCoordinate.toLaurent ^ ((p - 1) / 2) - T (-1) * f ^ 2) * hhalf
  have h2L : (2 : (ZMod p)[T;T⁻¹]) ≠ 0 := by
    change LaurentPolynomial.C (2 : ZMod p) ≠ 0
    intro hz
    apply h2
    have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff 0) hz
    simpa using he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left h2L)

end WPFieldAssembly.ActualConicDescent
