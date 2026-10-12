import WPActualCMGaussSquare
import WPActualGaussProper
import WPActualRankTwoLegendreField

open scoped Polynomial
open Polynomial WPActualNativeHasse WPHasseCubicSource WPActualCMGauss
  WPActualRankTwoLegendreField

namespace WPActualNativeQuadraticSquare

noncomputable def quadraticGaussRegular {K : Type*} [CommRing K] (Y : K[X]) : K[X] :=
  36 * X * (1 - X) * Y.derivative.derivative +
    36 * (1 - 2 * X) * Y.derivative - 5 * Y

noncomputable def quadraticSquareRegular {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  36 * X ^ 2 * (1 - X) ^ 2 * P.derivative.derivative.derivative +
    108 * X * (1 - X) * (1 - 2 * X) * P.derivative.derivative +
    (36 - 236 * X + 236 * X ^ 2) * P.derivative - 10 * (1 - 2 * X) * P

theorem quadraticSquare_source {K : Type*} [CommRing K] (Y : K[X]) :
    quadraticSquareRegular (Y ^ 2) =
      2 * X * (1 - X) * Y * (quadraticGaussRegular Y).derivative +
        (6 * X * (1 - X) * Y.derivative + 2 * (1 - 2 * X) * Y) *
          quadraticGaussRegular Y := by
  simp [quadraticSquareRegular, quadraticGaussRegular, derivative_mul, derivative_pow_succ]
  ring

theorem actual_quadratic_Gauss_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    quadraticGaussRegular (actualLegendreGauss p) = 0 := by
  have he : legendreRegular (p / 6) (actualLegendreGauss p) = 0 := by
    rw [actualLegendreGauss, ← legendreRegular_map, actual_integer_legendre_ODE,
      Polynomial.map_zero]
  have hc : (36 : (ZMod p)[X]) *
      C (((p / 6 : ℕ) : ZMod p) * (((p / 6 : ℕ) : ZMod p) + 1)) = -5 := by
    simpa only [map_mul, map_ofNat, map_neg, Nat.cast_add, Nat.cast_one, mul_assoc] using
      congrArg Polynomial.C (rankField_eigenvalue p hp)
  calc
    _ = 36 * legendreRegular (p / 6) (actualLegendreGauss p) -
        (36 * C (((p / 6 : ℕ) : ZMod p) * (((p / 6 : ℕ) : ZMod p) + 1)) + 5) *
          actualLegendreGauss p := by
      unfold quadraticGaussRegular legendreRegular
      ring
    _ = 0 := by rw [he, hc]; ring

theorem actual_quadratic_square_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    quadraticSquareRegular (actualLegendreGauss p ^ 2) = 0 := by
  rw [quadraticSquare_source, actual_quadratic_Gauss_ODE p hp, derivative_zero]
  ring

theorem actual_quadratic_Gauss_origin (p : ℕ) [Fact p.Prime] :
    (actualLegendreGauss p).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero]
  simp [actualLegendreGauss, coeff_shiftedLegendre]

/-- The whole native ODE under its original quadratic argument. -/
theorem native_quadratic_ODE_source {K : Type*} [CommRing K] (F : K[X]) :
    quadraticSquareRegular (F.comp (4 * X * (1 - X))) =
      2 * (1 - 2 * X) * (regularNative F).comp (4 * X * (1 - X)) := by
  simp [quadraticSquareRegular, regularNative, derivative_comp, derivative_mul,
    derivative_add, derivative_sub, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp]
  ring

noncomputable def quadraticE3 {K : Type*} [CommRing K] : K[X] := 36 * (1 - X) ^ 2
noncomputable def quadraticE2 {K : Type*} [CommRing K] : K[X] := -108 * X * (1 - X)
noncomputable def quadraticE1 {K : Type*} [CommRing K] : K[X] := -56 * X + 92 * X ^ 2
noncomputable def quadraticE0 {K : Type*} [CommRing K] : K[X] := -10 * X + 20 * X ^ 2

theorem quadraticSquare_euler {K : Type*} [CommRing K] (P : K[X]) :
    regularEuler quadraticE3 quadraticE2 quadraticE1 quadraticE0 P =
      X * quadraticSquareRegular P := by
  simp [regularEuler, quadraticE3, quadraticE2, quadraticE1, quadraticE0,
    quadraticSquareRegular, theta, derivative_mul]
  ring

theorem quadraticSquare_sub {K : Type*} [CommRing K] (P Q : K[X]) :
    quadraticSquareRegular (P - Q) = quadraticSquareRegular P - quadraticSquareRegular Q := by
  simp only [quadraticSquareRegular, derivative_sub]
  ring

theorem actual_quadratic_square_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualLegendreGauss p ^ 2).natDegree < p := by
  have hd : (actualLegendreGauss p).natDegree ≤ p / 6 := by
    unfold actualLegendreGauss
    exact natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])
  have he := natDegree_mul_le_of_le hd hd
  rw [← pow_two] at he
  omega

theorem actual_quadratic_square_unique (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p) (horigin : P.eval 0 = 1)
    (hsource : quadraticSquareRegular P = 0) : P = actualLegendreGauss p ^ 2 := by
  have h36 : (36 : ZMod p) ≠ 0 := by
    have h2 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    have h3 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
    convert mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h3) using 1; norm_num
  have hcoeff : (quadraticE3 : (ZMod p)[X]).coeff 0 = 36 ∧
      (quadraticE2 : (ZMod p)[X]).coeff 0 = 0 ∧
      (quadraticE1 : (ZMod p)[X]).coeff 0 = 0 ∧
      (quadraticE0 : (ZMod p)[X]).coeff 0 = 0 := by
    simp [quadraticE3, quadraticE2, quadraticE1, quadraticE0, coeff_zero_eq_eval_zero]
  have hdeg : (P - actualLegendreGauss p ^ 2).natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hdegree (actual_quadratic_square_degree p hp))
  have hzero := finite_regularEuler_uniqueness p quadraticE3 quadraticE2 quadraticE1 quadraticE0
    (P - actualLegendreGauss p ^ 2) 36 h36 hcoeff.1 hcoeff.2.1 hcoeff.2.2.1
      hcoeff.2.2.2 hdeg (by simp [horigin, actual_quadratic_Gauss_origin]) (by
        rw [quadraticSquare_euler, quadraticSquare_sub, hsource, actual_quadratic_square_ODE p hp]
        ring)
  exact sub_eq_zero.mp hzero

theorem actual_native_quadratic_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeField p (p / 6)).comp (4 * X * (1 - X)) = actualLegendreGauss p ^ 2 := by
  apply actual_quadratic_square_unique p (by omega)
  · have hd : ((nativeField p (p / 6)).comp (4 * X * (1 - X))).natDegree ≤
        (nativeField p (p / 6)).natDegree *
          (4 * X * (1 - X) : (ZMod p)[X]).natDegree := natDegree_comp_le
    have hg : (4 * X * (1 - X) : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
    have he := hd.trans (Nat.mul_le_mul (actual_native_field_degree p) hg)
    omega
  · simp [eval_comp, actual_native_field_origin]
  · rw [native_quadratic_ODE_source, actual_native_field_regular_ODE p (by omega)]
    simp

/-- The actual original quadratic Clausen attachment in the native Jacobi variable. -/
theorem actual_native_Jacobi_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeField p (p / 6)).comp (1 - X ^ 2) = actualLegendreJacobi p ^ 2 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have he := congrArg (fun P : (ZMod p)[X] => P.comp (C (1 / 2) * (1 - X)))
    (actual_native_quadratic_square p hp)
  rw [comp_assoc, Polynomial.pow_comp, ← actualLegendreJacobi] at he
  have harg : (4 * X * (1 - X) : (ZMod p)[X]).comp (C (1 / 2) * (1 - X)) =
      1 - X ^ 2 := by
    simp only [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.one_comp, Polynomial.ofNat_comp]
    have hf : (2 : ZMod p) * (1 / 2) = 1 := by field_simp
    have hc := congrArg (Polynomial.C (R := ZMod p)) hf
    simp only [map_mul, C_ofNat, map_one] at hc
    linear_combination (2 * (1 - X) - (1 - X) ^ 2 *
      (2 * C (1 / 2 : ZMod p) + 1)) * hc
  rwa [harg] at he

end WPActualNativeQuadraticSquare
