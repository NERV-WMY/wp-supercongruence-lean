import WPFieldAssembly.NativeTerminal
import WPFieldAssembly.NativeShiftedChi
import WPFieldAssembly.ConicKernel

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualPullbackSource
  WPFieldAssembly.NativePrecision WPFieldAssembly.NativeTerminal
  WPFieldAssembly.NativeShiftedChi WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.NativeConicTerminal

set_option maxHeartbeats 1000000

theorem shiftedChiQ_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    (shiftedChiQ p).coeff (p + 3 * N) =
      (WPReview.nativeCoefficient N / (p : ℚ)) * (-16 / 125 : ℚ) ^ N := by
  dsimp only
  let N := (p - 1) / 2
  have hVdeg : Vpolynomial.natDegree = 3 := by
    unfold Vpolynomial
    compute_degree <;> norm_num
  have hVtop : Vpolynomial.coeff 3 = -16 / 125 := by
    have he : Vpolynomial = C (-16 / 125 : ℚ) * X ^ 3 +
        C (72 / 125 : ℚ) * X ^ 2 - C (33 / 125 : ℚ) * X + C (4 / 125 : ℚ) := by
      apply Polynomial.funext
      intro x
      simp [Vpolynomial]
      ring
    rw [he]
    simp
  have hPtop : (nativeHalfPullback p).coeff (3 * N) =
      WPReview.nativeCoefficient N * (-16 / 125 : ℚ) ^ N := by
    have he := coeff_comp_bound_top
      (WPReview.nativePolynomial (N + 1)) Vpolynomial N 3
      (by rw [rational_native_degree]) hVdeg (by omega)
    rw [WPReview.nativePolynomial_coeff, if_pos (by omega), hVtop] at he
    simpa only [nativeHalfPullback, N, Nat.mul_comm] using he
  have href : ((nativeHalfPullback p).reflect (3 * N)).natDegree ≤ 3 * N :=
    natDegree_reflect_le.trans (max_le (le_refl _) (nativeHalfPullback_degree p))
  have hrefc : (X * (nativeHalfPullback p).reflect (3 * N)).coeff (p + 3 * N) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact (natDegree_mul_le_of_le (natDegree_X_le (R := ℚ)) href).trans_lt (by omega)
  have hfirst : (X ^ p * nativeHalfPullback p).coeff (p + 3 * N) =
      (nativeHalfPullback p).coeff (3 * N) := by
    rw [coeff_mul_add_eq_of_natDegree_le
      (show (X ^ p : ℚ[X]).natDegree ≤ p by simp) (nativeHalfPullback_degree p)]
    simp [N]
  rw [shiftedChiQ, coeff_C_mul, coeff_sub, hfirst, hrefc, sub_zero, hPtop]
  dsimp only [N]
  ring

theorem shiftedChiQ_conic_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    ((shiftedChiQ p).comp (5 * X ^ 2 - 1)).coeff ((p + 3 * N) * 2) =
      (WPReview.nativeCoefficient N / (p : ℚ)) * (5 : ℚ) ^ p * (-16 : ℚ) ^ N := by
  dsimp only
  let N := (p - 1) / 2
  have hBdeg : (5 * X ^ 2 - 1 : ℚ[X]).natDegree = 2 := by
    compute_degree
    norm_num
  have hBtop : (5 * X ^ 2 - 1 : ℚ[X]).coeff 2 = 5 := by
    change (5 * X ^ 2 - C (1 : ℚ) : ℚ[X]).coeff 2 = 5
    simp [Polynomial.coeff_one]
  rw [coeff_comp_bound_top (shiftedChiQ p) (5 * X ^ 2 - 1)
    (p + 3 * N) 2 (shiftedChiQ_degree p hp) hBdeg (by omega),
    hBtop, shiftedChiQ_top p hp]
  have hpowers : (-16 / 125 : ℚ) ^ N * (5 : ℚ) ^ (p + 3 * N) =
      (5 : ℚ) ^ p * (-16 : ℚ) ^ N := by
    rw [pow_add]
    have h125 : (5 : ℚ) ^ (3 * N) = (125 : ℚ) ^ N := by
      rw [pow_mul]
      norm_num
    rw [h125]
    calc
      _ = (5 : ℚ) ^ p * ((-16 / 125 : ℚ) ^ N * (125 : ℚ) ^ N) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [mul_assoc, hpowers]
  dsimp only [N]
  ring

/-- The terminal reduction passes through the actual integral polynomial model. -/
theorem actual_conic_H_terminal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((shiftedChiField p hp).comp (5 * X ^ 2 - 1)).coeff (5 * p - 3) =
      -5 * (nativeSixEta p : ZMod p) / 2 := by
  let N := (p - 1) / 2
  let HI := (shiftedChiIntegral p hp).comp
    (5 * X ^ 2 - 1 : (integralRationals p)[X])
  have hQ : HI.map (integralRationals p).subtype =
      (shiftedChiQ p).comp (5 * X ^ 2 - 1) := by
    simp only [HI, Polynomial.map_comp, shiftedChiIntegral_rational,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  have hZ : HI.map (residueHom p) =
      (shiftedChiField p hp).comp (5 * X ^ 2 - 1) := by
    simp only [HI, Polynomial.map_comp, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
      Polynomial.map_X, Polynomial.map_one]
    rfl
  have hI : HI.coeff ((p + 3 * N) * 2) =
      nativeHalfDivPrime p hp * (5 : integralRationals p) ^ p *
        (-16 : integralRationals p) ^ N := by
    apply Subtype.ext
    change (integralRationals p).subtype (HI.coeff ((p + 3 * N) * 2)) = _
    have hc := congrArg (fun P : ℚ[X] => P.coeff ((p + 3 * N) * 2)) hQ
    rw [coeff_map] at hc
    rw [hc, shiftedChiQ_conic_top p hp]
    rfl
  have hF := congrArg (residueHom p) hI
  simp only [map_mul, map_pow, map_ofNat, map_neg,
    actual_native_half_div_prime_residue] at hF
  have hcoef := congrArg
    (fun P : (ZMod p)[X] => P.coeff ((p + 3 * N) * 2)) hZ
  rw [coeff_map] at hcoef
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hindex : 5 * p - 3 = (p + 3 * N) * 2 := by dsimp [N]; omega
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h16 : (-16 : ZMod p) ^ N = (-1 : ZMod p) ^ N := by
    have hnum : (-16 : ZMod p) = -1 * 4 ^ 2 := by ring
    rw [hnum, mul_pow, ← pow_mul,
      show 2 * N = p - 1 by dsimp [N]; omega,
      ZMod.pow_card_sub_one_eq_one h4, mul_one]
  have hs : ((-1 : ZMod p) ^ N) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hindex, ← hcoef, hF, ZMod.pow_card, h16]
  change -(nativeSixEta p : ZMod p) * (-1 : ZMod p) ^ N / 2 *
    5 * (-1 : ZMod p) ^ N = _
  field_simp [h2]
  linear_combination -5 * (nativeSixEta p : ZMod p) * hs

end WPFieldAssembly.NativeConicTerminal
