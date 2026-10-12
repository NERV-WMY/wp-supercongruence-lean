import WPActualNativeCubicJet

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeJetODE WPActualNativeFirstIntegral
  WPActualCMGauss WPActualCubicGauge WPActualCubicCarrier WPActualCubicHasse
  WPActualNativeCubicJet

namespace WPActualNativeCubicTransport

noncomputable def cubicD {K : Type*} [CommRing K] : K[X] := 1 - 20 * X - 8 * X ^ 2

theorem cubic_discriminant {K : Type*} [CommRing K] :
    (cubicH : K[X]) ^ 3 - cubicA = cubicD ^ 2 := by
  unfold cubicH cubicA cubicD
  ring

theorem cubic_log_derivative {K : Type*} [CommRing K] :
    (X * (1 - X) : K[X]) * cubicB = cubicA * cubicD := by
  unfold cubicA cubicB cubicD
  ring

/-- The native first integral after the actual cubic substitution, with all denominators cleared. -/
theorem native_cubic_first_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let N := (p - 1) / 2
    let E := algebraMap (ZMod p)[X] (RatFunc (ZMod p))
    let H := E cubicH
    let A := E cubicA
    let D := E cubicD
    let q := A / H ^ 3
    let F := (nativeField p (p / 6)).eval₂ RatFunc.C q
    let F1 := (nativeField p (p / 6)).derivative.eval₂ RatFunc.C q
    let J := (nativeJetField p).eval₂ RatFunc.C q
    let J1 := (nativeJetField p).derivative.eval₂ RatFunc.C q
    A * H ^ (3 * N) * (F * J1 - F1 * J) =
      H ^ 3 * F * (D ^ (2 * N) - H ^ (3 * N) * F) := by
  dsimp only
  let E := algebraMap (ZMod p)[X] (RatFunc (ZMod p))
  let H := E cubicH
  let A := E cubicA
  let D := E cubicD
  let q := A / H ^ 3
  let N := (p - 1) / 2
  have hH : H ≠ 0 := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := ZMod p))
  have hd : H ^ 3 - A = D ^ 2 := by
    simpa only [E, H, A, D, map_sub, map_pow] using congrArg E (cubic_discriminant (K := ZMod p))
  have hq : 1 - q = D ^ 2 / H ^ 3 := by
    dsimp [q]
    field_simp [hH]
    linear_combination hd
  have hpow : (1 - q) ^ N = D ^ (2 * N) / H ^ (3 * N) := by
    rw [hq, div_pow, ← pow_mul, ← pow_mul]
  have he := congrArg (fun P : (ZMod p)[X] => P.eval₂ RatFunc.C q)
    (actual_native_first_integral p hp)
  simp only [eval₂_mul, eval₂_sub, eval₂_X, eval₂_pow, eval₂_one] at he
  rw [hpow] at he
  dsimp only [q] at he
  field_simp [hH] at he
  change A * H ^ (3 * N) * _ = H ^ 3 * _ * (D ^ (2 * N) - H ^ (3 * N) * _) 
  linear_combination he

/-- Pure cleared algebra: the complete native and homogeneous derivative sources imply transport. -/
theorem cleared_ratio_transport {K : Type*} [Field K]
    (H A B D R t u F F1 J J1 Y Y1 W W1 : K)
    (hH : H ≠ 0) (hY : Y ≠ 0)
    (hlog : R * B = A * D) (hF : Y ^ 2 = t * F) (hJ : W = t ^ 3 * H * J)
    (hWD : H ^ 4 * W1 + 4 * H ^ 3 * W = H * B * t ^ 3 * J1)
    (hYD : 2 * H ^ 4 * Y * Y1 + 4 * H ^ 3 * Y ^ 2 = B * t * F1)
    (hNative : A * t ^ 3 * (F * J1 - F1 * J) = H ^ 3 * F * (u ^ 2 - t ^ 3 * F)) :
    R * (W1 * Y - 2 * W * Y1) = D * u ^ 2 * Y - D * t ^ 2 * Y ^ 3 := by
  have he : H ^ 4 * Y * (R * (W1 * Y - 2 * W * Y1)) =
      H ^ 4 * Y * (D * u ^ 2 * Y - D * t ^ 2 * Y ^ 3) := by
    calc
      _ = R * Y ^ 2 * (H ^ 4 * W1 + 4 * H ^ 3 * W) -
          R * W * (2 * H ^ 4 * Y * Y1 + 4 * H ^ 3 * Y ^ 2) := by ring
      _ = R * B * H * t ^ 4 * (F * J1 - F1 * J) := by rw [hWD, hYD, hF, hJ]; ring
      _ = D * H * t * (A * t ^ 3 * (F * J1 - F1 * J)) := by rw [hlog]; ring
      _ = D * H * t * (H ^ 3 * F * (u ^ 2 - t ^ 3 * F)) := by rw [hNative]
      _ = H ^ 4 * Y * (D * u ^ 2 * Y - D * t ^ 2 * Y ^ 3) := by
        have hF2 := congrArg (fun v : K => v ^ 2) hF
        linear_combination -D * H ^ 4 * u ^ 2 * hF + D * H ^ 4 * t ^ 2 * hF2
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hH) hY) he

/-- The actual complete numerator obeys the original cubic ratio source, with no value premise. -/
theorem actual_native_cubic_transport (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    X * (1 - X) * ((nativeRatioNumerator p).derivative * actualGauss p -
        2 * nativeRatioNumerator p * (actualGauss p).derivative) =
      cubicD ^ p * actualGauss p - cubicD * cubicH ^ (p - 1) * actualGauss p ^ 3 := by
  let N := (p - 1) / 2
  let E := algebraMap (ZMod p)[X] (RatFunc (ZMod p))
  let H := E cubicH
  let A := E cubicA
  let B := E cubicB
  let D := E cubicD
  let R := E (X * (1 - X))
  let q := A / H ^ 3
  let t := H ^ N
  let u := D ^ N
  let F := (nativeField p (p / 6)).eval₂ RatFunc.C q
  let F1 := (nativeField p (p / 6)).derivative.eval₂ RatFunc.C q
  let J := (nativeJetField p).eval₂ RatFunc.C q
  let J1 := (nativeJetField p).derivative.eval₂ RatFunc.C q
  let Y := E (actualGauss p)
  let Y1 := E (actualGauss p).derivative
  let W := E (nativeRatioNumerator p)
  let W1 := E (nativeRatioNumerator p).derivative
  have hH : H ≠ 0 := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := ZMod p))
  have hY : Y ≠ 0 := by
    apply RatFunc.algebraMap_ne_zero
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
    simp [actualGauss_origin] at he
  have hpow (m : ℕ) : H ^ (m * N) = t ^ m := by dsimp [t]; rw [Nat.mul_comm m N, pow_mul]
  have hlog : R * B = A * D := by
    simpa only [E, R, B, A, D, map_mul] using congrArg E (cubic_log_derivative (K := ZMod p))
  have hF : Y ^ 2 = t * F := by
    simpa only [E, Y, t, H, N, F, q, A, map_pow] using
      (actual_cubic_rational_hasse p hp).symm
  have hJ : W = t ^ 3 * H * J := by
    have he := nativeRatioNumerator_rational p
    change W = H ^ (3 * N + 1) * J at he
    rw [pow_succ, hpow 3] at he
    exact he
  have hWD : H ^ 4 * W1 + 4 * H ^ 3 * W = H * B * t ^ 3 * J1 := by
    have he := congrArg E (nativeRatioNumerator_gauge p (by omega))
    simp only [map_add, map_mul, map_pow, map_ofNat] at he
    rw [cubicLift_rational_eval N (3 * N) (nativeJetField p).derivative
      (derivative_degree_bound _ N (nativeJetField_degree p)) (by omega)] at he
    change H ^ 4 * W1 + 4 * H ^ 3 * W = H * B * (H ^ (3 * N) * J1) at he
    rw [hpow 3] at he
    linear_combination he
  have hYD : 2 * H ^ 4 * Y * Y1 + 4 * H ^ 3 * Y ^ 2 = B * t * F1 := by
    have he := cubicLift_actual_gauge p (by omega) (nativeField p (p / 6))
      (actual_native_field_degree p)
    change cubicH ^ 4 * (actualNativeCarrier p).derivative +
      4 * cubicH ^ 3 * actualNativeCarrier p = _ at he
    rw [actual_cubic_hasse p hp, derivative_sq, C_ofNat] at he
    have hm := congrArg E he
    simp only [map_add, map_mul, map_pow, map_ofNat] at hm
    rw [cubicLift_rational_eval (p / 6) N (nativeField p (p / 6)).derivative
      (derivative_degree_bound _ (p / 6) (actual_native_field_degree p))
      (by rcases WPActualNativeParameter.prime_six_classes p (by omega) with h | h <;> dsimp [N] <;> omega)] at hm
    change H ^ 4 * (2 * Y * Y1) + 4 * H ^ 3 * Y ^ 2 = B * (t * F1) at hm
    linear_combination hm
  have hNative : A * t ^ 3 * (F * J1 - F1 * J) = H ^ 3 * F * (u ^ 2 - t ^ 3 * F) := by
    have he := native_cubic_first_integral p hp
    change A * H ^ (3 * N) * (F * J1 - F1 * J) =
      H ^ 3 * F * (D ^ (2 * N) - H ^ (3 * N) * F) at he
    have hu : D ^ (2 * N) = u ^ 2 := by dsimp [u]; rw [Nat.mul_comm 2 N, pow_mul]
    simpa only [hpow 3, hu] using he
  have hs := cleared_ratio_transport H A B D R t u F F1 J J1 Y Y1 W W1
    hH hY hlog hF hJ hWD hYD hNative
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hDp : D * u ^ 2 = D ^ p := by
    dsimp [u]
    rw [← pow_mul, ← pow_succ']
    congr 1
    dsimp [N]
    omega
  have hHp : t ^ 2 = H ^ (p - 1) := by
    dsimp [t]
    rw [← pow_mul]
    congr 1
    dsimp [N]
    omega
  rw [hDp, hHp] at hs
  apply RatFunc.algebraMap_injective (ZMod p)
  simpa only [E, R, W1, Y, W, Y1, D, H, map_sub, map_mul, map_pow, map_ofNat] using hs

end WPActualNativeCubicTransport
