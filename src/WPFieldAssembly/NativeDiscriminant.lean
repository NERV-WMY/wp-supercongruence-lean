import WPFieldAssembly.TerminatingSquare

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeFirstIntegral WPHasseCubicSource
  WPActualNativeChiTaylor WPFieldAssembly.TerminatingSquare

namespace WPFieldAssembly.NativeDiscriminant

set_option maxHeartbeats 800000

/-- The zero-parameter native operator retains the canonical rational normalization. -/
theorem clearedOperator_rational (F : ℚ[X]) :
    clearedOperator F = 72 * WPReview.nativeOperator F := by
  ext j
  cases j with
  | zero => simp [clearedOperator_coeff_zero, WPReview.nativeOperator,
      WPReview.nativeTheta_coeff]
  | succ n =>
    rw [clearedOperator_coeff_succ, coeff_ofNat_mul, WPReview.nativeOperator_coeff_succ]
    ring

theorem termRegular_zero {K : Type*} [CommRing K] (F : K[X]) :
    termRegular 0 F = regularNative F := by
  simp [termRegular, regularNative, C_ofNat]
  ring

/-- The exact residual at every finite cutoff; the upper coefficient is retained. -/
theorem rational_native_regular_residual (n : ℕ) :
    regularNative (WPReview.nativePolynomial (n + 1)) =
      C (-72 * WPReview.nativeEndpoint (n + 1)) * X ^ n := by
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from X_ne_zero)
  rw [← clearedOperator_eq_X_regular, clearedOperator_rational,
    WPReview.native_truncation_residual (n + 1) (by omega), ← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_neg, map_ofNat, pow_succ]
  ring

/-- The native and Jacobi discriminants are the same actual polynomial after transport. -/
theorem native_discriminant_quadratic {K : Type*} [CommRing K] (F : K[X]) :
    2 * jacobiDiscriminant 0 (F.comp (1 - X ^ 2)) =
      (nativeDiscriminant F).comp (1 - X ^ 2) := by
  simp [jacobiDiscriminant, nativeDiscriminant, derivative_comp,
    derivative_mul, derivative_pow_succ, mul_comp, sub_comp, add_comp,
    pow_comp, ofNat_comp, C_ofNat]
  ring

/-- The entire native cutoff in the original quadratic variable. -/
noncomputable def halfNativeJacobi (p : ℕ) : ℚ[X] :=
  (WPReview.nativePolynomial ((p - 1) / 2 + 1)).comp (1 - X ^ 2)

theorem half_native_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.nativeEndpoint ((p - 1) / 2 + 1) =
      (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2) / 72 := by
  have he := congrArg (fun n : ℕ => (n : ℚ)) (WPFiniteWSource.half_exponent p hp)
  push_cast at he
  have hn : (((p - 1) / 2 : ℕ) : ℚ) = ((p : ℚ) - 1) / 2 := by linarith
  unfold WPReview.nativeEndpoint
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hn]
  ring

/-- The whole N-cutoff source, with its literal nonzero terminal coefficient. -/
theorem actual_half_native_square_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    jacobiSquare 0 (halfNativeJacobi p) =
      C (4 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2)) *
          X * (1 - X ^ 2) ^ ((p - 1) / 2) := by
  have hterminal : -72 * WPReview.nativeEndpoint ((p - 1) / 2 + 1) =
      -(p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2) := by
    rw [half_native_endpoint p hp]
    ring
  rw [halfNativeJacobi, termRegular_jacobi_source, termRegular_zero,
    rational_native_regular_residual, hterminal, mul_comp, C_comp, pow_comp, X_comp]
  simp only [map_mul, map_neg, map_ofNat]
  ring

/-- The actual self concomitant differentiates with the full cutoff residual. -/
theorem actual_half_native_weighted_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((1 - X ^ 2) * jacobiDiscriminant 0 (halfNativeJacobi p)).derivative =
      C (2 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2)) *
          X * (1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p := by
  have he := jacobiDiscriminant_zero_source (halfNativeJacobi p)
  rw [actual_half_native_square_source p hp] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℚ[X]) ≠ 0)
  simp only [map_mul, map_ofNat] at he ⊢
  linear_combination he

end WPFieldAssembly.NativeDiscriminant
