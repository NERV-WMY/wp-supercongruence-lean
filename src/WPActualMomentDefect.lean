import WPActualPullbackSource

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource

namespace WPActualMomentDefect

noncomputable def baseMoment (p : ℕ) : ℚ :=
  (p : ℚ) / 9 * endpointIntegral (1 / 2) 2 (baseDensity p)

noncomputable def etaIntegral (p N e : ℕ) : ℚ :=
  endpointIntegral (1 / 2) 2 (weightedEta p N e)

noncomputable def etaPeriod (p N e : ℕ) : ℚ := (p : ℚ) * etaIntegral p N e

theorem Hpull_theta (e : ℕ) :
    Vpull * derivative (Hpull e Vpull) = (Fpull e Vpull - 1) * derivative Vpull := by
  have h := congrArg (fun P : ℚ[X] => substitute P Vpull) (Hpolynomial_theta e)
  have htheta : Vpull * substitute (Polynomial.derivative (Hpolynomial e)) Vpull =
      Fpull e Vpull - 1 := by
    simpa [substitute, Fpull] using h
  rw [Hpull, derivative_substitute]
  calc
    _ = (Vpull * substitute (Polynomial.derivative (Hpolynomial e)) Vpull) *
        derivative Vpull := by ring
    _ = _ := by rw [htheta]

theorem Spull_power (p : ℕ) : Spull ^ p = Vpull ^ p * T (-(p : ℤ)) := by
  rw [Spull, mul_pow, T_pow]
  simp

theorem derivative_Spull_power (p : ℕ) (hp : 1 ≤ p) :
    derivative (Spull ^ p) = C (p : ℚ) * logarithmicSDensity p := by
  have hi : p - 1 + 1 = p := by omega
  have hc : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by exact_mod_cast hi
  have hV : derivative (Vpull ^ p) = C (p : ℚ) * Vpull ^ (p - 1) * derivative Vpull := by
    simpa only [hi, hc] using derivative_pow_succ Vpull (p - 1)
  have hT : derivative (T (-(p : ℤ))) = C (-(p : ℚ)) * T (-(p : ℤ) - 1) := by
    simpa using derivative_monomial (-(p : ℤ)) 1
  rw [Spull_power, derivative_mul, hV, hT]
  unfold logarithmicSDensity baseDensity
  rw [map_neg]
  ring

/-- Actual finite integration by parts, retaining all coefficients of He. -/
theorem derivative_actual_product (p e : ℕ) (hp : 1 ≤ p) :
    derivative (Spull ^ p * Hpull e Vpull) =
      C (p : ℚ) * Hpull e Vpull * logarithmicSDensity p +
        baseDensity p * (Fpull e Vpull - 1) := by
  rw [derivative_mul, derivative_Spull_power p hp]
  have hVp : Vpull ^ p = Vpull ^ (p - 1) * Vpull := by
    rw [← pow_succ]
    congr 1
    omega
  have hterm : Spull ^ p * derivative (Hpull e Vpull) =
      baseDensity p * (Fpull e Vpull - 1) := by
    rw [Spull_power, hVp]
    calc
      _ = T (-(p : ℤ)) * Vpull ^ (p - 1) *
          (Vpull * derivative (Hpull e Vpull)) := by ring
      _ = _ := by rw [Hpull_theta]; unfold baseDensity; ring
  rw [hterm]
  ring

theorem actual_native_chi_density (p N e : ℕ) (hp : 1 ≤ p) (hN : p = 2 * N + 1) :
    nativeDensity p e = C ((p : ℚ) / 9) *
      (baseDensity p * Fpull e Vpull - C (p : ℚ) * baseDensity p * chi p N e) := by
  have hchi : Fpull e Vpull - C (p : ℚ) * chi p N e =
      T (2 * (N : ℤ)) * Fpull e Qpull := by
    rw [actual_chi_identity p N e hp]
    ring
  have hT : T (-(p : ℤ)) * T (2 * (N : ℤ)) = (T (-1) : ℚ[T;T⁻¹]) := by
    rw [← T_add]
    congr 1
    have hpZ : (p : ℤ) = 2 * (N : ℤ) + 1 := by exact_mod_cast hN
    omega
  rw [actual_native_Laurent_density p e hp]
  calc
    _ = C ((p : ℚ) / 9) * (T (-1) * Vpull ^ (p - 1) * derivative Vpull * Fpull e Qpull) := by ring
    _ = C ((p : ℚ) / 9) * (baseDensity p * (T (2 * (N : ℤ)) * Fpull e Qpull)) := by
      unfold baseDensity
      rw [show T (-(p : ℤ)) * Vpull ^ (p - 1) * derivative Vpull *
          (T (2 * (N : ℤ)) * Fpull e Qpull) =
        (T (-(p : ℤ)) * T (2 * (N : ℤ))) * Vpull ^ (p - 1) * derivative Vpull * Fpull e Qpull by ring,
        hT]
    _ = _ := by rw [← hchi]; ring

theorem actual_density_defect_identity (p N e : ℕ) (hp : 1 ≤ p) (hN : p = 2 * N + 1) :
    nativeDensity p e = C ((p : ℚ) / 9) * baseDensity p -
      C ((p : ℚ) ^ 2 / 9) * weightedEta p N e +
        C ((p : ℚ) / 9) * derivative (Spull ^ p * Hpull e Vpull) := by
  rw [actual_native_chi_density p N e hp hN, derivative_actual_product p e hp]
  have hc : C ((p : ℚ) ^ 2 / 9) = (C ((p : ℚ) / 9) * C (p : ℚ) : ℚ[T;T⁻¹]) := by
    rw [← map_mul]
    congr 1
    ring
  rw [hc]
  unfold weightedEta
  ring

theorem actual_product_both_endpoints (p e : ℕ) :
    evaluate 2 (by norm_num) (Spull ^ p * Hpull e Vpull) = 0 ∧
      evaluate (1 / 2) (by norm_num) (Spull ^ p * Hpull e Vpull) = 0 := by
  have hleft : evaluate (1 / 2) (by norm_num) Vpull = 0 := by
    rw [evaluate_Vpull]; norm_num
  have hright : evaluate 2 (by norm_num) Vpull = 0 := by
    rw [evaluate_Vpull]; norm_num
  constructor
  · rw [map_mul, Hpull, evaluate_substitute, hright, Hpolynomial_zero, mul_zero]
  · rw [map_mul, Hpull, evaluate_substitute, hleft, Hpolynomial_zero, mul_zero]

/-- NC60 as an exact identity for the entire actual short native moment. -/
theorem actual_short_moment_decomposition (p N e : ℕ) (hp : 1 ≤ p) (hN : p = 2 * N + 1) :
    actualShortMoment p e = baseMoment p - (p : ℚ) ^ 2 / 9 * etaIntegral p N e := by
  rw [← nativeDensity_endpoints, actual_density_defect_identity p N e hp hN]
  simp only [map_add, map_sub]
  have hsmul (a : ℚ) (L : ℚ[T;T⁻¹]) :
      endpointIntegral (1 / 2) 2 (C a * L) = a * endpointIntegral (1 / 2) 2 L := by
    rw [← LaurentPolynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [hsmul, hsmul, hsmul, integral_derivative _ (1 / 2) 2 (by norm_num) (by norm_num),
    (actual_product_both_endpoints p e).1, (actual_product_both_endpoints p e).2]
  simp only [sub_self, mul_zero, add_zero]
  rfl

theorem actual_short_moment_period_decomposition (p N e : ℕ) (hp : 1 ≤ p)
    (hN : p = 2 * N + 1) :
    actualShortMoment p e = baseMoment p - (p : ℚ) / 9 * etaPeriod p N e := by
  rw [actual_short_moment_decomposition p N e hp hN]
  unfold etaPeriod
  ring

end WPActualMomentDefect
