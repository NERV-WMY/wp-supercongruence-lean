import WPOriginalConductorMoment

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral

namespace WPActualPullbackSource

/-- The actual V(x), before x=y^2. -/
noncomputable def Vpolynomial : ℚ[X] := Polynomial.C (1 / 125) * (4 * Polynomial.X - 1) ^ 2 *
  (4 - Polynomial.X)

noncomputable def Xpull : ℚ[T;T⁻¹] := T 2
noncomputable def Vpull : ℚ[T;T⁻¹] := substitute Vpolynomial Xpull
noncomputable def Qpull : ℚ[T;T⁻¹] :=
  C (1 / 125) * (4 * Xpull - 1) * (4 - Xpull) ^ 2 * T (-6)
noncomputable def Spull : ℚ[T;T⁻¹] := Vpull * T (-1)

/-- The entire actual Fe is retained, with no jet or coefficient band removed. -/
noncomputable def Fpull (e : ℕ) (L : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  substitute (WPReview.nativePolynomial (e + 1)) L

/-- The n=0 slot is exactly zero; the remaining slots are cn/n for 1<=n<=e. -/
noncomputable def Hpolynomial (e : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range (e + 1), Polynomial.monomial n
    (WPReview.nativeCoefficient n / (n : ℚ))

noncomputable def Hpull (e : ℕ) (L : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  substitute (Hpolynomial e) L

/-- Actual chi after x=y^2, without a residue or moment-value premise. -/
noncomputable def chi (p N e : ℕ) : ℚ[T;T⁻¹] :=
  C (1 / (p : ℚ)) * (Fpull e Vpull - T (2 * (N : ℤ)) * Fpull e Qpull)

/-- S^p*dlog V, explicitly canceled as a finite Laurent polynomial. -/
noncomputable def baseDensity (p : ℕ) : ℚ[T;T⁻¹] :=
  T (-(p : ℤ)) * Vpull ^ (p - 1) * derivative Vpull

/-- S^p*dlog S, with the actual square-root logarithmic term retained. -/
noncomputable def logarithmicSDensity (p : ℕ) : ℚ[T;T⁻¹] :=
  baseDensity p - Vpull ^ p * T (-(p : ℤ) - 1)

noncomputable def weightedEta (p N e : ℕ) : ℚ[T;T⁻¹] :=
  chi p N e * baseDensity p + Hpull e Vpull * logarithmicSDensity p

/-- The complete native source coefficients, with the root-owned actual numerator. -/
noncomputable def nativeDensity (p e : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.range (e + 1),
    ∑ a ∈ Finset.range (3 * (p + n)),
      C (WPReview.nativeCoefficient n * (2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n))) *
        ((WPNativeMomentIntegrality.nativeNumerator p n).coeff a : ℚ)) *
      T (WPNativeMomentIntegrality.primitiveDenominator n a - 1)

noncomputable def actualShortMoment (p e : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (e + 1),
    WPReview.nativeCoefficient n * WPNativeMomentIntegrality.actualMonomialMoment p n

theorem Hpolynomial_coeff (e n : ℕ) : (Hpolynomial e).coeff n =
    if n < e + 1 then WPReview.nativeCoefficient n / (n : ℚ) else 0 := by
  classical
  simp only [Hpolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < e + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b _hb hbn; simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by have := Finset.mem_range.mp hb; omega
    simp [hbn]

theorem Hpolynomial_theta (e : ℕ) :
    Polynomial.X * Polynomial.derivative (Hpolynomial e) =
      WPReview.nativePolynomial (e + 1) - 1 := by
  ext n
  change (WPReview.nativeTheta (Hpolynomial e)).coeff n = _
  rw [WPReview.nativeTheta_coeff, Hpolynomial_coeff, Polynomial.coeff_sub,
    WPReview.nativePolynomial_coeff, Polynomial.coeff_one]
  cases n with
  | zero => simp [WPReview.nativeCoefficient_zero]
  | succ n =>
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    split_ifs <;> simp_all
    field_simp

theorem Hpolynomial_zero (e : ℕ) : (Hpolynomial e).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Hpolynomial_coeff]
  simp

theorem Vpolynomial_derivative : Polynomial.derivative Vpolynomial =
    Polynomial.C (3 / 125) * (4 * Polynomial.X - 1) * (11 - 4 * Polynomial.X) := by
  apply Polynomial.funext
  intro x
  norm_num [Vpolynomial, Polynomial.derivative_mul, Polynomial.derivative_pow_succ]
  ring

theorem evaluate_Vpull (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy Vpull = (4 * y ^ 2 - 1) ^ 2 * (4 - y ^ 2) / 125 := by
  rw [Vpull, evaluate_substitute]
  have hx : evaluate y hy Xpull = y ^ 2 := by
    simpa [Xpull] using evaluate_monomial 2 1 y hy
  rw [hx]
  norm_num [Vpolynomial]
  ring

theorem evaluate_Qpull (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy Qpull = (4 * y ^ 2 - 1) * (4 - y ^ 2) ^ 2 / (125 * y ^ 6) := by
  have hT (z : ℤ) : evaluate y hy (T z) = y ^ z := by
    simpa using evaluate_monomial z 1 y hy
  simp only [Qpull, Xpull, map_mul, map_sub, map_pow, map_ofNat, map_one,
    evaluate_C, hT]
  norm_num [zpow_neg, zpow_natCast]
  ring

theorem evaluate_Spull (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy Spull = evaluate y hy Vpull / y := by
  rw [Spull, map_mul]
  have hT : evaluate y hy (T (-1)) = y⁻¹ := by
    simpa using evaluate_monomial (-1) 1 y hy
  rw [hT, div_eq_mul_inv]

theorem evaluate_derivative_Vpull (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy (derivative Vpull) =
      6 / 125 * (4 * y ^ 2 - 1) * (11 - 4 * y ^ 2) * y := by
  rw [Vpull, derivative_substitute, map_mul, Vpolynomial_derivative,
    evaluate_substitute]
  have hx : evaluate y hy Xpull = y ^ 2 := by
    simpa [Xpull] using evaluate_monomial 2 1 y hy
  have hd : derivative Xpull = C 2 * T 1 := by
    simpa [Xpull] using derivative_monomial 2 1
  rw [hx, hd, evaluate_monomial]
  norm_num
  ring

theorem evaluate_Fpull (e : ℕ) (L : ℚ[T;T⁻¹]) (y : ℚ) (hy : y ≠ 0) :
    evaluate y hy (Fpull e L) =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n *
        (evaluate y hy L) ^ n := by
  rw [Fpull, evaluate_substitute]
  simp [WPReview.nativePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem nativeDensity_endpoints (p e : ℕ) :
    endpointIntegral (1 / 2) 2 (nativeDensity p e) = actualShortMoment p e := by
  classical
  unfold nativeDensity actualShortMoment
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_sum, WPNativeMomentIntegrality.actual_moment_endpoint_formula,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [integral_monomial]
  rw [show WPNativeMomentIntegrality.primitiveDenominator n a - 1 + 1 =
    WPNativeMomentIntegrality.primitiveDenominator n a by omega]
  ring

theorem actual_native_Laurent_density (p e : ℕ) (hp : 1 ≤ p) :
    nativeDensity p e = C ((p : ℚ) / 9) * T (-1) * Vpull ^ (p - 1) *
      derivative Vpull * Fpull e Qpull := by
  classical
  apply ext_positive_integers
  intro j
  let y : ℚ := (j : ℚ) + 3
  have hy : y ≠ 0 := by dsimp [y]; positivity
  have hy3 : 3 ≤ y := by
    dsimp [y]
    have hj : (0 : ℚ) ≤ (j : ℚ) := by positivity
    linarith
  have hA : 4 * y ^ 2 - 1 ≠ 0 := by nlinarith
  have hB : 4 - y ^ 2 ≠ 0 := by nlinarith
  have hT (z : ℤ) : evaluate y hy (T z) = y ^ z := by
    simpa using evaluate_monomial z 1 y hy
  change evaluate y hy _ = evaluate y hy _
  unfold nativeDensity
  rw [map_sum]
  simp only [map_mul, map_pow, evaluate_C, hT]
  rw [evaluate_Vpull, evaluate_derivative_Vpull, evaluate_Fpull, evaluate_Qpull,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_sum]
  simp only [map_mul, evaluate_C, hT]
  have hd := WPNativeMomentIntegrality.actual_native_density_full_series p n hp y hy hA hB
  have hvpow :
      ((4 * y ^ 2 - 1) ^ 2 * (4 - y ^ 2) / 125) ^ p =
        ((4 * y ^ 2 - 1) ^ 2 * (4 - y ^ 2) / 125) ^ (p - 1) *
          ((4 * y ^ 2 - 1) ^ 2 * (4 - y ^ 2) / 125) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ = WPReview.nativeCoefficient n *
        (2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n)) *
          ∑ a ∈ Finset.range (3 * (p + n)),
            ((WPNativeMomentIntegrality.nativeNumerator p n).coeff a : ℚ) *
              y ^ (WPNativeMomentIntegrality.primitiveDenominator n a - 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = WPReview.nativeCoefficient n *
        ((p : ℚ) / 2 * WPFiniteConductorReflection.firstFlux p n (y / 2)) :=
      congrArg (fun a : ℚ => WPReview.nativeCoefficient n * a) hd.symm
    _ = _ := by
      unfold WPFiniteConductorReflection.firstFlux
      rw [WPNativeMomentIntegrality.scaled_q2,
        WPNativeMomentIntegrality.scaled_q1 y hy,
        WPNativeMomentIntegrality.scaled_first_weight y hA hB, hvpow]
      simp only [zpow_neg_one]
      field_simp [hy, hA, hB]
      ring

theorem actual_chi_identity (p N e : ℕ) (hp : 1 ≤ p) :
    C (p : ℚ) * chi p N e = Fpull e Vpull - T (2 * (N : ℤ)) * Fpull e Qpull := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  rw [chi, ← mul_assoc, ← map_mul]
  simp [hpq]

end WPActualPullbackSource
