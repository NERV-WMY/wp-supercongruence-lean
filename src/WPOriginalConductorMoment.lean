import WPFiniteConductorCoefficient
import WPFiniteConductorFlux
import WPFiniteConductorIntegrality
import WPFiniteLaurentIntegral
import WPActualNativeMoment

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral
open WPFiniteConductorPolynomial WPFiniteConductorReflection WPNativeMomentIntegrality

namespace WPOriginalConductorMoment

noncomputable def twoFluxLaurent (p e : ℕ) : ℚ[T;T⁻¹] :=
  ∑ n ∈ Finset.range (e + 1),
    ∑ a ∈ Finset.range (3 * (p + n)),
      C (WPReview.nativeCoefficient n * (2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n))) *
        ((nativeNumerator p n).coeff a : ℚ)) *
      (T (primitiveDenominator n a - 1) + T (-primitiveDenominator n a - 1))

theorem reciprocal_primitive_endpoint (ell : ℤ) :
    monomialEndpoint ell 1 2 + monomialEndpoint (-ell) 1 2 =
      monomialEndpoint ell (1 / 2) 2 := by
  by_cases hell : ell = 0
  · simp [hell, monomialEndpoint]
  · have hq : (ell : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hell
    unfold monomialEndpoint
    rw [one_zpow, one_zpow, reciprocal_two_zpow]
    push_cast
    field_simp [hq]
    ring

theorem twoFluxLaurent_endpoints (p e : ℕ) :
    endpointIntegral 1 2 (twoFluxLaurent p e) =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n * actualMonomialMoment p n := by
  classical
  unfold twoFluxLaurent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_sum, actual_moment_endpoint_formula, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [mul_add, map_add, integral_monomial, integral_monomial]
  rw [show primitiveDenominator n a - 1 + 1 = primitiveDenominator n a by omega,
    show -primitiveDenominator n a - 1 + 1 = -primitiveDenominator n a by omega,
    ← mul_add, reciprocal_primitive_endpoint]
  ring

theorem reciprocal_normalized_density (p n : ℕ) (hp : 1 ≤ p) (s : ℚ)
    (hs : s ≠ 0) (hA : 4 * s ^ 2 - 1 ≠ 0) (hB : 4 - s ^ 2 ≠ 0) :
    (p : ℚ) / 2 * secondFlux p n (s / 2) =
      2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n)) *
        ∑ a ∈ Finset.range (3 * (p + n)), ((nativeNumerator p n).coeff a : ℚ) *
          s ^ (-primitiveDenominator n a - 1) := by
  have hsr : s / 2 ≠ 0 := div_ne_zero hs (by norm_num)
  have hr1 : 1 - (s / 2) ^ 2 ≠ 0 := by
    have h : 1 - (s / 2) ^ 2 = (4 - s ^ 2) / 4 := by ring
    rw [h]
    exact div_ne_zero hB (by norm_num)
  have hr16 : 16 * (s / 2) ^ 2 - 1 ≠ 0 := by
    convert hA using 1; ring
  have hphi : reciprocalCoordinate (s / 2) = (1 / s) / 2 := by
    unfold reciprocalCoordinate
    field_simp [hs]; norm_num
  have hrefl := actual_two_flux_reciprocal p n (s / 2) hsr hr1 hr16
  rw [hphi, show (-1 : ℚ) / (4 * (s / 2) ^ 2) = -1 / s ^ 2 by ring] at hrefl
  have hscaled : (p : ℚ) / 2 * secondFlux p n (s / 2) =
      ((p : ℚ) / 2 * firstFlux p n ((1 / s) / 2)) / s ^ 2 := by
    linear_combination (p : ℚ) / 2 * hrefl
  have hAinv : 4 * (1 / s) ^ 2 - 1 ≠ 0 := by
    have h : 4 * (1 / s) ^ 2 - 1 = (4 - s ^ 2) / s ^ 2 := by field_simp [hs]
    rw [h]
    exact div_ne_zero hB (pow_ne_zero 2 hs)
  have hBinv : 4 - (1 / s) ^ 2 ≠ 0 := by
    have h : 4 - (1 / s) ^ 2 = (4 * s ^ 2 - 1) / s ^ 2 := by field_simp [hs]
    rw [h]
    exact div_ne_zero hA (pow_ne_zero 2 hs)
  rw [hscaled, actual_native_density_full_series p n hp (1 / s)
    (div_ne_zero (by norm_num) hs) hAinv hBinv, mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [mul_div_assoc]
  congr 1
  calc
    (1 / s) ^ (primitiveDenominator n a - 1) / s ^ 2 =
        s ^ (-(primitiveDenominator n a - 1)) / s ^ (2 : ℤ) := by
      simp
    _ = s ^ (-(primitiveDenominator n a - 1) - 2) := (zpow_sub₀ hs _ _).symm
    _ = _ := by congr 1; omega

theorem normalized_two_source_series (p n : ℕ) (hp : 1 ≤ p) (s : ℚ)
    (hs : s ≠ 0) (hA : 4 * s ^ 2 - 1 ≠ 0) (hB : 4 - s ^ 2 ≠ 0) :
    (p : ℚ) / 2 * (firstFlux p n (s / 2) + secondFlux p n (s / 2)) =
      2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n)) *
        ∑ a ∈ Finset.range (3 * (p + n)), ((nativeNumerator p n).coeff a : ℚ) *
          (s ^ (primitiveDenominator n a - 1) + s ^ (-primitiveDenominator n a - 1)) := by
  rw [mul_add, actual_native_density_full_series p n hp s hs hA hB,
    reciprocal_normalized_density p n hp s hs hA hB, ← mul_add,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem Laurent_V_coordinate (s : ℚ) (hs : s ≠ 0) :
    evaluate s hs V = Ucoordinate (s / 2) := by
  rw [evaluate_V]
  unfold Ucoordinate
  field_simp [hs]; ring

theorem Laurent_V_derivative_coordinate (s : ℚ) (hs : s ≠ 0) :
    evaluate s hs (derivative V) = Uderivative (s / 2) / 2 := by
  rw [evaluate_derivative_V]
  unfold Uderivative
  field_simp [hs]; ring

theorem original_polynomial_Laurent_evaluation (p e : ℕ) (s : ℚ) (hs : s ≠ 0) :
    evaluate s hs
      (C (p : ℚ) * substitute ((Be p e).comp WPFiniteGammaIntegral.quadraticArgument) V *
        derivative V) =
      (p : ℚ) / 2 * (Be p e).eval (xCoordinate (s / 2)) * Uderivative (s / 2) := by
  rw [map_mul, map_mul, evaluate_C, evaluate_substitute,
    Laurent_V_coordinate, Laurent_V_derivative_coordinate]
  simp only [Polynomial.eval_comp, WPFiniteGammaIntegral.quadraticArgument,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  unfold xCoordinate
  ring

/-- The ORIGINAL Be density equals the two complete finite Laurent source channels. -/
theorem original_polynomial_two_primitives (p e : ℕ) (he : e + 4 ≤ p) :
    C (p : ℚ) * substitute ((Be p e).comp WPFiniteGammaIntegral.quadraticArgument) V *
        derivative V = twoFluxLaurent p e := by
  classical
  apply ext_positive_integers
  intro j
  let s : ℚ := (j : ℚ) + 3
  have hs : s ≠ 0 := by dsimp [s]; positivity
  have hs3 : 3 ≤ s := by
    dsimp [s]
    have hj : (0 : ℚ) ≤ (j : ℚ) := by positivity
    linarith
  have hA : 4 * s ^ 2 - 1 ≠ 0 := by nlinarith
  have hB : 4 - s ^ 2 ≠ 0 := by nlinarith
  have hsr : s / 2 ≠ 0 := div_ne_zero hs (by norm_num)
  change evaluate s hs _ = evaluate s hs _
  rw [original_polynomial_Laurent_evaluation]
  have hsource := Be_actual_two_flux_density p e he (s / 2) hsr
  rw [mul_assoc, hsource, Finset.mul_sum]
  unfold twoFluxLaurent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [show (p : ℚ) / 2 * (WPReview.nativeCoefficient n *
      (firstFlux p n (s / 2) + secondFlux p n (s / 2))) =
      WPReview.nativeCoefficient n * ((p : ℚ) / 2 *
        (firstFlux p n (s / 2) + secondFlux p n (s / 2))) by ring,
    normalized_two_source_series p n (by omega) s hs hA hB,
    Finset.mul_sum, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [map_mul, map_add, evaluate_C]
  have hT (z : ℤ) : evaluate s hs (T z) = s ^ z := by
    simpa using evaluate_monomial z 1 s hs
  rw [hT, hT]
  ring

/-- Exact original coefficient conductor Gamma equals the actual native primitive moment. -/
theorem original_p_Gamma_eq_native_moment (p e : ℕ) (he : e + 4 ≤ p) :
    (p : ℚ) * WPReview.Gamma (3 * p - 1) (fun k => (Be p e).coeff k) =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n * actualMonomialMoment p n := by
  rw [← Gamma_finite_pullback (Be p e) (3 * p - 1) (Be_degree p e he)]
  have hsmul (L : ℚ[T;T⁻¹]) :
      endpointIntegral 1 2 (C (p : ℚ) * L) = (p : ℚ) * endpointIntegral 1 2 L := by
    rw [← LaurentPolynomial.smul_eq_C_mul, map_smul]
    rfl
  rw [← hsmul, ← mul_assoc, original_polynomial_two_primitives p e he,
    twoFluxLaurent_endpoints]

theorem original_p_Gamma_eq_native_cutoff (p : ℕ) (hp : 19 ≤ p) :
    (p : ℚ) * WPReview.Gamma (3 * p - 1)
      (fun k => (Be p (p - 1 - p / 6)).coeff k) =
      ∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * actualMonomialMoment p n := by
  apply original_p_Gamma_eq_native_moment
  have hdiv : 3 ≤ p / 6 := by omega
  omega

end WPOriginalConductorMoment
