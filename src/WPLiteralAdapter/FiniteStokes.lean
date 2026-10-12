import WPActualSourceCoefficients
import WPActualPrimitivePolynomialPart
import WPLiteralNativeNormalization
import WPReview.FiniteStokes

open scoped BigOperators
open WPForcedSourceStokes
open Polynomial

namespace WPLiteralAdapter

noncomputable section

theorem actual_rational_polynomial_coefficient (P : ℚ[X]) (k : ℕ) :
    actualRationalCoefficient (algebraMap ℚ[X] (RatFunc ℚ) P) k = P.coeff k := by
  rw [actualRationalCoefficient, actualRationalSeries,
    ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) (LaurentSeries ℚ)]
  change (((P : PowerSeries ℚ) : LaurentSeries ℚ).coeff (k : ℤ)) = _
  rw [LaurentSeries.coeff_coe_powerSeries, Polynomial.coeff_coe]

/-- The retained six-state weighted G is exactly the same cubic polynomial used by the literal sum. -/
theorem actual_weighted_G_outer_polynomial (p : ℕ) :
    nativeWeightedG p = algebraMap ℚ[X] (RatFunc ℚ)
      (WPLiteralNativeNormalization.outerPolynomial p) := by
  have hP : 9*squaredNativePolynomial p + 126*thetaPower 1 (squaredNativePolynomial p) +
      532*thetaPower 2 (squaredNativePolynomial p) =
      ∑ n∈Finset.range p, monomial n ((WPReview.weightNat n : ℚ)*WPReview.nativeCoefficient n^2) := by
    ext n
    rw [finite_monomial_sum_coefficient]
    simp only [coeff_add, coeff_ofNat_mul, thetaPower_coeff, squaredNativePolynomial_coeff]
    by_cases hn : n<p
    · simp only [if_pos hn]
      simp only [WPReview.weightNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    · simp [hn]
  rw [native_weighted_G_literal, hP]
  change pullbackHom (∑ n∈Finset.range p,
    monomial n ((WPReview.weightNat n : ℚ)*WPReview.nativeCoefficient n^2)) = _
  rw [map_sum]
  simp only [pullbackHom_apply, pullbackValue_monomial,
    WPLiteralNativeNormalization.outerPolynomial]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
    lambda, mul_pow, pow_mul, map_pow, map_mul]
  norm_num [symbol, map_ratCast]
  ring

/-- Finite Stokes applies to the honest rational expansion and keeps both actual endpoints. -/
theorem actual_rational_finite_stokes (L : ℕ) (f : RatFunc ℚ) :
    WPReview.Gamma L
      (fun k => actualRationalCoefficient ((1-symbol)*rationalDerivative f-f/2) k) =
      -actualRationalCoefficient f 0/2 + ((L : ℚ)+1)*WPReview.gamma L*
        actualRationalCoefficient f ((L+1 : ℕ) : ℤ) := by
  have he : (fun k : ℕ => actualRationalCoefficient
      ((1-symbol)*rationalDerivative f-f/2) k) =
      WPReview.beta (fun k => actualRationalCoefficient f k) := by
    funext k
    rw [actual_beta_coefficient]
    simp only [WPReview.beta, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one,
      Int.cast_natCast]
  rw [he]
  exact WPReview.finite_stokes L (fun k => actualRationalCoefficient f k)

/-- The complete actual scalar equation after its finite rational moment, before endpoint elimination. -/
theorem actual_scalar_finite_stokes (p L : ℕ) (hp : 0<p) :
    WPReview.Gamma L (fun k => (2*(k : ℚ)+1)*actualRationalCoefficient (nativeWeightedG p) k) =
      -3375*actualRationalCoefficient (actualTotalPrimitive p) 0 +
        6750*((L : ℚ)+1)*WPReview.gamma L*
          actualRationalCoefficient (actualTotalPrimitive p) ((L+1 : ℕ) : ℤ) +
        3375*WPReview.Gamma L (fun k => actualRationalCoefficient (actualTotalSource p) k) +
        WPReview.Gamma L (fun k => actualRationalCoefficient (nativeSquareForcing p) k) := by
  have hcoeff (k : ℕ) :
      (2*(k : ℚ)+1)*actualRationalCoefficient (nativeWeightedG p) k =
        6750*actualRationalCoefficient
          ((1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2) k +
        3375*actualRationalCoefficient (actualTotalSource p) k +
        actualRationalCoefficient (nativeSquareForcing p) k := by
    rw [actual_beta_coefficient]
    have h := actual_full_source_coefficient p hp (k : ℤ)
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_natCast] using h
  have hsum : WPReview.Gamma L
      (fun k => (2*(k : ℚ)+1)*actualRationalCoefficient (nativeWeightedG p) k) =
      6750*WPReview.Gamma L (fun k => actualRationalCoefficient
        ((1-symbol)*rationalDerivative (actualTotalPrimitive p)-actualTotalPrimitive p/2) k) +
      3375*WPReview.Gamma L (fun k => actualRationalCoefficient (actualTotalSource p) k) +
      WPReview.Gamma L (fun k => actualRationalCoefficient (nativeSquareForcing p) k) := by
    unfold WPReview.Gamma
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp only
    rw [hcoeff]
    ring
  rw [hsum, actual_rational_finite_stokes]
  ring

/-- The true extended boundary is the Taylor coefficient 3p, with its restoring factor 3p. -/
theorem actual_scalar_extended_stokes (p : ℕ) (hp : 0<p) :
    WPReview.Gamma (3*p-1)
      (fun k => (2*(k : ℚ)+1)*actualRationalCoefficient (nativeWeightedG p) k) =
      -3375*actualRationalCoefficient (actualTotalPrimitive p) 0 +
        6750*(3*(p : ℚ))*WPReview.gamma (3*p-1)*
          actualRationalCoefficient (actualTotalPrimitive p) ((3*p : ℕ) : ℤ) +
        3375*WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (actualTotalSource p) k) +
        WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (nativeSquareForcing p) k) := by
  have h := actual_scalar_finite_stokes p (3*p-1) hp
  have he : 3*p-1+1=3*p := by omega
  rw [he] at h
  have hc : ((3*p-1 : ℕ) : ℚ)+1=3*(p : ℚ) := by
    rw [← Nat.cast_add_one, he, Nat.cast_mul, Nat.cast_ofNat]
  rw [hc] at h
  exact h

/-- Exact A1 and the complete forced scalar combine before any p-adic endpoint deletion. -/
theorem actual_literal_extended_stokes (p : ℕ) (hp : 0<p) :
    WPReview.literalSum p =
      -3375*actualRationalCoefficient (actualTotalPrimitive p) 0 +
        6750*(3*(p : ℚ))*WPReview.gamma (3*p-1)*
          actualRationalCoefficient (actualTotalPrimitive p) ((3*p : ℕ) : ℤ) +
        3375*WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (actualTotalSource p) k) +
        WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (nativeSquareForcing p) k) := by
  have h := actual_scalar_extended_stokes p hp
  have he : WPReview.Gamma (3*p-1)
      (fun k => (2*(k : ℚ)+1)*actualRationalCoefficient (nativeWeightedG p) k) =
      WPReview.literalSum p := by
    rw [actual_weighted_G_outer_polynomial]
    simp only [actual_rational_polynomial_coefficient]
    have hf : (fun k : ℕ => (2*(k : ℚ)+1)*
        (WPLiteralNativeNormalization.outerPolynomial p).coeff k) =
        (fun k => (WPLiteralNativeNormalization.outerOperator
          (WPLiteralNativeNormalization.outerPolynomial p)).coeff k) := by
      funext k
      rw [WPLiteralNativeNormalization.outerOperator_coeff]
    rw [hf]
    exact WPLiteralNativeNormalization.Gamma_outer_literal_extended p
  rw [he] at h
  exact h

end

end WPLiteralAdapter
