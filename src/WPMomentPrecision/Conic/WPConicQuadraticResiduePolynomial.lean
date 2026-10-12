import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

open scoped Polynomial
open Polynomial

namespace WPConicQuadraticResiduePolynomial

theorem coeff_one_sub_X_pow {K : Type*} [CommRing K] (m n : ℕ) :
    ((1 - X : K[X]) ^ m).coeff n = (m.choose n : K) * (-1 : K) ^ n := by
  have he : (1 - X : K[X]) ^ m = ((1 + X) ^ m).comp (C (-1) * X) := by
    simp only [pow_comp, add_comp, one_comp, X_comp, C_neg, C_1, neg_mul, one_mul]
    rfl
  rw [he, comp_C_mul_X_coeff, coeff_one_add_X_pow]

/-- The entire negative monomial cover numerator has its central coefficient zero. -/
theorem quadratic_cover_middle_zero {K : Type*} [CommRing K] (k : ℕ) :
    ((1 + X : K[X]) * (1 - X) ^ (2 * k + 1)).coeff (k + 1) = 0 := by
  have hc : (2 * k + 1).choose (k + 1) = (2 * k + 1).choose k :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_one_sub_X_pow,
    coeff_one_sub_X_pow, hc, pow_succ]
  ring

/-- After y=r^2 this is precisely the coefficient contributing to a negative-cover residue. -/
theorem quadratic_cover_even_middle_zero {K : Type*} [CommRing K] (k : ℕ) :
    ((1 + X ^ 2 : K[X]) * (1 - X ^ 2) ^ (2 * k + 1)).coeff (2 * k + 2) = 0 := by
  have he : (1 + X ^ 2 : K[X]) * (1 - X ^ 2) ^ (2 * k + 1) =
      Polynomial.expand K 2 ((1 + X) * (1 - X) ^ (2 * k + 1)) := by
    rw [expand_eq_comp_X_pow]
    simp only [mul_comp, add_comp, sub_comp, one_comp, X_comp, pow_comp]
  rw [he, show 2 * k + 2 = 2 * (k + 1) by omega,
    coeff_expand_mul' (by norm_num : 0 < 2), quadratic_cover_middle_zero]

end WPConicQuadraticResiduePolynomial
