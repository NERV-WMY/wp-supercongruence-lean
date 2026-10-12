import WPActualHasseReciprocal
import Mathlib.RingTheory.LaurentSeries

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial

namespace WPRationalInfinitySeries

theorem polynomial_ratfunc_eval {K : Type*} [Field K] (P : K[X]) :
    P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X) =
      algebraMap K[X] (RatFunc K) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [eval₂_add, map_add, hP, hQ]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
      map_mul, map_pow, RatFunc.algebraMap_C]

theorem rational_reflect_eval {K : Type*} [Field K] (m : ℕ) (P : K[X])
    (hP : P.natDegree ≤ m) :
    algebraMap K[X] (RatFunc K) (P.reflect m) =
      (algebraMap K[X] (RatFunc K) X) ^ m *
        P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ := by
  have hx : algebraMap K[X] (RatFunc K) X ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have he := WPActualHasseReciprocal.eval_reflect m (P.map RatFunc.C)
    (natDegree_map_le.trans hP) (algebraMap K[X] (RatFunc K) X) hx
  rw [reflect_map, eval_map, eval_map, polynomial_ratfunc_eval] at he
  exact he

/-- Reciprocal coordinates retain the Jacobian and the complete numerator and denominator. -/
theorem rational_infinity_density {K : Type*} [Field K] (m : ℕ) (P D : K[X])
    (hP : P.natDegree ≤ m) (hD : D.natDegree = m + 2) (hD0 : D ≠ 0) :
    -(algebraMap K[X] (RatFunc K) X)⁻¹ ^ 2 *
        P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ /
        D.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ =
      -algebraMap K[X] (RatFunc K) (P.reflect m) /
        algebraMap K[X] (RatFunc K) (D.reflect (m + 2)) := by
  have hx : algebraMap K[X] (RatFunc K) X ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hd : algebraMap K[X] (RatFunc K) (D.reflect (m + 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (reflect_eq_zero_iff.not.mpr hD0)
  have hpv : P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ =
      algebraMap K[X] (RatFunc K) (P.reflect m) /
        (algebraMap K[X] (RatFunc K) X) ^ m := by
    apply (eq_div_iff (pow_ne_zero m hx)).mpr
    linear_combination -(rational_reflect_eval m P hP)
  have hdv : D.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ =
      algebraMap K[X] (RatFunc K) (D.reflect (m + 2)) /
        (algebraMap K[X] (RatFunc K) X) ^ (m + 2) := by
    apply (eq_div_iff (pow_ne_zero (m + 2) hx)).mpr
    linear_combination -(rational_reflect_eval (m + 2) D hD.le)
  rw [hpv, hdv, pow_add]
  field_simp

theorem powerSeries_inverse_cast {K : Type*} [Field K] (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    ((f⁻¹ : K⟦X⟧) : K⸨X⸩) = (f : K⸨X⸩)⁻¹ := by
  have he := congrArg (fun g : K⟦X⟧ => (g : K⸨X⸩)) (PowerSeries.inv_mul_cancel f hf)
  rw [PowerSeries.coe_mul, PowerSeries.coe_one] at he
  exact eq_inv_of_mul_eq_one_left he

/-- This is an actual regular Laurent expansion of the original rational differential. -/
theorem rational_infinity_series_representation {K : Type*} [Field K]
    (m : ℕ) (P D : K[X]) (hP : P.natDegree ≤ m) (hD : D.natDegree = m + 2)
    (hD0 : D ≠ 0) :
    ((-((P.reflect m : K⟦X⟧) * (D.reflect (m + 2) : K⟦X⟧)⁻¹) : K⟦X⟧) : K⸨X⸩) =
      algebraMap (RatFunc K) K⸨X⸩
        (-(algebraMap K[X] (RatFunc K) X)⁻¹ ^ 2 *
          P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹ /
          D.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) X)⁻¹) := by
  have hunit : PowerSeries.constantCoeff (D.reflect (m + 2) : K⟦X⟧) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, ← hD, ← Polynomial.reverse, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hD0
  rw [rational_infinity_density m P D hP hD hD0]
  simp only [map_neg, map_mul, map_inv₀, powerSeries_inverse_cast _ hunit,
    RatFunc.coe_coe, RatFunc.coePolynomial, div_eq_mul_inv]
  ring

end WPRationalInfinitySeries
