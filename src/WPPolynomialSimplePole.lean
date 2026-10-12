import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

open scoped Polynomial
open Polynomial

namespace WPPolynomialSimplePole

/-- Polynomial division supplies the actual pole and regular part, with its exact constant. -/
theorem simple_pole_decomposition {K : Type*} [Field K] (Z D : K[X]) (c : K)
    (h2 : (2 : K) ≠ 0) (hroot : D.eval c = 0) (hD : D.derivative.eval c ≠ 0) :
    ∃ U R : K[X], U.eval c = D.derivative.eval c ∧ U.eval c ≠ 0 ∧
      algebraMap K[X] (RatFunc K) Z / algebraMap K[X] (RatFunc K) D =
        RatFunc.C (Z.eval c / D.derivative.eval c) /
          algebraMap K[X] (RatFunc K) (X - C c) +
        algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) U ∧
      R.eval c / U.eval c =
        (Z.derivative.eval c - (Z.eval c / D.derivative.eval c) *
          D.derivative.derivative.eval c / 2) / D.derivative.eval c := by
  obtain ⟨U, hfactor⟩ := (dvd_iff_isRoot (p := D) (a := c)).mpr hroot
  have hu : U.eval c = D.derivative.eval c := by
    have he := congrArg (fun P : K[X] => P.derivative.eval c) hfactor
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero] at he
    exact he.symm
  have hu2 : 2 * U.derivative.eval c = D.derivative.derivative.eval c := by
    have he := congrArg (fun P : K[X] => P.derivative.derivative.eval c) hfactor
    simp only [derivative_mul, derivative_add, derivative_sub, derivative_X,
      derivative_C, sub_zero, one_mul, zero_mul,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero] at he
    linear_combination -he
  let a := Z.eval c / D.derivative.eval c
  have hrem : (Z - C a * U).eval c = 0 := by
    rw [eval_sub, eval_mul, eval_C, hu]
    dsimp [a]
    field_simp
    ring
  obtain ⟨R, hR⟩ := (dvd_iff_isRoot (p := Z - C a * U) (a := c)).mpr hrem
  have hr : R.eval c = Z.derivative.eval c - a * U.derivative.eval c := by
    have he := congrArg (fun P : K[X] => P.derivative.eval c) hR
    simp only [derivative_sub, derivative_mul, derivative_C, derivative_X,
      sub_zero, one_mul, zero_mul, zero_add, eval_sub, eval_add, eval_mul,
      eval_C, eval_X, sub_self, zero_mul, add_zero] at he
    exact he.symm
  have hU : U ≠ 0 := by intro hz; rw [hz, eval_zero] at hu; exact hD hu.symm
  have hX : (X - C c : K[X]) ≠ 0 := sub_ne_zero.mpr (X_ne_C c)
  refine ⟨U, R, hu, (by rw [hu]; exact hD), ?_, ?_⟩
  · have hz : Z = C a * U + (X - C c) * R := by linear_combination hR
    change algebraMap K[X] (RatFunc K) Z / algebraMap K[X] (RatFunc K) D =
      RatFunc.C a / algebraMap K[X] (RatFunc K) (X - C c) +
        algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) U
    rw [hz, hfactor]
    simp only [map_add, map_mul, RatFunc.algebraMap_C]
    change (RatFunc.C a * algebraMap K[X] (RatFunc K) U +
        algebraMap K[X] (RatFunc K) (X - C c) * algebraMap K[X] (RatFunc K) R) /
        (algebraMap K[X] (RatFunc K) (X - C c) * algebraMap K[X] (RatFunc K) U) = _
    field_simp [RatFunc.algebraMap_ne_zero hU, RatFunc.algebraMap_ne_zero hX]
    rw [add_div, mul_div_cancel_left₀ _ (RatFunc.algebraMap_ne_zero hX)]
  · rw [hr, hu]
    have hue : U.derivative.eval c = D.derivative.derivative.eval c / 2 := by
      apply (eq_div_iff h2).mpr
      linear_combination hu2
    rw [hue]
    dsimp [a]
    ring

end WPPolynomialSimplePole
