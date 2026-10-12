import WPReview.FiniteStokes
import Mathlib.Algebra.Polynomial.Derivative

open scoped BigOperators
open Polynomial

namespace WPFiniteGammaIntegral

/-- Finite polynomial antiderivative evaluation at the endpoints 0 and 1. -/
noncomputable def integralZeroOne : ℚ[X] →ₗ[ℚ] ℚ where
  toFun P := P.sum (fun n a => a / ((n : ℚ) + 1))
  map_add' P Q := by
    apply sum_add_index
    · intro n; simp
    · intro n a b; exact add_div _ _ _
  map_smul' a P := by
    rw [sum_smul_index P a _ (by intro n; simp)]
    simp only [smul_eq_mul, RingHom.id_apply]
    simp only [Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring

theorem integral_monomial (n : ℕ) (a : ℚ) :
    integralZeroOne (monomial n a) = a / ((n : ℚ) + 1) := by
  simp [integralZeroOne]

theorem integral_C (a : ℚ) : integralZeroOne (C a) = a := by
  simp [integralZeroOne]

theorem integral_C_mul (a : ℚ) (P : ℚ[X]) :
    integralZeroOne (C a * P) = a * integralZeroOne P := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

/-- The polynomial endpoint theorem, proved from individual monomials. -/
theorem integral_derivative (P : ℚ[X]) :
    integralZeroOne (derivative P) = P.eval 1 - P.eval 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [derivative_add, map_add, hP, hQ, eval_add, eval_add]
    ring
  | monomial n a =>
    cases n with
    | zero => simp [integralZeroOne]
    | succ n =>
      rw [derivative_monomial_succ, integral_monomial]
      have hn : (n : ℚ) + 1 ≠ 0 := by positivity
      simp only [eval_monomial, one_pow, mul_one, pow_succ, mul_zero, sub_zero]
      field_simp

/-- The quadratic substitution used by the finite conductor Gamma functional. -/
noncomputable def quadraticArgument : ℚ[X] := 1 - X ^ 2

theorem quadratic_integral_zero : integralZeroOne (quadraticArgument ^ 0) = 1 := by
  simpa using integral_C (1 : ℚ)

theorem quadratic_derivative_identity (k : ℕ) :
    derivative (X * quadraticArgument ^ (k + 1)) =
      (2 * (k : ℚ) + 3) • quadraticArgument ^ (k + 1) -
        (2 * (k : ℚ) + 2) • quadraticArgument ^ k := by
  rw [derivative_mul, derivative_X, derivative_pow_succ]
  simp only [quadraticArgument, derivative_sub, derivative_one, derivative_X_sq,
    zero_sub, one_mul, smul_eq_C_mul, C_add, C_mul, C_1, C_ofNat, C_eq_natCast]
  rw [pow_succ]
  ring

/-- Exact integration by parts, retaining both polynomial endpoint evaluations. -/
theorem quadratic_integral_recurrence (k : ℕ) :
    (2 * (k : ℚ) + 3) * integralZeroOne (quadraticArgument ^ (k + 1)) =
      (2 * (k : ℚ) + 2) * integralZeroOne (quadraticArgument ^ k) := by
  have h := integral_derivative (X * quadraticArgument ^ (k + 1))
  rw [quadratic_derivative_identity, map_sub, map_smul, map_smul] at h
  simp [quadraticArgument] at h
  exact sub_eq_zero.mp h

theorem quadratic_integral_eq_gamma (k : ℕ) :
    integralZeroOne (quadraticArgument ^ k) = WPReview.gamma k := by
  induction k with
  | zero => rw [quadratic_integral_zero, WPReview.gamma_zero]
  | succ k ih =>
    have hr := quadratic_integral_recurrence k
    rw [ih] at hr
    have hg := WPReview.gamma_adjacent_recurrence k
    apply mul_left_cancel₀ (show 2 * (k : ℚ) + 3 ≠ 0 by positivity)
    linear_combination hr + 2 * hg

/-- The full exact Gamma functional for an arbitrary finite rational polynomial. -/
theorem integral_comp_quadratic (P : ℚ[X]) :
    integralZeroOne (P.comp quadraticArgument) =
      P.sum (fun k a => WPReview.gamma k * a) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [add_comp, map_add, hP, hQ, sum_add_index P Q]
    · intro k; simp
    · intro k a b; exact mul_add _ _ _
  | monomial k a =>
    rw [monomial_comp, integral_C_mul, quadratic_integral_eq_gamma]
    simp [mul_comm]

/-- The degree bound identifies the full polynomial functional with the stated finite cutoff. -/
theorem Gamma_eq_integral (P : ℚ[X]) (L : ℕ) (hL : P.natDegree ≤ L) :
    WPReview.Gamma L (fun k => P.coeff k) =
      integralZeroOne (P.comp quadraticArgument) := by
  classical
  rw [integral_comp_quadratic]
  have hsupport : P.support ⊆ Finset.range (L + 1) := by
    intro k hk
    have hk0 : P.coeff k ≠ 0 := mem_support_iff.mp hk
    have hkdeg : k ≤ P.natDegree := le_natDegree_of_ne_zero hk0
    exact Finset.mem_range.mpr (by omega)
  rw [sum_eq_of_subset (fun k a => WPReview.gamma k * a) (by intro k; simp) hsupport]
  rfl

end WPFiniteGammaIntegral
