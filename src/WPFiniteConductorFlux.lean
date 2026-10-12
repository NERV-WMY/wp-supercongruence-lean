import WPFiniteConductorPolynomial
import WPFiniteConductorReflection

open scoped BigOperators
open Polynomial
open WPFiniteConductorReflection

namespace WPFiniteConductorPolynomial

def Ucoordinate (r : ℚ) : ℚ := (4 * r ^ 2 - 1) / (3 * r)
def xCoordinate (r : ℚ) : ℚ := 1 - Ucoordinate r ^ 2
def Uderivative (r : ℚ) : ℚ := (4 * r ^ 2 + 1) / (3 * r ^ 2)

theorem source_root_product (r : ℚ) (hr : r ≠ 0) :
    lam.eval (xCoordinate r) = q1 r * q2 r := by
  norm_num [lam, xCoordinate, Ucoordinate, q1, q2]
  field_simp [hr]; ring

theorem source_root_sum (r : ℚ) (hr : r ≠ 0) :
    2 * m.eval (xCoordinate r) = q1 r + q2 r := by
  norm_num [m, xCoordinate, Ucoordinate, q1, q2]
  field_simp [hr]; ring

/-- The first original canceled coefficient, with both root source channels. -/
theorem original_flux_base_two (r : ℚ) (hr : r ≠ 0) :
    2 * lam.eval (xCoordinate r) * Q2.eval (xCoordinate r) * Uderivative r =
      firstWeight r * q2 r ^ 4 + secondWeight r * q1 r ^ 4 := by
  norm_num [lam, Q2, xCoordinate, Ucoordinate, Uderivative,
    firstWeight, secondWeight, q1, q2]
  field_simp [hr]; ring

/-- The next original canceled coefficient retains both distinct roots as well. -/
theorem original_flux_base_three (r : ℚ) (hr : r ≠ 0) :
    2 * lam.eval (xCoordinate r) * Q3.eval (xCoordinate r) * Uderivative r =
      firstWeight r * q2 r ^ 5 + secondWeight r * q1 r ^ 5 := by
  norm_num [lam, Q3, xCoordinate, Ucoordinate, Uderivative,
    firstWeight, secondWeight, q1, q2]
  field_simp [hr]; ring

/-- Uniform attachment of the ORIGINAL conductor recurrence to its two actual fluxes. -/
theorem canceledKernel_two_fluxes (k : ℕ) (r : ℚ) (hr : r ≠ 0) :
    2 * lam.eval (xCoordinate r) * (canceledKernel k).eval (xCoordinate r) *
        Uderivative r =
      firstWeight r * q2 r ^ (k + 4) + secondWeight r * q1 r ^ (k + 4) := by
  induction k using Nat.twoStepInduction with
  | zero => exact original_flux_base_two r hr
  | one => exact original_flux_base_three r hr
  | more k hk hk1 =>
    rw [canceledKernel]
    simp only [eval_sub, eval_mul, eval_ofNat]
    calc
      2 * lam.eval (xCoordinate r) *
            (2 * m.eval (xCoordinate r) * (canceledKernel (k + 1)).eval (xCoordinate r) -
              lam.eval (xCoordinate r) * (canceledKernel k).eval (xCoordinate r)) *
          Uderivative r =
        (2 * m.eval (xCoordinate r)) *
          (2 * lam.eval (xCoordinate r) * (canceledKernel (k + 1)).eval (xCoordinate r) *
            Uderivative r) -
        lam.eval (xCoordinate r) *
          (2 * lam.eval (xCoordinate r) * (canceledKernel k).eval (xCoordinate r) *
            Uderivative r) := by ring
      _ = _ := by
        rw [hk, hk1, source_root_product r hr, source_root_sum r hr]
        simp only [pow_succ]
        ring

/-- The polynomial defined by original coefficient extraction gives BOTH full finite fluxes. -/
theorem Be_actual_two_flux_density (p e : ℕ) (he : e + 4 ≤ p) (r : ℚ)
    (hr : r ≠ 0) :
    (Be p e).eval (xCoordinate r) * Uderivative r =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n *
        (firstFlux p n r + secondFlux p n r) := by
  classical
  unfold Be
  rw [eval_finsetSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ e := by have := Finset.mem_range.mp hn; omega
  have hp : p = (p - 4 - n + 4) + n := by omega
  simp only [eval_mul, eval_C, eval_pow]
  calc
    (2 * WPReview.nativeCoefficient n * lam.eval (xCoordinate r) ^ (n + 1) *
          (canceledKernel (p - 4 - n)).eval (xCoordinate r)) * Uderivative r =
      WPReview.nativeCoefficient n * lam.eval (xCoordinate r) ^ n *
        (2 * lam.eval (xCoordinate r) * (canceledKernel (p - 4 - n)).eval (xCoordinate r) *
          Uderivative r) := by rw [pow_succ]; ring
    _ = _ := by
      rw [canceledKernel_two_fluxes _ r hr, source_root_product r hr]
      unfold firstFlux secondFlux
      conv_rhs => rw [hp]
      simp only [pow_add, mul_pow]
      ring

end WPFiniteConductorPolynomial
