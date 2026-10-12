import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace WPReview

/-- The actual rational factorial weight of the finite outer functional. -/
def gamma (k : ℕ) : ℚ :=
  (4 : ℚ) ^ k * (k.factorial : ℚ) ^ 2 / ((2 * k + 1).factorial : ℚ)

/-- Inclusive finite cutoff, with no restriction on the coefficient sequence. -/
def Gamma (L : ℕ) (a : ℕ → ℚ) : ℚ :=
  ∑ k ∈ Finset.range (L + 1), gamma k * a k

/-- The coefficient sequence of `(1-x) T' - T/2`. -/
def beta (t : ℕ → ℚ) (k : ℕ) : ℚ :=
  ((k : ℚ) + 1) * t (k + 1) - ((k : ℚ) + 1 / 2) * t k

theorem rational_factorial_ne_zero (n : ℕ) :
    (n.factorial : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

theorem gamma_zero : gamma 0 = 1 := by
  norm_num [gamma]

/-- The adjacent recurrence follows from the factorial definition itself. -/
theorem gamma_adjacent_recurrence (k : ℕ) :
    ((k : ℚ) + 1) * gamma k = ((k : ℚ) + 3 / 2) * gamma (k + 1) := by
  have hnum : ((k + 1).factorial : ℚ) =
      ((k : ℚ) + 1) * (k.factorial : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_succ k)
  have hden : ((2 * (k + 1) + 1).factorial : ℚ) =
      (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) *
        ((2 * k + 1).factorial : ℚ) := by
    rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hbase := rational_factorial_ne_zero (2 * k + 1)
  have htwo : 2 * (k : ℚ) + 2 ≠ 0 := by positivity
  have hthree : 2 * (k : ℚ) + 3 ≠ 0 := by positivity
  unfold gamma
  rw [hnum, hden, pow_succ]
  field_simp [hbase, htwo, hthree]; ring

/-- Multiplication by the odd factor gives the literal half-parameter weight. -/
theorem gamma_factorial_identity (k : ℕ) :
    (2 * (k : ℚ) + 1) * gamma k =
      (4 : ℚ) ^ k * (k.factorial : ℚ) ^ 2 / ((2 * k).factorial : ℚ) := by
  have hden : ((2 * k + 1).factorial : ℚ) =
      (2 * (k : ℚ) + 1) * ((2 * k).factorial : ℚ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one]
  have hbase := rational_factorial_ne_zero (2 * k)
  have hodd : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
  rw [gamma, hden]
  field_simp [hbase, hodd]

theorem Gamma_succ (L : ℕ) (a : ℕ → ℚ) :
    Gamma (L + 1) a = Gamma L a + gamma (L + 1) * a (L + 1) := by
  simp only [Gamma, Finset.sum_range_succ]

/-- At cutoff zero both the lower and upper coefficients are present. -/
theorem finite_stokes_zero (t : ℕ → ℚ) :
    Gamma 0 (beta t) = -t 0 / 2 + gamma 0 * t 1 := by
  norm_num [Gamma, beta, gamma]; ring

/-- Finite Stokes for every rational sequence, retaining its upper endpoint. -/
theorem finite_stokes (L : ℕ) (t : ℕ → ℚ) :
    Gamma L (beta t) =
      -t 0 / 2 + ((L : ℚ) + 1) * gamma L * t (L + 1) := by
  induction L with
  | zero =>
      simpa only [Nat.cast_zero, zero_add, one_mul] using
        finite_stokes_zero t
  | succ L ih =>
      rw [Gamma_succ, ih]
      simp only [beta, Nat.cast_succ]
      linear_combination t (L + 1) * gamma_adjacent_recurrence L

end WPReview
