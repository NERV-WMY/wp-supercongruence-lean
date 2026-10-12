import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Ring

namespace WPReview

/-- The integer binomial product for the sixfold factorial coefficient. -/
def coefficientNat (n : ℕ) : ℕ :=
  (Nat.choose (2 * n) n) ^ 3 * Nat.choose (4 * n) (2 * n) *
    Nat.choose (6 * n) (2 * n)

/-- Multiplying the binomial product by the sixfold factorial denominator
recovers the literal numerator, including at `n = 0`. -/
theorem coefficient_factorial_identity (n : ℕ) :
    coefficientNat n * n.factorial ^ 6 = (6 * n).factorial := by
  have h2 := Nat.add_choose_mul_factorial_mul_factorial n n
  have h4 := Nat.add_choose_mul_factorial_mul_factorial (2 * n) (2 * n)
  have h6 := Nat.add_choose_mul_factorial_mul_factorial (4 * n) (2 * n)
  rw [show n + n = 2 * n by ring] at h2
  rw [show 2 * n + 2 * n = 4 * n by ring] at h4
  rw [show 4 * n + 2 * n = 6 * n by ring] at h6
  calc
    coefficientNat n * n.factorial ^ 6 =
        Nat.choose (6 * n) (2 * n) * Nat.choose (4 * n) (2 * n) *
          (Nat.choose (2 * n) n * n.factorial * n.factorial) ^ 3 := by
            unfold coefficientNat
            ring
    _ = Nat.choose (6 * n) (2 * n) * Nat.choose (4 * n) (2 * n) *
          (2 * n).factorial ^ 3 := by rw [h2]
    _ = Nat.choose (6 * n) (2 * n) *
          (Nat.choose (4 * n) (2 * n) * (2 * n).factorial * (2 * n).factorial) *
          (2 * n).factorial := by ring
    _ = Nat.choose (6 * n) (2 * n) * (4 * n).factorial * (2 * n).factorial := by
          rw [h4]
    _ = (6 * n).factorial := h6

/-- The integer binomial product is the exact rational factorial ratio. -/
theorem coefficient_eq_factorial_ratio (n : ℕ) :
    (coefficientNat n : ℚ) = ((6 * n).factorial : ℚ) / (n.factorial : ℚ) ^ 6 := by
  have hn : (n.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (eq_div_iff (pow_ne_zero 6 hn)).mpr
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    congrArg (fun k : ℕ => (k : ℚ)) (coefficient_factorial_identity n)

end WPReview
