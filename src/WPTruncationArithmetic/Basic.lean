import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace WPTruncationArithmetic

/-- The actual valuation of a nonzero natural factorial. -/
def factorialValuation (p n : ℕ) : ℕ := padicValNat p n.factorial

/-- The integer arithmetic lower bound before adding the coefficient valuation. -/
def poleCutoff (p j : ℕ) : ℤ :=
  -(j : ℤ) - (factorialValuation p j : ℤ) + ((j / 5 : ℕ) : ℤ) - 1

/-- The integer bound at the largest allowed pole. -/
def truncationDigits (p q : ℕ) : ℤ :=
  ((q / 5 : ℕ) : ℤ) - 1 - (factorialValuation p q : ℤ)

end WPTruncationArithmetic
