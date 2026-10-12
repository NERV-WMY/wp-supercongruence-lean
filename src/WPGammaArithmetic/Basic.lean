import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace WPGammaArithmetic

/-- The literal finite outer factorial weight. -/
def gamma (k : ℕ) : ℚ :=
  (4 : ℚ) ^ k * (k.factorial : ℚ) ^ 2 / ((2 * k + 1).factorial : ℚ)

/-- Zero differences are explicit because the valuation of zero defaults to zero. -/
def RationalCongruent (p m : ℕ) (a b : ℚ) : Prop :=
  a = b ∨ (m : ℤ) ≤ padicValRat p (a - b)

def gammaMoment (L : ℕ) (a : ℕ → ℚ) : ℚ :=
  ∑ k ∈ Finset.range (L + 1), gamma k * a k

theorem gamma_definition_agrees (k : ℕ) :
    gamma k =
      (4 : ℚ) ^ k * (k.factorial : ℚ) ^ 2 / ((2 * k + 1).factorial : ℚ) := rfl

end WPGammaArithmetic
