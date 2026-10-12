import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

namespace WPSupercongruenceStatement

def W (p : Nat) : Rat :=
  Finset.sum (Finset.range p) (fun n =>
    ((Nat.factorial (6 * n) : Rat) / (Nat.factorial n : Rat)^6) /
      (10 : Rat)^(6 * n) * (532 * (n : Rat)^2 + 126 * (n : Rat) + 9))

def Congruent (p : Nat) (a b : Rat) : Prop :=
  a = b ∨ (5 : Int) ≤ padicValRat p (a - b)

def Challenge : Prop :=
  ∀ p : Nat, Nat.Prime p → 7 ≤ p → Congruent p (W p) (9 * (p : Rat)^2)

end WPSupercongruenceStatement
