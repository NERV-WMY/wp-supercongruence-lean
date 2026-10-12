import WPTruncationArithmetic.Basic
import Mathlib.Tactic

namespace WPTruncationArithmetic

theorem factorial_valuation_zero (p : ℕ) : factorialValuation p 0 = 0 := by
  simp [factorialValuation]

theorem factorial_valuation_succ (p n : ℕ) (hp : p.Prime) :
    factorialValuation p (n + 1) =
      factorialValuation p n + padicValNat p (n + 1) := by
  let : Fact p.Prime := ⟨hp⟩
  unfold factorialValuation
  rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
  exact Nat.add_comm _ _

theorem factorial_valuation_recursion (p n : ℕ) (hp : p.Prime) :
    factorialValuation p n = n / p + factorialValuation p (n / p) := by
  let : Fact p.Prime := ⟨hp⟩
  unfold factorialValuation
  rw [← padicValNat_mul_div_factorial n, padicValNat_factorial_mul]
  exact Nat.add_comm _ _

theorem factorial_valuation_growth (p q : ℕ) (hp : p.Prime) (hq : 1 ≤ q) :
    (factorialValuation p q : ℚ) ≤ ((q : ℚ) - 1) / ((p : ℚ) - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hnat : (p - 1) * factorialValuation p q ≤ q - 1 := by
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : q ≠ 0)
    change (p - 1) * padicValNat p q.factorial ≤ q - 1
    omega
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  have hcast : ((p : ℚ) - 1) * (factorialValuation p q : ℚ) ≤ (q : ℚ) - 1 := by
    exact_mod_cast hnat
  have hpos : (0 : ℚ) < (p : ℚ) - 1 := by
    have h : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    linarith
  apply (le_div_iff₀ hpos).mpr
  nlinarith [hcast]

end WPTruncationArithmetic
