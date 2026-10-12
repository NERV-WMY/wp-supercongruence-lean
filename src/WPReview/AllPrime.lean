import WPFieldAssembly.ScalarFinalSuccessorAllPrime

namespace WPReview

/- Parent integration of the original full target. The actual terminal assembly
and its native producer must complete FIVE before this module is checked.
Verification and review status are recorded in the scalar successor recovery. -/

/-- The original full weighted sum has value 9p^2 modulo p^5 for every prime p >= 7. -/
theorem literal_all_primes (p : ℕ) (hprime : p.Prime) (hp : 7 ≤ p) :
    RationalCongruent p 5 (literalSum p) (9 * (p : ℚ)^2) := by
  let : Fact p.Prime := ⟨hprime⟩
  exact WPFieldAssembly.ScalarFinalSuccessorAllPrime.all_primes_literal_congruence p hp

end WPReview
