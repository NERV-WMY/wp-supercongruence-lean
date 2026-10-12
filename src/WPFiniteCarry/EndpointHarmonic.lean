import WPFiniteCarry.EvenLogLift
import Mathlib.Algebra.BigOperators.Intervals

open scoped Polynomial BigOperators
open Polynomial WPActualRankTwoHatLift WPActualEvenLogCarry

namespace WPFiniteCarry

set_option maxHeartbeats 800000

private theorem even_reciprocal_row (N : ℕ) :
    (∑ j ∈ Finset.Ico 1 (2 * N + 1), (1 + (-1 : ℚ) ^ j) / (j : ℚ)) =
      rationalHarmonic N := by
  induction N with
  | zero => simp [rationalHarmonic]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by omega,
      Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega),
      ih, rationalHarmonic_succ]
    have ho : (-1 : ℚ) ^ (2 * n + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    have he : (-1 : ℚ) ^ (2 * n + 1 + 1) = 1 := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, pow_mul]
      norm_num
    rw [ho, he]
    simp only [add_neg_cancel, zero_div, add_zero, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
    have hu : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp [hu]
    ring

private theorem rationalEvenLog_endpoint_odd (N : ℕ) :
    (rationalEvenLog (2 * N + 1)).eval 1 = rationalHarmonic N / 2 := by
  simp only [rationalEvenLog, eval_mul, eval_C, eval_add, eval_comp, eval_neg,
    eval_X, rationalLogPolynomial, eval_finsetSum, eval_pow, one_pow, mul_one]
  rw [← Finset.sum_add_distrib]
  have hf (j : ℕ) : 1 / (j : ℚ) + 1 / (j : ℚ) * (-1 : ℚ) ^ j =
      (1 + (-1 : ℚ) ^ j) / (j : ℚ) := by ring
  simp_rw [hf]
  rw [even_reciprocal_row]
  ring

/-- The literal characteristic-zero endpoint of the canonical even logarithm. -/
theorem rationalEvenLog_endpoint_harmonic (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rationalEvenLog p).eval 1 = rationalHarmonic ((p - 1) / 2) / 2 := by
  have h := rationalEvenLog_endpoint_odd ((p - 1) / 2)
  rw [prime_half_identity p hp] at h
  exact h

/-- The actual Q quotient keeps the original half-harmonic endpoint before reduction. -/
theorem actualEvenLogEndpointCarry_harmonic (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    actualEvenLogEndpointCarry p =
      (rationalHarmonic ((p - 1) / 2) / 2 +
        (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)) / (p : ℚ) := by
  rw [actualEvenLogEndpointCarry, rationalEvenLog_endpoint_harmonic p hp]

end WPFiniteCarry
