import WPReview.Coefficient
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace WPReview

def weightNat (n : ℕ) : ℕ := 532 * n ^ 2 + 126 * n + 9

def literalTerm (n : ℕ) : ℚ :=
  ((6 * n).factorial : ℚ) / (n.factorial : ℚ) ^ 6 /
    (10 : ℚ) ^ (6 * n) * (weightNat n : ℚ)

def literalSum (p : ℕ) : ℚ := ∑ n ∈ Finset.range p, literalTerm n

def clearingDenominatorNat (p : ℕ) : ℕ := 10 ^ (6 * (p - 1))

def clearedSumNat (p : ℕ) : ℕ :=
  ∑ n ∈ Finset.range p,
    coefficientNat n * weightNat n * 10 ^ (6 * (p - 1 - n))

def clearedSum (p : ℕ) : ℤ := clearedSumNat p

def clearedDifference (p : ℕ) : ℤ :=
  clearedSum p - 9 * (p : ℤ) ^ 2 * (clearingDenominatorNat p : ℤ)

/-- The zero case is explicit because `padicValRat p 0` defaults to zero. -/
def RationalCongruent (p k : ℕ) (a b : ℚ) : Prop :=
  a = b ∨ (k : ℤ) ≤ padicValRat p (a - b)

theorem literal_term_eq_coefficient (n : ℕ) :
    literalTerm n = (coefficientNat n : ℚ) * (weightNat n : ℚ) /
      (10 : ℚ) ^ (6 * n) := by
  rw [literalTerm, ← coefficient_eq_factorial_ratio]
  ring

theorem clearing_denominator_ne_zero (p : ℕ) :
    (clearingDenominatorNat p : ℚ) ≠ 0 := by
  simp [clearingDenominatorNat]

theorem literal_sum_eq_cleared (p : ℕ) (hp : 0 < p) :
    literalSum p = (clearedSum p : ℚ) / (clearingDenominatorNat p : ℚ) := by
  simp only [literalSum, clearedSum, clearedSumNat]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : n < p := Finset.mem_range.mp hn
  have hexp : 6 * (p - 1) = 6 * n + 6 * (p - 1 - n) := by omega
  have hpow : (clearingDenominatorNat p : ℚ) =
      (10 : ℚ) ^ (6 * n) * (10 : ℚ) ^ (6 * (p - 1 - n)) := by
    simp [clearingDenominatorNat, hexp, pow_add]
  rw [literal_term_eq_coefficient, hpow]
  field_simp

theorem prime_not_dvd_ten (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ 10 := by
  intro h
  have hmul : p ∣ 2 * 5 := by simpa using h
  rcases hp.dvd_mul.mp hmul with h2 | h5
  · have := Nat.le_of_dvd (by decide : 0 < 2) h2
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 5) h5
    omega

theorem clearing_denominator_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ clearingDenominatorNat p := by
  intro h
  exact prime_not_dvd_ten p hp hp7 (hp.dvd_of_dvd_pow h)

theorem literal_difference_eq_cleared (p : ℕ) (hp : 0 < p) :
    literalSum p - 9 * (p : ℚ) ^ 2 =
      (clearedDifference p : ℚ) / (clearingDenominatorNat p : ℚ) := by
  rw [literal_sum_eq_cleared p hp]
  simp only [clearedDifference, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_natCast]
  field_simp [clearing_denominator_ne_zero p]

theorem literal_congruence_iff (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    RationalCongruent p 5 (literalSum p) (9 * (p : ℚ) ^ 2) ↔
      (p : ℤ) ^ 5 ∣ clearedDifference p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdiff := literal_difference_eq_cleared p hp.pos
  have hQ := clearing_denominator_ne_zero p
  have hvQ : padicValRat p (clearingDenominatorNat p : ℚ) = 0 := by
    simp only [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (clearing_denominator_unit p hp hp7), Nat.cast_zero]
  rw [RationalCongruent, ← sub_eq_zero, hdiff, div_eq_zero_iff, or_iff_left hQ,
    padicValInt_dvd_iff]
  by_cases hD : clearedDifference p = 0
  · simp [hD]
  · have hDr : (clearedDifference p : ℚ) ≠ 0 := by exact_mod_cast hD
    rw [padicValRat.div hDr hQ, hvQ, sub_zero, padicValRat.of_int]
    simp only [Int.cast_eq_zero, hD, false_or, Nat.cast_ofNat]
    exact_mod_cast (Iff.rfl : 5 ≤ padicValInt p (clearedDifference p) ↔
      5 ≤ padicValInt p (clearedDifference p))

end WPReview
