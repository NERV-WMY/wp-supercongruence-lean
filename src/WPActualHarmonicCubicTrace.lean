import WPActualNativeCubicInvariant
import Mathlib.Algebra.QuadraticAlgebra.Basic

open scoped BigOperators QuadraticAlgebra

namespace WPActualHarmonicCubicTrace

abbrev CubicIntegers := QuadraticAlgebra ℤ (-1) (-1)

def cubicOmega : CubicIntegers := QuadraticAlgebra.omega

def cubicTrace : CubicIntegers →ₗ[ℤ] ℤ := QuadraticAlgebra.trace

theorem cubicOmega_cube : cubicOmega ^ 3 = 1 := by
  ext <;> norm_num [CubicIntegers, cubicOmega, QuadraticAlgebra.omega, pow_succ]

theorem cubicOmega_minus_square : (1 - cubicOmega) ^ 2 = -3 * cubicOmega := by
  ext <;> norm_num [CubicIntegers, cubicOmega, QuadraticAlgebra.omega, pow_succ]

theorem cubicOmega_plus : 1 + cubicOmega = -cubicOmega ^ 2 := by
  ext <;> norm_num [CubicIntegers, cubicOmega, QuadraticAlgebra.omega, pow_succ]

theorem cubicOmega_power_mod (n : ℕ) : cubicOmega ^ n = cubicOmega ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, cubicOmega_cube, one_pow, mul_one]

theorem cubicTrace_integer_mul (n : ℤ) (z : CubicIntegers) :
    cubicTrace ((n : CubicIntegers) * z) = n * cubicTrace z := by
  simp [cubicTrace, QuadraticAlgebra.trace_def]
  ring

theorem cubicTrace_omega_power (n : ℕ) :
    cubicTrace (cubicOmega ^ n) = if 3 ∣ n then 2 else -1 := by
  rw [cubicOmega_power_mod]
  simp only [Nat.dvd_iff_mod_eq_zero]
  have hn := Nat.mod_lt n (by omega : 0 < 3)
  generalize hm : n % 3 = m at *
  interval_cases m <;> norm_num [CubicIntegers, cubicTrace, QuadraticAlgebra.trace_def,
    cubicOmega, QuadraticAlgebra.omega, pow_succ]

theorem cubicTrace_plus_prime (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicTrace ((1 + cubicOmega) ^ p) = 1 := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h3 : ¬3 ∣ 2 * p := by
    intro hd
    have he := Nat.Prime.dvd_mul Nat.prime_three |>.mp hd
    rcases he with h | h
    · have := Nat.le_of_dvd (by omega : 0 < 2) h; omega
    · rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h with h | h <;> omega
  rw [cubicOmega_plus, neg_pow, hodd.neg_one_pow, ← pow_mul,
    show 2 * p = p * 2 by omega, show (-1 : CubicIntegers) * cubicOmega ^ (p * 2) =
      (-1 : ℤ) • (cubicOmega ^ (p * 2)) by simp]
  rw [map_smul]
  simp only [smul_eq_mul, cubicTrace_omega_power, show ¬3 ∣ p * 2 by omega, ite_false]
  norm_num

theorem cubicTrace_minus_prime_square (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicTrace ((1 - cubicOmega) ^ p) ^ 2 = 9 * (3 : ℤ) ^ (p - 1) := by
  let N := (p - 1) / 2
  have hn := WPActualHasseReciprocal.actual_half_exponent p hp
  have he : (1 - cubicOmega) ^ p = ((-3 : CubicIntegers) ^ N) *
      (cubicOmega ^ N * (1 - cubicOmega)) := by
    rw [show p = 2 * N + 1 by dsimp [N]; omega, pow_succ, pow_mul,
      cubicOmega_minus_square, mul_pow]
    ring
  have hnmod : N % 3 = 0 ∨ N % 3 = 2 := by
    rcases WPActualNativeParameter.prime_six_classes p hp with h | h <;> dsimp [N] <;> omega
  have ht : (cubicTrace (cubicOmega ^ N * (1 - cubicOmega))) ^ 2 = 9 := by
    rw [cubicOmega_power_mod]
    rcases hnmod with h | h <;> rw [h] <;>
      norm_num [CubicIntegers, cubicTrace, QuadraticAlgebra.trace_def,
        cubicOmega, QuadraticAlgebra.omega, pow_succ]
  have hcast : (-3 : CubicIntegers) ^ N = (((-3 : ℤ) ^ N : ℤ) : CubicIntegers) := by
    push_cast
    rfl
  rw [he, hcast, cubicTrace_integer_mul, mul_pow, ht]
  have hpN : 2 * N = p - 1 := by dsimp [N]; omega
  rw [← pow_mul, Nat.mul_comm N 2, pow_mul]
  norm_num only [show (-3 : ℤ) ^ 2 = 9 by norm_num]
  rw [show (9 : ℤ) = 3 ^ 2 by norm_num, ← pow_mul, hpN]
  ring

/-- The original integral cube filter, before division by p or reduction to the field. -/
theorem cubicTrace_binomial (p : ℕ) (s : ℤ) :
    cubicTrace ((1 + (s : CubicIntegers) * cubicOmega) ^ p) =
      3 * (∑ j ∈ Finset.range (p + 1),
        if 3 ∣ j then (Nat.choose p j : ℤ) * s ^ j else 0) - (1 + s) ^ p := by
  rw [show 1 + (s : CubicIntegers) * cubicOmega =
    (s : CubicIntegers) * cubicOmega + 1 by ring, add_pow, map_sum]
  rw [show (1 + s) ^ p = (s + 1) ^ p by congr 1; ring, add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have he : ((s : CubicIntegers) * cubicOmega) ^ j * (Nat.choose p j : CubicIntegers) =
      (((Nat.choose p j : ℤ) * s ^ j : ℤ) : CubicIntegers) * cubicOmega ^ j := by
    push_cast
    ring
  rw [he, cubicTrace_integer_mul, cubicTrace_omega_power]
  split_ifs <;> ring

def cubicQuotientSum (p : ℕ) (s : ℤ) : ℤ :=
  ∑ j ∈ Finset.Ico 1 p, if 3 ∣ j then
    ((Nat.choose p j : ℤ) / (p : ℤ)) * s ^ j else 0

theorem cubicTrace_quotient (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (s : ℤ) :
    cubicTrace ((1 + (s : CubicIntegers) * cubicOmega) ^ p) =
      3 + 3 * (p : ℤ) * cubicQuotientSum p s - (1 + s) ^ p := by
  have hprime : p.Prime := Fact.out
  have h3 : ¬3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hprime).mp h with h | h <;> omega
  have hr : (∑ j ∈ Finset.range (p + 1),
      if 3 ∣ j then (Nat.choose p j : ℤ) * s ^ j else 0) =
      1 + ∑ j ∈ Finset.Ico 1 p, if 3 ∣ j then (Nat.choose p j : ℤ) * s ^ j else 0 := by
    rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ hprime.one_le]
    simp only [Finset.sum_range_one, dvd_zero, ite_true, Nat.choose_zero_right,
      Nat.cast_one, pow_zero, mul_one, h3, ite_false, add_zero]
  have hs : (∑ j ∈ Finset.Ico 1 p, if 3 ∣ j then (Nat.choose p j : ℤ) * s ^ j else 0) =
      (p : ℤ) * cubicQuotientSum p s := by
    rw [cubicQuotientSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h3j : 3 ∣ j
    · simp only [h3j, ite_true]
      have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
        have hj' := Finset.mem_Ico.mp hj
        exact_mod_cast hprime.dvd_choose_self (by omega : j ≠ 0) hj'.2
      rw [← mul_assoc, Int.mul_ediv_cancel' hd]
    · simp [h3j]
  rw [cubicTrace_binomial, hr, hs]
  ring

theorem cubicQuotientSum_minus_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicTrace ((1 - cubicOmega) ^ p) - 3 = 3 * (p : ℤ) * cubicQuotientSum p (-1) := by
  have he := cubicTrace_quotient p hp (-1)
  norm_num only [Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg,
    add_neg_cancel, zero_pow (by omega : p ≠ 0)] at he
  linear_combination he

theorem cubicQuotientSum_plus_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (2 : ℤ) ^ p - 2 = 3 * (p : ℤ) * cubicQuotientSum p 1 := by
  have he := cubicTrace_quotient p hp 1
  rw [Int.cast_one, one_mul, cubicTrace_plus_prime p hp] at he
  norm_num only [show (1 + 1 : ℤ) = 2 by norm_num] at he
  linear_combination he

end WPActualHarmonicCubicTrace
