import WPNativeMomentIntegrality
import WPReview.NativeTruncation
import WPGammaArithmetic.Valuation

open scoped BigOperators

namespace WPNativeMomentIntegrality

theorem nativeCoefficient_ne_zero (n : ℕ) : WPReview.nativeCoefficient n ≠ 0 := by
  unfold WPReview.nativeCoefficient
  exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (mul_ne_zero
      (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))))
      (pow_ne_zero _ (by norm_num)))

private theorem small_unit (p n : ℕ) (hn : 0 < n) (hnp : n < p) :
    padicValRat p (n : ℚ) = 0 := by
  have hnd : ¬p ∣ n := by
    intro hd
    have hle := Nat.le_of_dvd hn hd
    omega
  simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Int.natCast_zero]

theorem native_normalizer_unit (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    padicValRat p (1728 : ℚ) = 0 := by
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    simpa using small_unit p 2 (by norm_num) (by omega)
  have hthree : padicValRat p (3 : ℚ) = 0 := by
    simpa using small_unit p 3 (by norm_num) (by omega)
  rw [show (1728 : ℚ) = 2 ^ 6 * 3 ^ 3 by norm_num,
    padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
    padicValRat.pow, htwo, hthree]
  ring

theorem native_coefficient_valuation_below_prime (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    padicValRat p (WPReview.nativeCoefficient n) =
      ((6 * n / p : ℕ) : ℤ) - ((3 * n / p : ℕ) : ℤ) := by
  have hprime : p.Prime := Fact.out
  have h6 : 6 * n < p ^ 2 := by nlinarith
  have h3 : 3 * n < p ^ 2 := by nlinarith
  have h1 : n < p ^ 2 := by nlinarith
  have hn0 : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3n0 : ((3 * n).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h6n0 : ((6 * n).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1728 : (1728 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold WPReview.nativeCoefficient
  rw [padicValRat.div h6n0 (mul_ne_zero (mul_ne_zero h3n0 (pow_ne_zero _ hn0)) h1728),
    padicValRat.mul (mul_ne_zero h3n0 (pow_ne_zero _ hn0)) h1728,
    padicValRat.mul h3n0 (pow_ne_zero _ hn0), padicValRat.pow, padicValRat.pow,
    native_normalizer_unit p hp, padicValRat.of_nat, padicValRat.of_nat,
    padicValRat.of_nat, WPGammaArithmetic.factorial_valuation_below_square p (6 * n) hprime h6,
    WPGammaArithmetic.factorial_valuation_below_square p (3 * n) hprime h3,
    WPGammaArithmetic.factorial_valuation_below_square p n hprime h1,
    Nat.div_eq_of_lt hn]
  ring

theorem native_high_tail_valuation (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (htail : p - 1 - p / 6 < n) :
    padicValRat p (WPReview.nativeCoefficient n) = 3 := by
  have h6low : 5 * p ≤ 6 * n := by omega
  have h3low : 2 * p ≤ 3 * n := by omega
  have h6 : 6 * n / p = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * n / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [native_coefficient_valuation_below_prime p n hp hn, h6, h3]
  norm_num

/-- The original cutoff e=p-1-floor(p/6), extended by zero through n=p-1. -/
def nativeShortCoefficient (p n : ℕ) : ℚ :=
  if n ≤ p - 1 - p / 6 then WPReview.nativeCoefficient n else 0

theorem native_full_short_coefficient_precision (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    WPReview.nativeCoefficient n = nativeShortCoefficient p n ∨
      (3 : ℤ) ≤ padicValRat p (WPReview.nativeCoefficient n - nativeShortCoefficient p n) := by
  by_cases hne : n ≤ p - 1 - p / 6
  · exact Or.inl (by simp [nativeShortCoefficient, hne])
  · exact Or.inr (by
      simp only [nativeShortCoefficient, if_neg hne, sub_zero]
      rw [native_high_tail_valuation p n hp hn (by omega)])

theorem native_full_short_moment_precision (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (L : ℕ → ℕ → ℤ) :
    (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * monomialMoment p n (L n)) =
      (∑ n ∈ Finset.range p, nativeShortCoefficient p n * monomialMoment p n (L n)) ∨
    (3 : ℤ) ≤ padicValRat p
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * monomialMoment p n (L n)) -
        (∑ n ∈ Finset.range p, nativeShortCoefficient p n * monomialMoment p n (L n))) := by
  exact finite_native_moment_preserves_precision p 3 hp L
    WPReview.nativeCoefficient (nativeShortCoefficient p)
    (fun n hn => native_full_short_coefficient_precision p n hp hn)

theorem native_short_moment_eq_literal_cutoff (p : ℕ) (hp : 7 ≤ p)
    (L : ℕ → ℕ → ℤ) :
    (∑ n ∈ Finset.range p, nativeShortCoefficient p n * monomialMoment p n (L n)) =
      ∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * monomialMoment p n (L n) := by
  have he : p - 1 - p / 6 + 1 ≤ p := by omega
  rw [← Finset.sum_range_add_sum_Ico
    (fun n => nativeShortCoefficient p n * monomialMoment p n (L n)) he]
  have hlow :
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        nativeShortCoefficient p n * monomialMoment p n (L n)) =
      ∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * monomialMoment p n (L n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [nativeShortCoefficient, if_pos (show n ≤ p - 1 - p / 6 by
      have := Finset.mem_range.mp hn
      omega)]
  have hhigh :
      (∑ n ∈ Finset.Ico (p - 1 - p / 6 + 1) p,
        nativeShortCoefficient p n * monomialMoment p n (L n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have ht := (Finset.mem_Ico.mp hn).1
    simp [nativeShortCoefficient, show ¬n ≤ p - 1 - p / 6 by omega]
  rw [hlow, hhigh, add_zero]

/-- The actual short cutoff e and full native cutoff preserve the third digit. -/
theorem native_full_literal_cutoff_moment_precision (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (L : ℕ → ℕ → ℤ) :
    (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * monomialMoment p n (L n)) =
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * monomialMoment p n (L n)) ∨
    (3 : ℤ) ≤ padicValRat p
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * monomialMoment p n (L n)) -
        (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
          WPReview.nativeCoefficient n * monomialMoment p n (L n))) := by
  have h := native_full_short_moment_precision p hp L
  rw [native_short_moment_eq_literal_cutoff p hp L] at h
  exact h

end WPNativeMomentIntegrality
