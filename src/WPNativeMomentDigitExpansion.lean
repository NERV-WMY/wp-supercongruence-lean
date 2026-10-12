import WPActualNativeMoment
import WPReview.LaurentPrecision
import WPGammaArithmetic.Precision
import Mathlib.Algebra.Ring.Int.Parity

open scoped BigOperators

namespace WPNativeMomentIntegrality

/-- Multiplication by an integral scalar retains the stated finite precision. -/
theorem precision_mul_integral (p k : ℕ) [Fact p.Prime] (c a b : ℚ)
    (hc : 0 ≤ padicValRat p c) (hab : WPReview.RationalCongruent p k a b) :
    WPReview.RationalCongruent p k (c * a) (c * b) := by
  rcases hab with hab | hab
  · exact Or.inl (congrArg (fun z : ℚ => c * z) hab)
  by_cases hc0 : c = 0
  · exact Or.inl (by simp [hc0])
  by_cases hab0 : a = b
  · exact Or.inl (congrArg (fun z : ℚ => c * z) hab0)
  apply Or.inr
  rw [← mul_sub, padicValRat.mul hc0 (sub_ne_zero.mpr hab0)]
  omega

theorem two_zpow_unit (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (m : ℤ) :
    padicValRat p ((2 : ℚ) ^ m) = 0 := by
  have hd : ¬p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
    rfl
  rw [padicValRat.zpow, htwo, mul_zero]

/-- The four-power kernel has the original two endpoints after its exact unit factor. -/
theorem primitive_weight_four_kernel (p : ℕ) (m : ℤ) :
    primitiveWeight p m =
      (2 : ℚ) ^ m * ((p : ℚ) * (1 - (4 : ℚ) ^ (-m)) / (m : ℚ)) := by
  have h := WPFiniteConductorReflection.reciprocal_weight_product m
  unfold primitiveWeight
  linear_combination (p : ℚ) / (m : ℚ) * h

theorem primitive_denominator_native_interval (p n a : ℕ) (_hp : 7 ≤ p)
    (hn : n ≤ p - 1 - p / 6) (ha : a < 3 * (p + n)) :
    Odd (primitiveDenominator n a) ∧
      -6 * ((5 * p / 6 : ℕ) : ℤ) - 1 ≤ primitiveDenominator n a ∧
      primitiveDenominator n a ≤ 6 * (p : ℤ) - 1 := by
  have he : p - 1 - p / 6 ≤ 5 * p / 6 := by omega
  refine ⟨⟨(a : ℤ) - 3 * (n : ℤ), ?_⟩, ?_, ?_⟩
  · unfold primitiveDenominator
    ring
  · unfold primitiveDenominator
    omega
  · unfold primitiveDenominator
    omega

theorem primitive_resonant_multiplier (p n a : ℕ) (b : ℤ) (hp : 7 ≤ p)
    (hn : n < p) (ha : a < 3 * (p + n))
    (hsplit : primitiveDenominator n a = (b : ℤ) * (p : ℤ)) :
    WPLaurent.AllowedMultiplier (b : ℤ) := by
  have hodd : Odd ((b : ℤ) * (p : ℤ)) := by
    rw [← hsplit]
    refine ⟨(a : ℤ) - 3 * (n : ℤ), ?_⟩
    unfold primitiveDenominator
    ring
  have hbodd : Odd b := (Int.odd_mul.mp hodd).1
  obtain ⟨k, hk⟩ := hbodd
  have hlo : -(6 * (p : ℤ)) < primitiveDenominator n a := by
    unfold primitiveDenominator
    omega
  have hhi : primitiveDenominator n a < 6 * (p : ℤ) := by
    unfold primitiveDenominator
    omega
  have hpz : 0 < (p : ℤ) := by omega
  rw [hsplit] at hlo hhi
  have hb : (b : ℤ) < 6 := by nlinarith
  have hblow : -6 < b := by nlinarith
  unfold WPLaurent.AllowedMultiplier
  omega

/-- Exact integer quotient and remainder select the actual primitive's kernel. -/
def primitiveDigitExpansion (p : ℕ) (m : ℤ) : ℚ :=
  if m % (p : ℤ) = 0 then
    (2 : ℚ) ^ m * WPLaurent.resonantExpansion p (m / (p : ℤ))
  else
    (2 : ℚ) ^ m *
      WPLaurent.nonresonantExpansion p m (m / (p : ℤ)) (m % (p : ℤ))

theorem native_primitive_nonresonant_digits (p n a : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n ≤ p - 1 - p / 6) (ha : a < 3 * (p + n))
    (hr : primitiveDenominator n a % (p : ℤ) ≠ 0) :
    WPReview.RationalCongruent p 3
      (primitiveWeight p (primitiveDenominator n a))
      (primitiveDigitExpansion p (primitiveDenominator n a)) := by
  have hprime : p.Prime := Fact.out
  let m := primitiveDenominator n a
  have hm : m = m / (p : ℤ) * (p : ℤ) + m % (p : ℤ) := by
    simpa only [mul_comm] using (Int.mul_ediv_add_emod m (p : ℤ)).symm
  have hpz : 0 < (p : ℤ) := by omega
  have hr1 : 1 ≤ m % (p : ℤ) := by
    have hr' : m % (p : ℤ) ≠ 0 := hr
    have hnonneg := Int.emod_nonneg m (show (p : ℤ) ≠ 0 by omega)
    omega
  have hrp : m % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos m hpz
  obtain ⟨hodd, hlo, hhi⟩ := primitive_denominator_native_interval p n a hp hn ha
  have h := WPReview.nonresonant_laurent_kernel p hprime hp m
    (m / (p : ℤ)) (m % (p : ℤ)) hm hr1 hrp hodd hlo hhi
  have hmul := precision_mul_integral p 3 ((2 : ℚ) ^ m) _ _
    (by rw [two_zpow_unit p hp m]) h
  rw [← primitive_weight_four_kernel] at hmul
  simpa only [primitiveDigitExpansion, if_neg hr,
    WPLaurent.nonresonantExpansion, WPReview.fermatQuotientFour,
    WPLaurent.fermatQuotient4] using hmul

theorem native_primitive_resonant_digits (p n a : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n ≤ p - 1 - p / 6) (ha : a < 3 * (p + n))
    (hr : primitiveDenominator n a % (p : ℤ) = 0) :
    WPReview.RationalCongruent p 3
      (primitiveWeight p (primitiveDenominator n a))
      (primitiveDigitExpansion p (primitiveDenominator n a)) := by
  have hprime : p.Prime := Fact.out
  let m := primitiveDenominator n a
  let b := m / (p : ℤ)
  have hm : m = b * (p : ℤ) := by
    have he := Int.mul_ediv_add_emod m (p : ℤ)
    have hr' : m % (p : ℤ) = 0 := hr
    simpa only [hr', add_zero, mul_comm] using he.symm
  have hnfull : n < p := by omega
  have hb := primitive_resonant_multiplier p n a b hp hnfull ha hm
  have h := WPReview.resonant_laurent_kernel p hprime hp b hb
  rw [← hm] at h
  have hmul := precision_mul_integral p 3 ((2 : ℚ) ^ m) _ _
    (by rw [two_zpow_unit p hp m]) h
  rw [← primitive_weight_four_kernel] at hmul
  simpa only [primitiveDigitExpansion, if_pos hr,
    WPLaurent.resonantExpansion, WPReview.fermatQuotientFour,
    WPLaurent.fermatQuotient4] using hmul

/-- Every original coefficient has its actual signed resonance or unit remainder. -/
theorem native_primitive_three_digits (p n a : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n ≤ p - 1 - p / 6) (ha : a < 3 * (p + n)) :
    WPReview.RationalCongruent p 3
      (primitiveWeight p (primitiveDenominator n a))
      (primitiveDigitExpansion p (primitiveDenominator n a)) := by
  by_cases hr : primitiveDenominator n a % (p : ℤ) = 0
  · exact native_primitive_resonant_digits p n a hp hn ha hr
  · exact native_primitive_nonresonant_digits p n a hp hn ha hr

theorem actual_moment_normalizer_unit (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    padicValRat p (2 / (3 * (125 : ℚ) ^ (p + n))) = 0 := by
  have small (v : ℕ) (hv : 0 < v) (hvp : v < p) : padicValRat p (v : ℚ) = 0 := by
    have hd : ¬p ∣ v := by
      intro h
      have := Nat.le_of_dvd hv h
      omega
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd]
    rfl
  have h2 : padicValRat p (2 : ℚ) = 0 := by simpa using small 2 (by norm_num) (by omega)
  have h3 : padicValRat p (3 : ℚ) = 0 := by simpa using small 3 (by norm_num) (by omega)
  have h5 : padicValRat p (5 : ℚ) = 0 := by simpa using small 5 (by norm_num) (by omega)
  have h125 : padicValRat p (125 : ℚ) = 0 := by
    rw [show (125 : ℚ) = 5 ^ 3 by norm_num, padicValRat.pow, h5]
    ring
  rw [padicValRat.div (by norm_num) (by positivity),
    padicValRat.mul (by norm_num) (by positivity), padicValRat.pow, h2, h3, h125]
  ring

noncomputable def actualMomentDigitExpansion (p n : ℕ) : ℚ :=
  2 / (3 * (125 : ℚ) ^ (p + n)) *
    ∑ a ∈ Finset.range (3 * (p + n)),
      ((nativeNumerator p n).coeff a : ℚ) *
        primitiveDigitExpansion p (primitiveDenominator n a)

/-- The third-digit expansion sums the entire actual numerator, not a selected band. -/
theorem actual_monomial_moment_three_digits (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n ≤ p - 1 - p / 6) :
    WPReview.RationalCongruent p 3
      (actualMonomialMoment p n) (actualMomentDigitExpansion p n) := by
  have hprime : p.Prime := Fact.out
  have hsum : WPReview.RationalCongruent p 3
      (∑ a ∈ Finset.range (3 * (p + n)),
        ((nativeNumerator p n).coeff a : ℚ) * primitiveWeight p (primitiveDenominator n a))
      (∑ a ∈ Finset.range (3 * (p + n)),
        ((nativeNumerator p n).coeff a : ℚ) * primitiveDigitExpansion p (primitiveDenominator n a)) := by
    apply (WPGammaArithmetic.rationalCongruent_iff_sub_zero p 3 _ _).mpr
    rw [← Finset.sum_sub_distrib]
    apply WPGammaArithmetic.rationalCongruent_zero_sum p 3 hprime
    intro a ha
    have hc : 0 ≤ padicValRat p ((nativeNumerator p n).coeff a : ℚ) := by
      rw [padicValRat.of_int]
      exact Int.natCast_nonneg _
    have hterm := precision_mul_integral p 3 ((nativeNumerator p n).coeff a : ℚ) _ _
      hc (native_primitive_three_digits p n a hp hn (Finset.mem_range.mp ha))
    exact (WPGammaArithmetic.rationalCongruent_iff_sub_zero p 3 _ _).mp hterm
  exact precision_mul_integral p 3 _ _ _
    (by rw [actual_moment_normalizer_unit p n hp]) hsum

theorem native_coefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (WPReview.nativeCoefficient n) := by
  rw [native_coefficient_valuation_below_prime p n hp hn]
  have hdiv : 3 * n / p ≤ 6 * n / p := Nat.div_le_div_right (by omega)
  omega

theorem actual_short_moment_three_digits (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    WPReview.RationalCongruent p 3
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * actualMonomialMoment p n)
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * actualMomentDigitExpansion p n) := by
  have hprime : p.Prime := Fact.out
  apply (WPGammaArithmetic.rationalCongruent_iff_sub_zero p 3 _ _).mpr
  rw [← Finset.sum_sub_distrib]
  apply WPGammaArithmetic.rationalCongruent_zero_sum p 3 hprime
  intro n hn
  have hnshort : n ≤ p - 1 - p / 6 := by have := Finset.mem_range.mp hn; omega
  have hnfull : n < p := by omega
  have hterm := precision_mul_integral p 3 (WPReview.nativeCoefficient n) _ _
    (native_coefficient_integral p n hp hnfull)
    (actual_monomial_moment_three_digits p n hp hnshort)
  exact (WPGammaArithmetic.rationalCongruent_iff_sub_zero p 3 _ _).mp hterm

theorem precision_trans (p k : ℕ) [Fact p.Prime] (a b c : ℚ)
    (hab : WPReview.RationalCongruent p k a b)
    (hbc : WPReview.RationalCongruent p k b c) :
    WPReview.RationalCongruent p k a c := by
  have hprime : p.Prime := Fact.out
  apply (WPGammaArithmetic.rationalCongruent_iff_sub_zero p k a c).mpr
  rw [show a - c = (a - b) + (b - c) by ring]
  exact WPGammaArithmetic.rationalCongruent_zero_add p k hprime _ _
    ((WPGammaArithmetic.rationalCongruent_iff_sub_zero p k a b).mp hab)
    ((WPGammaArithmetic.rationalCongruent_iff_sub_zero p k b c).mp hbc)

/-- The full literal native cutoff now has an unconditional finite third-digit expansion. -/
theorem actual_full_moment_three_digits (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    WPReview.RationalCongruent p 3
      (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n)
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * actualMomentDigitExpansion p n) :=
  precision_trans p 3 _ _ _
    (actual_full_literal_cutoff_moment_precision p hp)
    (actual_short_moment_three_digits p hp)

end WPNativeMomentIntegrality
