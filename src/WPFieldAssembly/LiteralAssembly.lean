import WPLiteralAdapter.FinalAdapter
import WPNativeMomentDigitExpansion
import WPReview.ExceptionPrimes
import WPSmallPrime13And17Literal

open scoped BigOperators
open WPNativeMomentIntegrality WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPFieldAssembly.LiteralAssembly

/-- Exact valuation cancellation retains the zero case at every precision. -/
theorem precisionZero_cancel_exact_valuation
    (p k l : ℕ) [Fact p.Prime] (c a : ℚ) (hc : c ≠ 0)
    (hv : padicValRat p c = (l : ℤ))
    (h : precisionZero p (k + l) (c * a)) : precisionZero p k a := by
  by_cases ha : a = 0
  · exact Or.inl ha
  rcases h with h | h
  · exact Or.inl ((mul_eq_zero.mp h).resolve_left hc)
  apply Or.inr
  rw [padicValRat.mul hc ha, hv] at h
  simp only [Nat.cast_add] at h
  omega

private theorem small_rational_unit (p n : ℕ) (hn : 0 < n) (hnp : n < p) :
    padicValRat p (n : ℚ) = 0 := by
  have hnd : ¬p ∣ n := by
    intro hd
    have hle := Nat.le_of_dvd hn hd
    omega
  simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Int.natCast_zero]

/-- The original normalized literal multiplier loses exactly two digits. -/
theorem literal_multiplier_valuation
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    padicValRat p (3375 * (p : ℚ)^2 * (120 / (1728 : ℚ)^p)) = 2 := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    simpa using small_rational_unit p 2 (by norm_num) (by omega)
  have hthree : padicValRat p (3 : ℚ) = 0 := by
    simpa using small_rational_unit p 3 (by norm_num) (by omega)
  have hfive : padicValRat p (5 : ℚ) = 0 := by
    simpa using small_rational_unit p 5 (by norm_num) (by omega)
  have h3375 : padicValRat p (3375 : ℚ) = 0 := by
    rw [show (3375 : ℚ) = 3^3 * 5^3 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
      padicValRat.pow, hthree, hfive]
    norm_num
  have h120 : padicValRat p (120 : ℚ) = 0 := by
    rw [show (120 : ℚ) = 2^3 * 3 * 5 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num),
      padicValRat.mul (by norm_num) (by norm_num), padicValRat.pow,
      htwo, hthree, hfive]
    norm_num
  have hN0 : (120 / (1728 : ℚ)^p) ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero p (by norm_num))
  have hN : padicValRat p (120 / (1728 : ℚ)^p) = 0 := by
    rw [padicValRat.div (by norm_num) (pow_ne_zero p (by norm_num)),
      h120, padicValRat.pow, native_normalizer_unit p (by omega)]
    norm_num
  rw [padicValRat.mul (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpq)) hN0,
    padicValRat.mul (by norm_num) (pow_ne_zero 2 hpq), h3375,
    padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt, hN]
  norm_num

/-- The checked original literal congruence recovers the same full actual moment. -/
theorem full_actual_moment_of_literal
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hl : WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2)) :
    WPReview.RationalCongruent p 3 (WPLiteralAdapter.fullActualMoment p)
      ((1728 : ℚ)^p / 45000) := by
  let R := integralSubring p
  let M := WPLiteralAdapter.fullActualMoment p
  let N : ℚ := 120 / (1728 : ℚ)^p
  let T : ℚ := (1728 : ℚ)^p / 45000
  let K : ℚ := 3375 * (p : ℚ)^2 * N
  have hMI : 0 ≤ padicValRat p M := by
    change M ∈ R
    dsimp only [M, WPLiteralAdapter.fullActualMoment]
    apply R.sum_mem
    intro n hn
    have hnp : n < p := Finset.mem_range.mp hn
    exact R.mul_mem
      (native_coefficient_integral p n (by omega) hnp)
      (actual_monomial_moment_integral p n (by omega) hnp)
  obtain ⟨ha, hn⟩ := WPLiteralAdapter.actual_literal_adapter_and_normalization p hp
  have hreplace : WPReview.RationalCongruent p 3
      (WPReview.nativeCoefficient p * M) (N * M) := by
    convert precision_mul_integral p 3 M _ _ hMI hn using 1 <;> ring
  have hzreplace : precisionZero p 3 (WPReview.nativeCoefficient p * M - N * M) := by
    simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero] using hreplace
  have hp₂ : precisionZero p 2 ((p : ℚ)^2) := by
    apply Or.inr
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hreplace₅ := precisionZero_mul p 2 3 _ _ hp₂ hzreplace
  have hreplace3375 :=
    precisionZero_mul_integral p 5 _ 3375 hreplace₅ (natCast_mem R 3375)
  have hnz : precisionZero p 5
      (3375 * (p : ℚ)^2 * WPReview.nativeCoefficient p * M - K * M) := by
    convert hreplace3375 using 1
    dsimp only [K]
    ring
  have haz : precisionZero p 5
      (WPReview.literalSum p - 3375 * (p : ℚ)^2 * WPReview.nativeCoefficient p * M) := by
    simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero, M] using ha
  have hlz : precisionZero p 5 (WPReview.literalSum p - 9 * (p : ℚ)^2) := by
    simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero] using hl
  have hnative : precisionZero p 5
      (3375 * (p : ℚ)^2 * WPReview.nativeCoefficient p * M - 9 * (p : ℚ)^2) := by
    convert precisionZero_add p 5 _ _
      (precisionZero_neg p 5 _ haz) hlz using 1
    ring
  have hnorm : precisionZero p 5 (K * M - 9 * (p : ℚ)^2) := by
    convert precisionZero_add p 5 _ _
      (precisionZero_neg p 5 _ hnz) hnative using 1
    ring
  have hNT : N * T = (1 / 375 : ℚ) := by
    dsimp only [N, T]
    have hz : (1728 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
    field_simp [hz]
    ring
  have hKT : K * T = 9 * (p : ℚ)^2 := by
    dsimp only [K]
    rw [mul_assoc, hNT]
    ring
  have hdiff : precisionZero p (3 + 2) (K * (M - T)) := by
    convert hnorm using 1
    rw [← hKT]
    ring
  have hK0 : K ≠ 0 := by
    dsimp only [K, N]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))
      (div_ne_zero (by norm_num) (pow_ne_zero p (by norm_num)))
  have hval : padicValRat p K = (2 : ℤ) := literal_multiplier_valuation p hp
  have hmoment := precisionZero_cancel_exact_valuation p 3 2 K (M - T) hK0 hval hdiff
  simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero, M, T] using hmoment

/-- The exact literal consequence of the complete actual moment congruence. -/
theorem literal_of_full_actual_moment
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hm : WPReview.RationalCongruent p 3
      (WPLiteralAdapter.fullActualMoment p) ((1728 : ℚ)^p / 45000)) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  let R := integralSubring p
  let M := WPLiteralAdapter.fullActualMoment p
  let N : ℚ := 120 / (1728 : ℚ)^p
  let T : ℚ := (1728 : ℚ)^p / 45000
  have hMI : 0 ≤ padicValRat p M := by
    change M ∈ R
    dsimp only [M, WPLiteralAdapter.fullActualMoment]
    apply R.sum_mem
    intro n hn
    have hnp : n < p := Finset.mem_range.mp hn
    exact R.mul_mem
      (native_coefficient_integral p n (by omega) hnp)
      (actual_monomial_moment_integral p n (by omega) hnp)
  have hNI : 0 ≤ padicValRat p N := by
    have hi : ((1728 : ℚ)^p)⁻¹ ∈ R := by
      change 0 ≤ padicValRat p ((1728 : ℚ)^p)⁻¹
      rw [padicValRat.inv, padicValRat.pow, native_normalizer_unit p (by omega)]
      simp
    change N ∈ R
    simpa only [N, div_eq_mul_inv, Nat.cast_ofNat] using
      R.mul_mem (natCast_mem R 120) hi
  obtain ⟨ha, hn⟩ := WPLiteralAdapter.actual_literal_adapter_and_normalization p hp
  have h₁ : WPReview.RationalCongruent p 3
      (WPReview.nativeCoefficient p * M) (N * M) := by
    convert precision_mul_integral p 3 M _ _ hMI hn using 1 <;> ring
  have h₂ : WPReview.RationalCongruent p 3 (N * M) (N * T) :=
    precision_mul_integral p 3 N _ _ hNI hm
  have h₃ := precision_trans p 3 _ _ _ h₁ h₂
  have hd : precisionZero p 3 (WPReview.nativeCoefficient p * M - N * T) := by
    simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero] using h₃
  have hp₂ : precisionZero p 2 ((p : ℚ)^2) := by
    apply Or.inr
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hd₅ := precisionZero_mul p 2 3 _ _ hp₂ hd
  have hs := precisionZero_mul_integral p 5 _ 3375 hd₅ (natCast_mem R 3375)
  have hNT : N * T = (1 / 375 : ℚ) := by
    dsimp only [N, T]
    have hz : (1728 : ℚ)^p ≠ 0 := pow_ne_zero p (by norm_num)
    field_simp [hz]
    ring
  have hv : 3375 * (p : ℚ)^2 * (N * T) = 9 * (p : ℚ)^2 := by
    rw [hNT]
    ring
  have hstep : WPReview.RationalCongruent p 5
      (3375 * (p : ℚ)^2 * WPReview.nativeCoefficient p * M)
      (9 * (p : ℚ)^2) := by
    have hz : precisionZero p 5
        (3375 * (p : ℚ)^2 * WPReview.nativeCoefficient p * M - 9 * (p : ℚ)^2) := by
      convert hs using 1
      rw [← hv]
      ring
    simpa only [WPReview.RationalCongruent, precisionZero, sub_eq_zero] using hz
  exact precision_trans p 5 _ _ _ ha hstep

/-- Precision five for the literal sum is exactly precision three for its actual moment. -/
theorem literal_iff_full_actual_moment
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) ↔
      WPReview.RationalCongruent p 3 (WPLiteralAdapter.fullActualMoment p)
        ((1728 : ℚ)^p / 45000) :=
  ⟨full_actual_moment_of_literal p hp, literal_of_full_actual_moment p hp⟩

/-- The retained four small primes complete any actual large-prime endpoint. -/
theorem literal_of_large_prime_endpoint
    (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hlarge : 19 ≤ p →
      WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2)) :
    WPReview.RationalCongruent p 5 (WPReview.literalSum p) (9 * (p : ℚ)^2) := by
  by_cases hp19 : 19 ≤ p
  · exact hlarge hp19
  have hlt : p < 19 := lt_of_not_ge hp19
  have hprime : p.Prime := Fact.out
  have hc : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    interval_cases p <;> norm_num at hprime
    all_goals norm_num
  rcases hc with rfl | rfl | rfl | rfl
  · exact WPReview.literal_seven
  · exact WPReview.literal_eleven
  · exact WPReview.literal_thirteen
  · exact WPReview.literal_seventeen

end WPFieldAssembly.LiteralAssembly
