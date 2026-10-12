import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import WPFiniteField

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial HahnSeries

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- Frobenius support is proved for the whole infinite local power series. -/
theorem lowH_powerSeries_frobenius_coeff (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : PowerSeries K) (n : ℕ) (hn : ¬ p ∣ n) :
    PowerSeries.coeff n (Q ^ p) = 0 := by
  have hn0 : 1 ≤ n := by
    by_contra h
    have he : n = 0 := by omega
    exact hn (he ▸ dvd_zero p)
  have hu : (n : K) ≠ 0 := by
    intro he
    exact hn ((CharP.cast_eq_zero_iff K p n).mp he)
  have hd : PowerSeries.derivative K (Q ^ p) = 0 := by
    have hpC := congrArg (PowerSeries.C : K →+* PowerSeries K) (CharP.cast_eq_zero K p)
    simp only [map_natCast, map_zero] at hpC
    rw [PowerSeries.derivative_pow, hpC, zero_mul, zero_mul]
  have he := congrArg (PowerSeries.coeff (n - 1)) hd
  simp only [PowerSeries.coeff_derivative, Nat.sub_add_cancel hn0,
    map_zero, ← Nat.cast_add_one] at he
  exact (mul_eq_zero.mp he).resolve_right hu

/-- All integer exponents and arbitrary pole orders of the original local source remain. -/
theorem lowH_series_frobenius_coeff (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : LaurentSeries K) (j : ℤ) (hj : ¬ (p : ℤ) ∣ j) : (Q ^ p).coeff j = 0 := by
  have hshift : ¬ (p : ℤ) ∣ j - (p : ℤ) * Q.order := by
    rintro ⟨k, hk⟩
    apply hj
    refine ⟨k + Q.order, ?_⟩
    linear_combination hk
  rw [← LaurentSeries.single_order_mul_powerSeriesPart Q, mul_pow,
    HahnSeries.single_pow, one_pow, nsmul_eq_mul, HahnSeries.coeff_single_mul, one_mul,
    ← PowerSeries.coe_pow, PowerSeries.coeff_coe]
  by_cases hn : j - (p : ℤ) * Q.order < 0
  · rw [if_pos hn]
  · rw [if_neg hn]
    apply lowH_powerSeries_frobenius_coeff p
    intro h
    apply hshift
    have he : ((j - (p : ℤ) * Q.order).natAbs : ℤ) = j - (p : ℤ) * Q.order :=
      (Int.eq_natAbs_of_nonneg (by omega)).symm
    rw [← he]
    exact_mod_cast h

theorem lowH_series_polynomial_monomial (a : K) (n : ℕ) :
    algebraMap K[X] (LaurentSeries K) (Polynomial.C a * X ^ n) = HahnSeries.single (n : ℤ) a := by
  rw [Polynomial.algebraMap_hahnSeries_apply]
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
    map_mul, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X,
    HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

/-- No truncation is applied to Q: this includes every rational denominator and Frobenius phase. -/
theorem lowH_series_full_frobenius_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[X]) (hS : S.natDegree < p - 1) (Q : LaurentSeries K) :
    (Q ^ p * algebraMap K[X] (LaurentSeries K) S).coeff (-1) = 0 := by
  have he := congrArg (fun P : K[X] =>
    (Q ^ p * algebraMap K[X] (LaurentSeries K) P).coeff (-1)) S.as_sum_support_C_mul_X_pow
  rw [he]
  simp only [map_sum, Finset.mul_sum, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [lowH_series_polynomial_monomial, HahnSeries.coeff_mul_single]
  have hnle : n ≤ S.natDegree := le_natDegree_of_ne_zero (mem_support_iff.mp hn)
  have hnd : ¬ (p : ℤ) ∣ -1 - (n : ℤ) := by
    intro h
    have he : (p : ℤ) ∣ (n : ℤ) + 1 := by
      convert Int.dvd_neg.mpr h using 1
      ring
    have hu : 0 < (n : ℤ) + 1 ∧ (n : ℤ) + 1 < p := by omega
    exact (not_lt_of_ge (Int.le_of_dvd hu.1 he)) hu.2
  rw [lowH_series_frobenius_coeff p Q _ hnd, zero_mul]

/-- The built-in rational expansion supplies actual rational poles, rather than a finite surrogate. -/
theorem lowH_rational_full_frobenius_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[X]) (hS : S.natDegree < p - 1) (Q : RatFunc K) :
    (algebraMap (RatFunc K) (LaurentSeries K) (Q ^ p) *
      algebraMap K[X] (LaurentSeries K) S).coeff (-1) = 0 := by
  rw [map_pow]
  exact lowH_series_full_frobenius_residue p hp S hS _

end WPFieldAssembly.ActualBpairContraction
