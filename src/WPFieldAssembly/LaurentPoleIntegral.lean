import WPFieldAssembly.LaurentPoleTrace
import WPActualEtaIntegrality

open scoped LaurentPolynomial PowerSeries BigOperators
open WPPIntegralReduction

namespace WPFieldAssembly.LaurentPoleIntegral

open LaurentPoleTrace

theorem denominator_bound_integral (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : q.den < p) : q ∈ integralRationals p := by
  change 0 ≤ padicValRat p q
  apply (integral_iff_denominator_not_dvd p q).mpr
  intro h
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero q.den_ne_zero) h
  omega

theorem quarter_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1/4 : ℚ) ∈ integralRationals p := by
  apply denominator_bound_integral p
  norm_num
  omega

theorem four_fifteenths_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4/15 : ℚ) ∈ integralRationals p := by
  apply denominator_bound_integral p
  norm_num
  omega

/-- The literal reciprocal coefficient is integral before any residue reduction. -/
theorem literal_reciprocal_integral (p k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((4/15 : ℚ)*(4^(k+1)-(1/4 : ℚ)^(k+1))) ∈ integralRationals p := by
  exact (integralRationals p).mul_mem (four_fifteenths_integral p hp)
    ((integralRationals p).sub_mem
      ((integralRationals p).pow_mem (natCast_mem (integralRationals p) 4) (k+1))
      ((integralRationals p).pow_mem (quarter_integral p hp) (k+1)))

theorem reciprocal_coeff_integral (p k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.coeff k reciprocal ∈ integralRationals p := by
  rw [reciprocal, PowerSeries.coeff_mk]
  exact literal_reciprocal_integral p k hp

/-- All powers use the checked finite convolution of the literal rational coefficients. -/
theorem reciprocal_power_coeff_integral (p m k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.coeff k (reciprocal^m) ∈ integralRationals p := by
  induction m generalizing k with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact (integralRationals p).one_mem
    · exact (integralRationals p).zero_mem
  | succ m ih =>
    rw [reciprocal_finite_recurrence]
    apply (integralRationals p).sum_mem
    intro q _
    exact (integralRationals p).mul_mem (ih q.1)
      (literal_reciprocal_integral p q.2 hp)

theorem zcoeff_power_integral (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    zcoeff n (reciprocal^m) ∈ integralRationals p := by
  by_cases hn : 0 ≤ n
  · rw [zcoeff, if_pos hn]
    exact reciprocal_power_coeff_integral p m n.toNat hp
  · rw [zcoeff, if_neg hn]
    exact (integralRationals p).zero_mem

theorem weight_integral (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    weight m n ∈ integralRationals p := by
  have hquarter : (-1/4 : ℚ) ∈ integralRationals p := by
    rw [show (-1/4 : ℚ) = -(1/4 : ℚ) by ring]
    exact (integralRationals p).neg_mem (quarter_integral p hp)
  exact (integralRationals p).mul_mem
    ((integralRationals p).neg_mem ((integralRationals p).pow_mem hquarter m))
    (zcoeff_power_integral p m hp _)

/-- The whole finite Laurent input is transported over the actual p-integral subring. -/
theorem trace_integral (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (L : ℚ[T;T⁻¹])
    (hL : L ∈ WPActualEtaIntegrality.integralLaurent p) :
    LaurentPoleTrace.trace m L ∈ integralRationals p := by
  rw [trace_eq_sum]
  unfold Finsupp.sum
  apply (integralRationals p).sum_mem
  intro n _
  exact (integralRationals p).mul_mem (hL n) (weight_integral p m hp n)

theorem trace_padicVal_nonneg (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : ∀ n, 0 ≤ padicValRat p (L.coeff n)) :
    0 ≤ padicValRat p (LaurentPoleTrace.trace m L) :=
  trace_integral p m hp L hL

end WPFieldAssembly.LaurentPoleIntegral
