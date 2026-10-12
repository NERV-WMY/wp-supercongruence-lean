import WPFieldAssembly.ActualBpairLowHSeries
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The literal finite Laurent source is embedded by all of its original integer coefficients. -/
noncomputable def lowHFiniteSeries : K[T;T⁻¹] →ₗ[K] LaurentSeries K :=
  (HahnSeries.ofFinsuppLinearMap K).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem lowHFiniteSeries_coeff (A : K[T;T⁻¹]) (n : ℤ) :
    (lowHFiniteSeries A).coeff n = A.coeff n := rfl

theorem lowHFiniteSeries_monomial (a : K) (n : ℤ) :
    lowHFiniteSeries (LaurentPolynomial.C a * T n) = HahnSeries.single n a := by
  ext j
  rw [lowHFiniteSeries_coeff, ← single_eq_C_mul_T]
  rfl

theorem lowHFiniteSeries_mul (A B : K[T;T⁻¹]) :
    lowHFiniteSeries (A * B) = lowHFiniteSeries A * lowHFiniteSeries B := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB =>
    simp only [add_mul, map_add, hA, hB]
  | C_mul_T n a =>
    induction B using LaurentPolynomial.induction_on' with
    | add A B hA hB => simp only [mul_add, map_add, hA, hB]
    | C_mul_T m b =>
      rw [show LaurentPolynomial.C a * T n * (LaurentPolynomial.C b * T m) =
          LaurentPolynomial.C (a * b) * T (n + m) by rw [map_mul, T_add]; ring,
        lowHFiniteSeries_monomial, lowHFiniteSeries_monomial, lowHFiniteSeries_monomial,
        HahnSeries.single_mul_single]

theorem lowH_series_derivative_coeff (Q : LaurentSeries K) (n : ℤ) :
    (LaurentSeries.derivative K Q).coeff n = ((n + 1 : ℤ) : K) * Q.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right]
  exact zsmul_eq_mul _ _

theorem lowHFiniteSeries_derivative (A : K[T;T⁻¹]) :
    lowHFiniteSeries (D A) = LaurentSeries.derivative K (lowHFiniteSeries A) := by
  ext n
  rw [lowHFiniteSeries_coeff, D_coeff, lowH_series_derivative_coeff, lowHFiniteSeries_coeff]

theorem lowH_series_derivative_residue (Q : LaurentSeries K) :
    (LaurentSeries.derivative K Q).coeff (-1) = 0 := by
  rw [lowH_series_derivative_coeff]
  simp

/-- Integration by parts uses the entire second Laurent expansion, including all original poles. -/
theorem lowH_finite_series_IBP (A : K[T;T⁻¹]) (Q : LaurentSeries K) :
    (lowHFiniteSeries (D A) * Q).coeff (-1) +
      (lowHFiniteSeries A * LaurentSeries.derivative K Q).coeff (-1) = 0 := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB =>
    simp only [map_add, add_mul, HahnSeries.coeff_add] at *
    linear_combination hA + hB
  | C_mul_T n a =>
    rw [D_monomial, lowHFiniteSeries_monomial, lowHFiniteSeries_monomial,
      HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul, lowH_series_derivative_coeff]
    rw [show (-1 : ℤ) - (n - 1) = -n by omega,
      show (-1 : ℤ) - n + 1 = -n by omega]
    simp only [Int.cast_neg]
    ring

/-- The ordinary power-series derivative agrees with the full Laurent derivative after embedding. -/
theorem lowH_series_derivative_powerSeries (J : PowerSeries K) :
    LaurentSeries.derivative K (J : LaurentSeries K) =
      (PowerSeries.derivative K J : LaurentSeries K) := by
  ext n
  rw [lowH_series_derivative_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  by_cases hn : n < 0
  · rw [if_pos hn]
    by_cases hn1 : n + 1 < 0
    · rw [if_pos hn1, mul_zero]
    · have hzero : n + 1 = 0 := by omega
      rw [hzero, Int.cast_zero, zero_mul]
  · rw [if_neg hn, if_neg (by omega : ¬n + 1 < 0), PowerSeries.coeff_derivative]
    have hn0 : ((n.natAbs : ℕ) : ℤ) = n := (Int.eq_natAbs_of_nonneg (by omega)).symm
    have hn1cast : (((n + 1).natAbs : ℕ) : ℤ) = n + 1 :=
      (Int.eq_natAbs_of_nonneg (by omega)).symm
    have hn1 : (n + 1).natAbs = n.natAbs + 1 := by omega
    rw [hn1]
    have hc : ((n + 1 : ℤ) : K) = ((n.natAbs + 1 : ℕ) : K) := by
      rw [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
      congr 1
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : K)) hn0.symm
    rw [hc, Nat.cast_add, Nat.cast_one]
    ring

end WPFieldAssembly.ActualBpairContraction
