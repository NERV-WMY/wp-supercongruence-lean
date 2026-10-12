import WPFieldAssembly.ActualBpairLowHGreen
import WPFiniteABSourceTail

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteAffineLog
open WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.NativeClosureLowH
variable {K : Type*} [Field K]
set_option maxHeartbeats 1400000

/-- Every coefficient of the original scaled finite logarithm enters the Laurent source. -/
theorem native_scaled_log_expansion (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (Polynomial.C c * X)).toLaurent =
      ∑ j ∈ Finset.Ico 1 p,
        LaurentPolynomial.C (c ^ j / (j : K)) * T (j : ℤ) := by
  unfold LP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp,
    mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul]
  simp only [map_sum, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  simp only [div_eq_mul_inv, ← map_mul, mul_comm]

/-- The full cutoff inversion keeps its p-phase and reflected unit denominator. -/
theorem native_scaled_log_inversion (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : K) (hc : c ≠ 0) :
    invert (((LP p : K[X]).comp (Polynomial.C c * X)).toLaurent) =
      -LaurentPolynomial.C (c ^ p) * T (-(p : ℤ)) *
        ((LP p).comp (Polynomial.C c⁻¹ * X)).toLaurent := by
  rw [native_scaled_log_expansion, map_sum]
  simp only [map_mul, invert_C, invert_T]
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => LaurentPolynomial.C (c ^ j / (j : K)) * T (-(j : ℤ))),
    native_scaled_log_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have he : c ^ (p - j) / ((p - j : ℕ) : K) =
      -(c ^ p) * ((c⁻¹) ^ j / (j : K)) := by
    rw [pow_sub₀ c hc (by omega : j ≤ p),
      WPFiniteField.reflected_denominator (K := K) p j hj]
    simp only [div_eq_mul_inv, inv_pow, inv_neg]
    ring
  have ht : (T (-(p : ℤ)) : K[T;T⁻¹]) * T (j : ℤ) =
      T (-((p - j : ℕ) : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  rw [he]
  simp only [map_mul, map_neg]
  linear_combination
    (LaurentPolynomial.C (c ^ p) * LaurentPolynomial.C ((c⁻¹) ^ j / (j : K))) * ht

/-- The reciprocal of the whole original log pair is identified before any band is selected. -/
theorem native_log_pair_inversion (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent =
      T (-(p : ℤ)) * ((lowHLog p 4).toLaurent -
        (lowHLog p (1 / 4)).toLaurent) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hA := native_scaled_log_inversion (K := K) p (1 / 4) (one_div_ne_zero h4)
  have hB := native_scaled_log_inversion (K := K) p 4 h4
  rw [hap, one_div, inv_inv] at hA
  rw [h4p] at hB
  simp only [map_ofNat] at hA hB
  have hunit : (4 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 4 : K) = 1 := by
    change LaurentPolynomial.C (4 : K) * LaurentPolynomial.C (1 / 4 : K) =
      LaurentPolynomial.C (1 : K)
    rw [← map_mul, mul_one_div_cancel h4, map_one]
  rw [one_div] at hunit
  simp only [WPFiniteABSourceTail.logTrace, map_add, map_mul, map_neg,
    invert_C, map_ofNat, Polynomial.toLaurent_C, one_div]
  rw [hA, hB]
  simp only [lowHLog, inv_inv, map_ofNat]
  linear_combination T (-(p : ℤ)) *
    (((LP p : K[X]).comp (Polynomial.C (4 : K)⁻¹ * X)).toLaurent -
      ((LP p : K[X]).comp (4 * X)).toLaurent) * hunit

end WPFieldAssembly.NativeClosureLowH
