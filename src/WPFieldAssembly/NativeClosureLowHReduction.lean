import WPFieldAssembly.NativeClosureLowHCarrier
import WPFieldAssembly.NativeClosureLowHIdentity

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualCubicNativeSource

namespace WPFieldAssembly.NativeClosureLowH
variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The y*dlogQ density is the original full reciprocal cubic source, including its origin pole. -/
theorem native_qlog_density (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHLinearYQLog H = 3 * (4 * T (-1) - 11) *
      (lowHBranchYQuotient H).toLaurent := by
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by
    rw [← T_add]; norm_num
  rw [lowHLinearYQLog, lowHLinearYOverX,
    lowHBranchYQuotient_source H h0]
  simp only [map_mul, map_sub, map_ofNat, WPFiniteZSource.Abar,
    Polynomial.toLaurent_X, map_one]
  linear_combination 12 * (lowHBranchYQuotient H).toLaurent * T 1 * ht -
    51 * (lowHBranchYQuotient H).toLaurent * ht

/-- The derivative is obtained from the actual positive carrier by complete inversion. -/
theorem native_v_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (actualAK (K := K) p).toLaurent) =
      -LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
            (4 * T (-(p : ℤ)) - 11)) := by
  have h := congrArg invert (actual_AK_cleared_derivative (K := K) p hp)
  simp only [map_mul, map_sub, map_ofNat, invert_C, invert_T,
    WPFiniteZSource.invert_Abar, WPFiniteZSource.invert_squared_power] at h
  rw [D_invert]
  linear_combination -h

/-- The reciprocal source retains its exact half-Frobenius band before contraction. -/
theorem native_v_shifted_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    T (((p - 1) / 2 : ℕ) : ℤ) *
      (2 * ((lowHCubicY H).toLaurent * D (invert (actualAK (K := K) p).toLaurent)) +
        lowHLinearYQLog H) =
      3 * (4 * T (-(p : ℤ)) - 11) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (lowHBranchYQuotient H).toLaurent := by
  have h := native_v_cleared_derivative (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : (2 : K[T;T⁻¹]) * LaurentPolynomial.C (3 / 2 : K) = 3 := by
    change LaurentPolynomial.C (2 : K) * LaurentPolynomial.C (3 / 2 : K) =
      LaurentPolynomial.C (3 : K)
    rw [← map_mul]; congr 1; field_simp [h2]
  have ht : (T (((p - 1) / 2 : ℕ) : ℤ) *
      T (-(((p - 1) / 2 : ℕ) : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  rw [lowHBranchYQuotient_source H h0, map_mul, native_qlog_density H h0]
  linear_combination 2 * T (((p - 1) / 2 : ℕ) : ℤ) *
    (lowHBranchYQuotient H).toLaurent * h -
    T (((p - 1) / 2 : ℕ) : ℤ) * (lowHBranchYQuotient H).toLaurent *
      ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (-(p : ℤ)) - 11)) * hc +
    3 * (4 * T (-(p : ℤ)) - 11) *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (lowHBranchYQuotient H).toLaurent * ht

end WPFieldAssembly.NativeClosureLowH
