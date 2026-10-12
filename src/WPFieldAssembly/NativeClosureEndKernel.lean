import WPFieldAssembly.NativeClosureEndBands
import WPFieldAssembly.NativeClosureLowHSource
import WPFieldAssembly.ActualCubicNativeSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteAffineLog
open WPFieldAssembly.ActualCubicNativeSource WPFieldAssembly.NativeClosureLowH

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- Actual P and the actual native logarithm select both complete SB107 bands.
The equality fixes the source itself, including its invisible coefficients. -/
theorem actual_P_endKernel_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
      ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p)) =
        endKernelChi0 (K := K) p := by
  have he := native_Cslot (K := K) p hp u hu
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    convert mul_ne_zero h3 h5 using 1; norm_num
  have hscalar : -nativeConstant (K := K) p / 3 - WPFiniteNC122.h p / 3 -
      (11 * WPFiniteNC122.q p / 15 -
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2) = 0 := by
    dsimp only [nativeConstant]
    field_simp [h2, h3, h5, h15]
    ring
  have hc := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hscalar
  simp only [lowHWholeCslot, lowHLog, one_div, inv_inv] at he
  simp only [endKernelChi0, endKernelW0, endKernelW1, div_eq_mul_inv,
    map_sub, map_add, map_neg, map_mul, map_one, map_ofNat, map_zero,
    Polynomial.toLaurent_C] at he hc ⊢
  linear_combination (norm := ring_nf) he + hc

end WPFieldAssembly.ActualBpairContraction
