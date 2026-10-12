import WPFieldAssembly.ActualBpairLowHRemainingLogs
import WPFieldAssembly.ActualBpairLowHLogDerivative
import WPFieldAssembly.ActualBpairLowHKernelLog
import WPFieldAssembly.ActualBpairLowHKernelAttachment

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: The full original mixed log portion IR71g--i is
paired with the literal K_B and its actual derivative. Both proper ends,
all three kernel phases, y(0) and the two auxiliary origin primitives remain
in the source until their proved common cancellation. No native-u or Gauss
endpoint value is assumed. The root-owned kernel import remains required. -/

/-- The complete twelve-band source is multiplied by the genuine y/Abar quotient. -/
theorem lowH_original_kernel_rows_source (p : ℕ) (H : K[X]) :
    lowHKernelDerivativeBands (K := K) p * (lowHBranchYQuotient H).toLaurent =
      (1 - T ((p - 1 : ℕ) : ℤ)) *
        ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
          T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent) := by
  simp only [lowHKernelDerivativeBands, lowHKernelRowZero, lowHKernelRowOne,
    lowHKernelRowTwo, map_mul, map_add, map_sub, map_ofNat, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  ring

/-- Both ends cancel against y before the actual kernel derivative is transported to its full rows. -/
theorem lowH_original_derivative_log_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (lowHCubicY H).toLaurent * D (literalKB (K := K) p) =
      LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (1 - T ((p - 1 : ℕ) : ℤ)) *
        ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
          T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent) := by
  rw [lowHBranchYQuotient_source H h0, map_mul]
  calc
    _ = LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        ((WPFiniteZSource.Abar : K[X]).toLaurent * D (literalKB (K := K) p) *
          (lowHBranchYQuotient H).toLaurent) := by ring
    _ = _ := by
      rw [lowH_original_kernel_derivative_source p hp, lowH_original_kernel_rows_source]
      ring

theorem lowH_original_derivative_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    (LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
      (lowHCubicY H).toLaurent * D (literalKB (K := K) p)).coeff (-1) =
      -(lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) +
        (2 / 15 : K) * ((1 / 4) * WPFiniteProductTail.originPrimitive p (lowHCubicY H) 4 -
          4 * WPFiniteProductTail.originPrimitive p (lowHCubicY H) (1 / 4)) := by
  have hb := lowH_prime_six_band p hp
  rw [lowH_original_derivative_log_source p hp H h0]
  exact lowH_original_three_rows_two_end_residue p hp (p / 6) (by omega) hb.2 H hH h0

/-- The actual three log groups cancel both auxiliary primitives together. -/
theorem lowH_original_whole_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    (LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (lowHCubicY H).toLaurent * D (literalKB (K := K) p) +
      LaurentPolynomial.C (-5 / 6 : K) *
        (literalKB (K := K) p * (lowHqCubicDensity H).toLaurent) +
      lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
        (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0)).coeff (-1) =
      (8 / 75 : K) * (lowHEulerJ p H).eval 1 := by
  have hb := lowH_prime_six_band p hp
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [lowH_original_derivative_log_residue p hp H hH h0,
    lowH_literalKB_scaled_cubic_log_residue p hp (p / 6) (by omega) hb.2 H hH h0,
    lowH_original_remaining_log_residue p hp H hH h0]
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h6]
  ring

end WPFieldAssembly.ActualBpairContraction
