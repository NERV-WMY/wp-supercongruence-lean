import WPFieldAssembly.ActualBpairLowHOriginBands
import WPFieldAssembly.ActualBpairKernelSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The finite twelve-band consumer is identified with the original whole kernel source. -/
theorem lowH_original_kernel_derivative_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (literalKB (K := K) p) =
      lowHKernelDerivativeBands (K := K) p := by
  simpa only [lowHKernelDerivativeBands, map_ofNat] using
    literalKB_cleared_derivative (K := K) p hp

/-- Both proper ends are cancelled as a whole before the original D-slot origin is extracted. -/
theorem lowH_original_D_KB_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    ((lowHCubicY H).toLaurent *
      (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
      (Dstar p).toLaurent * D (literalKB (K := K) p)).coeff (-1) =
      (3 / 10 : K) * (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 := by
  have he := lowH_original_kernel_derivative_source (K := K) p hp
  conv_lhs => rw [lowHBranchYQuotient_source H h0, map_mul]
  rw [show (WPFiniteZSource.Abar : K[X]).toLaurent * (lowHBranchYQuotient H).toLaurent *
      (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
      (Dstar p).toLaurent * D (literalKB (K := K) p) =
      (LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (literalKB (K := K) p)) *
      (lowHBranchYQuotient H * Dstar p).toLaurent by rw [map_mul]; ring, he]
  exact lowH_original_D_kernel_origin p hp H hH h0

/-- The original q2/kappa slot retains its own origin contribution until the q-log cancels it. -/
theorem lowH_original_constant_KB_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0)
    (q2 κ : K) :
    ((lowHCubicY H).toLaurent *
      (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
      D (literalKB (K := K) p)).coeff (-1) =
      (q2 / 2 - κ / 3) * (lowHCubicY H).coeff 0 := by
  have he := lowH_original_kernel_derivative_source (K := K) p hp
  conv_lhs => rw [lowHBranchYQuotient_source H h0, map_mul]
  rw [show (WPFiniteZSource.Abar : K[X]).toLaurent * (lowHBranchYQuotient H).toLaurent *
      (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
      D (literalKB (K := K) p) =
      (LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (literalKB (K := K) p)) *
      (lowHBranchYQuotient H).toLaurent by ring, he]
  exact lowH_original_constant_kernel_origin p hp H hH h0 q2 κ

end WPFieldAssembly.ActualBpairContraction
