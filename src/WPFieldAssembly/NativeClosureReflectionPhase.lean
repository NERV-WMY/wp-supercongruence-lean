import WPFieldAssembly.ActualSB72Attachment
import WPFieldAssembly.ActualGreenResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

/-- The actual phase is fixed by the original polynomial, including 0 and both p slots. -/
theorem native_zeta_phase (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualChiEndpoints.zeta (K := K) p =
      LaurentPolynomial.C (1 / 3 : K) * WPFiniteZSource.phase p := by
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  rw [ActualChiEndpoints.zeta, WPFiniteZSource.phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1 / 3 : K) * WPFiniteZSource.phase p * ht

end WPFieldAssembly.ActualBpairContraction
