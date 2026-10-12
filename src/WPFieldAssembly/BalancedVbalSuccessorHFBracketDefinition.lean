import WPFieldAssembly.SourceClosureHFBranchFactor
import WPFieldAssembly.ActualSB72Attachment

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFieldAssembly.ActualBpairContraction
  WPFieldAssembly.ActualGreenResidue

namespace WPFieldAssembly.SourceClosureHFNativeTransport

variable {K : Type*} [Field K]

/-- The full HF bracket uses v=L(Q)-h and u=L(V)-h in that order. -/
noncomputable def nativeHFBracket (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  -T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (WPFiniteZSource.P p u) +
    LaurentPolynomial.C (1 / 3 : K) *
      (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          (invert (actualAK (K := K) p).toLaurent + LaurentPolynomial.C (hK (K := K) p)) -
        ((actualAK (K := K) p).toLaurent + LaurentPolynomial.C (hK (K := K) p)))

end WPFieldAssembly.SourceClosureHFNativeTransport
