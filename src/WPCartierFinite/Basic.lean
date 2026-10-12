import Mathlib.Algebra.MonoidAlgebra.Basic
import WPReview.FiniteInterpolation
import WPTruncationArithmetic.Valuation

namespace WPCartierFinite

abbrev Exponents := Fin 5 → ℤ

abbrev LaurentPolynomial := AddMonoidAlgebra ℚ Exponents

end WPCartierFinite
