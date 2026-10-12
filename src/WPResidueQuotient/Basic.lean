import Mathlib.Algebra.MonoidAlgebra.Basic

namespace WPResidueQuotient

abbrev Exponents := Fin 5 → ℤ

abbrev LaurentPolynomial (R : Type*) [Semiring R] :=
  AddMonoidAlgebra R Exponents

end WPResidueQuotient
