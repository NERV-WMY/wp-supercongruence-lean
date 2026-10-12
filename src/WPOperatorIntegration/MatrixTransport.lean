import WPOperatorIntegration.QuotientCompatibility

noncomputable section

namespace WPOperatorIntegration

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- A scoped scalar-embedding lemma: its column identity is an explicit
hypothesis, later discharged by the actual two-limit calculation. -/
theorem integral_matrix_of_Qp_columns
    (A B : Matrix (Fin 5) (Fin 5) ℤ_[p]) (s : ℤ_[p])
    (h : ∀ j : Fin 5,
      Matrix.mulVec ((fun i k => (A i k : ℚ_[p])) : Matrix (Fin 5) (Fin 5) ℚ_[p])
        (fun k => (B k j : ℚ_[p])) = (s : ℚ_[p]) • Pi.single j (1 : ℚ_[p])) :
    A * B = s • (1 : Matrix (Fin 5) (Fin 5) ℤ_[p]) := by
  ext i j
  apply PadicInt.ext
  have hc := congrFun (h j) i
  by_cases hij : i = j
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
      Matrix.one_apply, hij, PadicInt.coe_sum] using hc
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply,
      Matrix.one_apply, hij, Ne.symm hij, PadicInt.coe_sum] using hc

end WPOperatorIntegration
