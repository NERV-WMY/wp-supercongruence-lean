import WPCompletedCartier.ActualMatrix

namespace WPCompletedCartier.ActualNormalization

noncomputable section
open scoped BigOperators
open WPCompletedCartier.ActualMatrix WPCompletedCartier.ScalarBridge

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)

/-- The actual integral marked vector in the factorial Gamma coordinates. -/
def gammaMarkedZp : Fin 5 → ℤ_[p] :=
  (inverseFactorialMatrixZp p hp).mulVec (markedZp p hp)

@[simp] theorem gammaMarkedZp_coe (i : Fin 5) :
    (gammaMarkedZp p hp i : ℚ_[p]) = (gammaMarkedVector i : ℚ_[p]) := by
  have hm : inverseFactorialMatrix.mulVec WPCartierFinite.markedVector =
      gammaMarkedVector := by
    rw [← factorialMatrix_marked, Matrix.mulVec_mulVec,
      factorialMatrix_inverse_left, Matrix.one_mulVec]
  have hi := congrFun hm i
  have hiQ := congrArg (fun q : ℚ => (q : ℚ_[p])) hi
  simp only [inverseFactorialMatrix, Matrix.mulVec_diagonal,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast] at hiQ
  simpa only [gammaMarkedZp, inverseFactorialMatrixZp, Matrix.mulVec_diagonal,
    PadicInt.coe_mul, inverseFactorialZp_coe, markedZp_coe] using hiQ

theorem gammaMarkedZp_literal :
    (fun i => (gammaMarkedZp p hp i : ℚ_[p])) =
      fun i => (gammaMarkedVector i : ℚ_[p]) := by
  funext i
  exact gammaMarkedZp_coe p hp i

def gammaScalarRowZp : Fin 5 → ℤ_[p] := fun i => (i.val.factorial : ℤ_[p])

theorem gammaScalarRowZp_literal : gammaScalarRowZp p = ![1, 1, 2, 6, 24] := by
  ext i
  fin_cases i <;> norm_num [gammaScalarRowZp]

def lambdaGammaZp (v : Fin 5 → ℤ_[p]) : ℤ_[p] := dotProduct (gammaScalarRowZp p) v

theorem lambdaGammaZp_eq_H (v : Fin 5 → ℤ_[p]) :
    lambdaGammaZp p v =
      dotProduct (1 : Fin 5 → ℤ_[p]) ((factorialMatrixZp p).mulVec v) := by
  simp only [lambdaGammaZp, gammaScalarRowZp, factorialMatrixZp,
    Matrix.mulVec_diagonal, dotProduct, Pi.one_apply, one_mul]

theorem gammaMarkedZp_H :
    (factorialMatrixZp p).mulVec (gammaMarkedZp p hp) = markedZp p hp := by
  ext i
  simp only [factorialMatrixZp, gammaMarkedZp, inverseFactorialMatrixZp,
    Matrix.mulVec_diagonal]
  rw [← mul_assoc, mul_comm (i.val.factorial : ℤ_[p]),
    inverseFactorialZp_mul, one_mul]

theorem gammaMarkedZp_pairing : lambdaGammaZp p (gammaMarkedZp p hp) = 9 := by
  rw [lambdaGammaZp_eq_H, gammaMarkedZp_H]
  simpa only [dotProduct, Pi.one_apply, one_mul] using marked_pairing_zp p hp

/-- H transports the scalar and both actual coordinate vectors exactly. -/
theorem normalized_marked_scalar (C : Matrix (Fin 5) (Fin 5) ℤ_[p]) :
    lambdaGammaZp p (C.mulVec (gammaMarkedZp p hp)) =
      dotProduct (1 : Fin 5 → ℤ_[p])
        ((factorialMatrixZp p * C * inverseFactorialMatrixZp p hp).mulVec
          (markedZp p hp)) := by
  rw [lambdaGammaZp_eq_H, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rfl

variable (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem actual_normalized_marked_scalar :
    lambdaGammaZp p ((actualGammaMatrix p hp hp7 hp19).mulVec (gammaMarkedZp p hp)) =
      dotProduct (1 : Fin 5 → ℤ_[p])
        ((actualPhiMatrix p hp hp7 hp19).mulVec (markedZp p hp)) :=
  normalized_marked_scalar p hp (actualGammaMatrix p hp hp7 hp19)

/-- This uses the constructed matrix's congruence; no scalar-value premise is added. -/
theorem actualGamma_literal_congruence :
    lambdaGammaZp p ((actualGammaMatrix p hp hp7 hp19).mulVec (gammaMarkedZp p hp)) -
        literalSumZp p hp ∈ Ideal.span ({(p : ℤ_[p]) ^ 5} : Set ℤ_[p]) := by
  rw [actual_normalized_marked_scalar]
  exact actualCartier_literal_congruence p hp hp7 hp19

theorem actualGamma_literal_congruence_qp :
    QpCongruent p 5
      (lambdaGammaZp p
        ((actualGammaMatrix p hp hp7 hp19).mulVec (gammaMarkedZp p hp)) : ℚ_[p])
      (WPReview.literalSum p : ℚ_[p]) := by
  rw [← literalSumZp_coe p hp]
  exact (qpCongruent_coe_iff_ideal p 5 _ _).mpr
    (actualGamma_literal_congruence p hp hp7 hp19)

end

end WPCompletedCartier.ActualNormalization
