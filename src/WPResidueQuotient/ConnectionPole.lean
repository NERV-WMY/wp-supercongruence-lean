import WPResidueQuotient.ConnectionReduction
import WPResidueQuotient.PoleRecurrence

namespace WPResidueQuotient.ActualConnection

noncomputable section

variable (K : Type*) [CommRing K]

/-- The fifth connection column uses the proved six-vertex identity in
    the actual quotient, with the genuine inverted discriminant. -/
theorem qGamma_six (h6 : IsUnit (6 : K)) :
    qGamma K 5 = (Parameter.discriminantInverse : Coeff K) •
      (qGamma K 0 - 31 • qGamma K 1 + 90 • qGamma K 2 -
        65 • qGamma K 3 + 15 • qGamma K 4) := by
  let v : Coeff K := boundaryScalar K h6
  let d : Coeff K := Parameter.discriminantInverse
  have huv : v * (6 * parameter K) = 1 := by
    rw [mul_comm]
    exact six_parameter_mul_boundaryScalar K h6
  have hd : d * (1 - (6 * parameter K) ^ 6) = 1 := by
    rw [mul_comm]
    exact Parameter.discriminant_mul_inverse
  let c : FClosed (parameter K) := gammaClosed K 0 - 31 • gammaClosed K 1 +
    90 • gammaClosed K 2 - 65 • gammaClosed K 3 + 15 • gammaClosed K 4
  have he : (gammaClosed K 5 : Ambient K) - (d • c : FClosed (parameter K)) ∈
      exactAmbient (parameter K) := by
    simpa only [c, gammaClosed, Gamma_succ, Submodule.coe_sub, Submodule.coe_add,
      Submodule.coe_smul_of_tower] using sixthPole_difference_exact (parameter K) v d huv hd
  have h := ambientExact_quotient_eq (parameter K) (gammaClosed K 5) (d • c) he
  simp only [c, map_smul, map_sub, map_add, map_nsmul] at h
  exact h

theorem quotientTheta_fifth_column (h6 : IsUnit (6 : K)) :
    quotientTheta K (qGamma K 4) =
      (Parameter.discriminantInverse : Coeff K) •
        (qGamma K 0 - 31 • qGamma K 1 + 90 • qGamma K 2 -
          65 • qGamma K 3 + 15 • qGamma K 4) - 5 • qGamma K 4 := by
  rw [quotientTheta_Gamma, qGamma_six K h6]

end

end WPResidueQuotient.ActualConnection
