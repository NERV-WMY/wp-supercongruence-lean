import WPDual.Connection

noncomputable section

namespace WPDual

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def dualPsiMatrix : Matrix (Fin 5) (Fin 5) (K p) :=
  -(dualV p * (fieldJ p).transpose * dualVInverse p)

theorem dualPsi_is_matrix (hp7 : 7 ≤ p) :
    dualPsi p = matrixAction p (dualPsiMatrix p) := by
  calc
    dualPsi p = (dualPsi p * dualGauge p) * dualGaugeInverse p := by
      rw [mul_assoc, dualGauge_mul_inverse, mul_one]
    _ = (dualGauge p * (-dualJordan p)) * dualGaugeInverse p := by rw [dualPsi_gauge p hp7]
    _ = matrixAction p (dualPsiMatrix p) := by
      simp only [dualPsiMatrix, dualGauge, dualJordan, dualGaugeInverse, map_neg, map_mul]
      rw [mul_neg (matrixAction p (dualV p)) (matrixAction p (fieldJ p).transpose),
        neg_mul (matrixAction p (dualV p) * matrixAction p (fieldJ p).transpose)
          (matrixAction p (dualVInverse p))]

theorem dualPsiMatrix_negative_transpose :
    dualPsiMatrix p = -(WPState.fieldV p * fieldJ p * (WPState.fieldV p)⁻¹).transpose := by
  rw [dualPsiMatrix, dualV, dualVInverse, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [mul_assoc]

theorem dualPsiMatrix_fifth_zero : dualPsiMatrix p ^ 5 = 0 := by
  rw [dualPsiMatrix_negative_transpose, neg_pow, ← Matrix.transpose_pow,
    pcurvature_matrix_fifth_zero, Matrix.transpose_zero, mul_zero]

theorem dualPsi_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    dualPsi p (a • v) = a • dualPsi p v := by
  rw [dualPsi_is_matrix p hp7]
  change (dualPsiMatrix p).mulVecLin (a • v) = a • (dualPsiMatrix p).mulVecLin v
  exact map_smul _ _ _

def sixTheta : Derivation (ZMod p) (K p) (K p) := (6 : ZMod p) • theta p
def sixEuler : StateEnd p := (6 : ZMod p) • euler p
def sixNabla : StateEnd p := (6 : ZMod p) • dualNabla p
def sixPsi : StateEnd p := sixNabla p ^ p - sixNabla p

theorem six_frobenius : (6 : ZMod p) ^ p = 6 := by
  simpa only [ZMod.card] using FiniteField.pow_card (6 : ZMod p)

theorem six_field_unit (hp7 : 7 ≤ p) : IsUnit (6 : K p) := by
  have hu := WPFiveFactor.six_unit p (Fact.out : p.Prime) hp7
  simpa only [map_ofNat] using hu.map (algebraMap (ZMod p) (K p))

theorem sixTheta_actual_apply (a : K p) : sixTheta p a = (6 : K p) * theta p a := by
  simp only [sixTheta, Derivation.smul_apply, Algebra.smul_def, map_ofNat]

theorem sixTheta_prime_field (a : K p) : (sixTheta p)^[p] a = sixTheta p a := by
  have he : (sixTheta p : K p → K p) =
      ((6 : ZMod p) • (theta p).toLinearMap : Module.End (ZMod p) (K p)) := rfl
  rw [he, ← Module.End.pow_apply, smul_pow, six_frobenius]
  change (6 : ZMod p) • (((theta p).toLinearMap ^ p) a) = _
  rw [Module.End.pow_apply]
  change (6 : ZMod p) • (theta p)^[p] a = _
  rw [theta_prime_field]
  rfl

theorem sixEuler_prime : sixEuler p ^ p = sixEuler p := by
  rw [sixEuler, smul_pow, six_frobenius, euler_prime]

theorem sixNabla_actual_apply (v : StateSpace p) (i : Fin 5) :
    sixNabla p v i = (6 : K p) * (theta p (v i) + ∑ j, fieldN p j i * v j) := by
  change (6 : ZMod p) • (dualNabla p v i) = _
  rw [dualNabla_actual_apply, Algebra.smul_def, map_ofNat]

theorem sixNabla_leibniz (a : K p) (v : StateSpace p) :
    sixNabla p (a • v) = sixTheta p a • v + a • sixNabla p v := by
  change (6 : ZMod p) • dualNabla p (a • v) = _
  rw [dualNabla_leibniz, smul_add]
  change (6 : ZMod p) • (theta p a • v) + (6 : ZMod p) • (a • dualNabla p v) =
    ((6 : ZMod p) • theta p a) • v + a • ((6 : ZMod p) • dualNabla p v)
  rw [smul_assoc, smul_comm (6 : ZMod p) a]

theorem six_pcurvature_scaling : sixPsi p = (6 : ZMod p) • dualPsi p := by
  rw [sixPsi, sixNabla, smul_pow, six_frobenius, dualPsi, smul_sub]

theorem six_pcurvature_fifth_zero (hp7 : 7 ≤ p) : sixPsi p ^ 5 = 0 := by
  rw [six_pcurvature_scaling, smul_pow, dual_pcurvature_fifth_zero p hp7, smul_zero]

theorem actual_six_rescaled_fifth_zero (hp7 : 7 ≤ p) :
    (sixNabla p ^ p - sixNabla p) ^ 5 = 0 := six_pcurvature_fifth_zero p hp7

theorem sixPsi_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    sixPsi p (a • v) = a • sixPsi p v := by
  rw [six_pcurvature_scaling]
  change (6 : ZMod p) • dualPsi p (a • v) = a • ((6 : ZMod p) • dualPsi p v)
  rw [dualPsi_K_linear p hp7, smul_comm]

end WPDual
