import WPPsi

noncomputable section

namespace WPDual

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def dualV : Matrix (Fin 5) (Fin 5) (K p) := ((WPState.fieldV p)⁻¹).transpose
def dualVInverse : Matrix (Fin 5) (Fin 5) (K p) := (WPState.fieldV p).transpose

theorem thetaMatrix_mul (A B : Matrix (Fin 5) (Fin 5) (K p)) :
    thetaMatrix p (A * B) = thetaMatrix p A * B + A * thetaMatrix p B := by
  apply Matrix.ext
  intro i j
  change theta p (∑ k, A i k * B k j) =
    (∑ k, theta p (A i k) * B k j) + ∑ k, A i k * theta p (B k j)
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [(theta p).leibniz]
  simp only [smul_eq_mul]
  ring

theorem thetaMatrix_transpose (A : Matrix (Fin 5) (Fin 5) (K p)) :
    thetaMatrix p A.transpose = (thetaMatrix p A).transpose := rfl

theorem thetaMatrix_one : thetaMatrix p (1 : Matrix (Fin 5) (Fin 5) (K p)) = 0 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [thetaMatrix, Matrix.one_apply, h]

theorem fieldV_inv_mul : (WPState.fieldV p)⁻¹ * WPState.fieldV p = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (WPState.fieldV_det_nonzero p))

theorem fieldV_mul_inv : WPState.fieldV p * (WPState.fieldV p)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (WPState.fieldV_det_nonzero p))

theorem thetaMatrix_fieldV_inverse :
    thetaMatrix p ((WPState.fieldV p)⁻¹) =
      -((WPState.fieldV p)⁻¹ * thetaMatrix p (WPState.fieldV p) * (WPState.fieldV p)⁻¹) := by
  have hz : thetaMatrix p (WPState.fieldV p) * (WPState.fieldV p)⁻¹ +
      WPState.fieldV p * thetaMatrix p ((WPState.fieldV p)⁻¹) = 0 := by
    rw [← thetaMatrix_mul, fieldV_mul_inv, thetaMatrix_one]
  have he : WPState.fieldV p * thetaMatrix p ((WPState.fieldV p)⁻¹) =
      -(thetaMatrix p (WPState.fieldV p) * (WPState.fieldV p)⁻¹) := by
    calc
      WPState.fieldV p * thetaMatrix p ((WPState.fieldV p)⁻¹) =
          (thetaMatrix p (WPState.fieldV p) * (WPState.fieldV p)⁻¹ +
            WPState.fieldV p * thetaMatrix p ((WPState.fieldV p)⁻¹)) -
              thetaMatrix p (WPState.fieldV p) * (WPState.fieldV p)⁻¹ := by abel
      _ = _ := by rw [hz]; simp
  calc
    thetaMatrix p ((WPState.fieldV p)⁻¹) =
        (WPState.fieldV p)⁻¹ * (WPState.fieldV p * thetaMatrix p ((WPState.fieldV p)⁻¹)) := by
          rw [← mul_assoc, fieldV_inv_mul, one_mul]
    _ = _ := by rw [he, mul_neg, mul_assoc]

theorem inverse_field_gauge (hp7 : 7 ≤ p) :
    thetaMatrix p ((WPState.fieldV p)⁻¹) =
      fieldJ p * (WPState.fieldV p)⁻¹ - (WPState.fieldV p)⁻¹ * fieldN p := by
  rw [thetaMatrix_fieldV_inverse, field_gauge_equation p hp7]
  have hleft : (WPState.fieldV p)⁻¹ * (fieldN p * WPState.fieldV p) * (WPState.fieldV p)⁻¹ =
      (WPState.fieldV p)⁻¹ * fieldN p := by
    calc
      _ = ((WPState.fieldV p)⁻¹ * fieldN p) * (WPState.fieldV p * (WPState.fieldV p)⁻¹) := by
        simp only [mul_assoc]
      _ = _ := by rw [fieldV_mul_inv, mul_one]
  have hright : (WPState.fieldV p)⁻¹ * (WPState.fieldV p * fieldJ p) * (WPState.fieldV p)⁻¹ =
      fieldJ p * (WPState.fieldV p)⁻¹ := by
    rw [← mul_assoc ((WPState.fieldV p)⁻¹) (WPState.fieldV p), fieldV_inv_mul, one_mul]
  rw [mul_sub, sub_mul, hleft, hright, neg_sub]

theorem dual_matrix_gauge (hp7 : 7 ≤ p) :
    thetaMatrix p (dualV p) =
      dualV p * (fieldJ p).transpose - (fieldN p).transpose * dualV p := by
  rw [dualV, thetaMatrix_transpose, inverse_field_gauge p hp7,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]

theorem dualV_inverse_mul : dualVInverse p * dualV p = 1 := by
  rw [dualVInverse, dualV, ← Matrix.transpose_mul, fieldV_inv_mul, Matrix.transpose_one]

theorem dualV_mul_inverse : dualV p * dualVInverse p = 1 := by
  rw [dualVInverse, dualV, ← Matrix.transpose_mul, fieldV_mul_inv, Matrix.transpose_one]

end WPDual
