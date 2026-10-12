import WPToricPsi.Actual

noncomputable section

namespace WPToricDual

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def dualV : Matrix (Fin 3) (Fin 3) (K p) := ((WPToricState.fieldV p)⁻¹).transpose
def dualVInverse : Matrix (Fin 3) (Fin 3) (K p) := (WPToricState.fieldV p).transpose

theorem thetaMatrix_mul (A B : Matrix (Fin 3) (Fin 3) (K p)) :
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

theorem thetaMatrix_transpose (A : Matrix (Fin 3) (Fin 3) (K p)) :
    thetaMatrix p A.transpose = (thetaMatrix p A).transpose := rfl

theorem thetaMatrix_one : thetaMatrix p (1 : Matrix (Fin 3) (Fin 3) (K p)) = 0 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [thetaMatrix, Matrix.one_apply, h]

theorem fieldV_inv_mul : (WPToricState.fieldV p)⁻¹ * WPToricState.fieldV p = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (WPToricState.fieldV_det_nonzero p))

theorem fieldV_mul_inv : WPToricState.fieldV p * (WPToricState.fieldV p)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (WPToricState.fieldV_det_nonzero p))

theorem thetaMatrix_fieldV_inverse :
    thetaMatrix p ((WPToricState.fieldV p)⁻¹) =
      -((WPToricState.fieldV p)⁻¹ * thetaMatrix p (WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹) := by
  have hz : thetaMatrix p (WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹ +
      WPToricState.fieldV p * thetaMatrix p ((WPToricState.fieldV p)⁻¹) = 0 := by
    rw [← thetaMatrix_mul, fieldV_mul_inv, thetaMatrix_one]
  have he : WPToricState.fieldV p * thetaMatrix p ((WPToricState.fieldV p)⁻¹) =
      -(thetaMatrix p (WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹) := by
    calc
      WPToricState.fieldV p * thetaMatrix p ((WPToricState.fieldV p)⁻¹) =
          (thetaMatrix p (WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹ +
            WPToricState.fieldV p * thetaMatrix p ((WPToricState.fieldV p)⁻¹)) -
              thetaMatrix p (WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹ := by abel
      _ = _ := by rw [hz]; simp
  calc
    thetaMatrix p ((WPToricState.fieldV p)⁻¹) =
        (WPToricState.fieldV p)⁻¹ * (WPToricState.fieldV p * thetaMatrix p ((WPToricState.fieldV p)⁻¹)) := by
          rw [← mul_assoc, fieldV_inv_mul, one_mul]
    _ = _ := by rw [he, mul_neg, mul_assoc]

theorem inverse_field_gauge (hp7 : 7 ≤ p) :
    thetaMatrix p ((WPToricState.fieldV p)⁻¹) =
      fieldJ p * (WPToricState.fieldV p)⁻¹ - (WPToricState.fieldV p)⁻¹ * fieldN p := by
  rw [thetaMatrix_fieldV_inverse, field_gauge_equation p hp7]
  have hleft : (WPToricState.fieldV p)⁻¹ * (fieldN p * WPToricState.fieldV p) * (WPToricState.fieldV p)⁻¹ =
      (WPToricState.fieldV p)⁻¹ * fieldN p := by
    calc
      _ = ((WPToricState.fieldV p)⁻¹ * fieldN p) * (WPToricState.fieldV p * (WPToricState.fieldV p)⁻¹) := by
        simp only [mul_assoc]
      _ = _ := by rw [fieldV_mul_inv, mul_one]
  have hright : (WPToricState.fieldV p)⁻¹ * (WPToricState.fieldV p * fieldJ p) * (WPToricState.fieldV p)⁻¹ =
      fieldJ p * (WPToricState.fieldV p)⁻¹ := by
    rw [← mul_assoc ((WPToricState.fieldV p)⁻¹) (WPToricState.fieldV p), fieldV_inv_mul, one_mul]
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

end WPToricDual

