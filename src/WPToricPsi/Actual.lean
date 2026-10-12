import WPToricPsi.Connection

noncomputable section

open WPPsi

namespace WPToricPsi

open Polynomial

variable (p : ℕ) [Fact p.Prime]

theorem polyMap_C (a : ZMod p) :
    polyMap p (C a) = algebraMap (ZMod p) (K p) a := by
  change algebraMap (Polynomial (ZMod p)) (K p) (C a) = _
  rfl

theorem oneMinus_literal : oneMinus p = 1 - polyMap p X := by
  simp only [oneMinus, map_sub, map_one]

theorem theta_X : theta p (polyMap p X) = polyMap p X := by
  rw [theta_poly]
  simp [WPRho.theta]

theorem theta_fraction_formula (P Q : Polynomial (ZMod p)) :
    theta p (polyMap p P / polyMap p Q) =
      polyMap p (X * (P.derivative * Q - P * Q.derivative)) / (polyMap p Q) ^ 2 := by
  rw [(theta p).leibniz_div, theta_poly, theta_poly]
  simp only [smul_eq_mul, WPRho.theta, map_mul, map_sub, div_eq_mul_inv, inv_pow]
  ring

theorem fieldN_actual_entry (i j : Fin 3) :
    fieldN p i j = if i.val < 2 then (if j.val = i.val + 1 then 1 else 0)
      else (polyMap p X / oneMinus p) * algebraMap (ZMod p) (K p) (WPToricState.lowerCoeff p j) := by
  by_cases hi : i.val < 2
  · by_cases hj : j.val = i.val + 1
    · simp only [fieldN, fieldNpoly, RingHom.mapMatrix_apply, Matrix.map_apply,
        WPToricState.Npoly, if_pos hi, if_pos hj]
      change (oneMinus p)⁻¹ * oneMinus p = 1
      exact inv_mul_cancel₀ (oneMinus_nonzero p)
    · simp only [fieldN, fieldNpoly, RingHom.mapMatrix_apply, Matrix.map_apply,
        WPToricState.Npoly, if_pos hi, if_neg hj, map_zero, mul_zero]
  · simp only [fieldN, fieldNpoly, RingHom.mapMatrix_apply, Matrix.map_apply,
      WPToricState.Npoly, if_neg hi, map_mul, polyMap_C, div_eq_mul_inv]
    ring

theorem field_small_nonzero (hp7 : 7 ≤ p) : (2 : K p) ≠ 0 ∧ (3 : K p) ≠ 0 ∧ (6 : K p) ≠ 0 := by
  have h6 : (6 : K p) ≠ 0 := isUnit_iff_ne_zero.mp
    (WPRho.mapped_six_unit Fact.out hp7 (algebraMap (ZMod p) (K p)))
  have h23 : (2 : K p) * 3 ≠ 0 := by norm_num; exact h6
  exact ⟨(mul_ne_zero_iff.mp h23).1, (mul_ne_zero_iff.mp h23).2, h6⟩

theorem fieldN_literal (hp7 : 7 ≤ p) :
    fieldN p = !![0, 1, 0; 0, 0, 1;
      (polyMap p X / oneMinus p) * (5 / 72 : K p),
      (polyMap p X / oneMinus p) * (23 / 36 : K p),
      (polyMap p X / oneMinus p) * (3 / 2 : K p)] := by
  obtain ⟨h2, h3, h6⟩ := field_small_nonzero p hp7
  have h36 : (36 : K p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h3) using 1; norm_num
  have h72 : (72 : K p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3) using 1; norm_num
  have hd : oneMinus p ≠ 0 := oneMinus_nonzero p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fieldN_actual_entry, WPToricState.lowerCoeff, map_inv₀, map_ofNat] <;>
    field_simp <;> norm_num

theorem nabla_actual_apply (v : StateSpace p) (i : Fin 3) :
    nabla p v i = theta p (v i) - ∑ j, fieldN p i j * v j := rfl

theorem nabla_leibniz (a : K p) (v : StateSpace p) :
    nabla p (a • v) = theta p a • v + a • nabla p v := by
  funext i
  change theta p (a * v i) - ∑ j, fieldN p i j * (a * v j) =
    theta p a * v i + a * (theta p (v i) - ∑ j, fieldN p i j * v j)
  rw [(theta p).leibniz]
  simp only [smul_eq_mul, mul_sub, Finset.mul_sum]
  have hs : (∑ j, fieldN p i j * (a * v j)) = ∑ j, a * (fieldN p i j * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem pcurvature_is_matrix (hp7 : 7 ≤ p) :
    psi p = matrixAction p (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) := by
  calc
    psi p = (psi p * gauge p) * gaugeInverse p := by
      rw [mul_assoc, gauge_mul_inverse, mul_one]
    _ = (gauge p * jordan p) * gaugeInverse p := by rw [psi_gauge p hp7]
    _ = matrixAction p (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) := by
      simp only [gauge, jordan, gaugeInverse, map_mul]

theorem pcurvature_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    psi p (a • v) = a • psi p v := by
  rw [pcurvature_is_matrix p hp7]
  change (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹).mulVecLin (a • v) =
    a • (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹).mulVecLin v
  exact map_smul _ _ _

theorem pcurvature_matrix_third_zero :
    (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) ^ 3 = 0 := by
  have hu : IsUnit (WPToricState.fieldV p).det :=
    isUnit_iff_ne_zero.mpr (WPToricState.fieldV_det_nonzero p)
  have hi : (WPToricState.fieldV p)⁻¹ * WPToricState.fieldV p = 1 :=
    Matrix.nonsing_inv_mul _ hu
  have hpw : ∀ n : ℕ, (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) ^ n *
      WPToricState.fieldV p = WPToricState.fieldV p * fieldJ p ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih]
      calc
        (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) *
            (WPToricState.fieldV p * fieldJ p ^ n) =
          WPToricState.fieldV p * fieldJ p * ((WPToricState.fieldV p)⁻¹ * WPToricState.fieldV p) *
            fieldJ p ^ n := by simp only [mul_assoc]
        _ = WPToricState.fieldV p * fieldJ p ^ (n + 1) := by
          rw [hi, mul_one, mul_assoc, ← pow_succ']
  calc
    (WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) ^ 3 =
        ((WPToricState.fieldV p * fieldJ p * (WPToricState.fieldV p)⁻¹) ^ 3 * WPToricState.fieldV p) *
          (WPToricState.fieldV p)⁻¹ := by
            simp only [mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]
    _ = (WPToricState.fieldV p * fieldJ p ^ 3) * (WPToricState.fieldV p)⁻¹ := by rw [hpw]
    _ = 0 := by rw [fieldJ_third_zero, mul_zero, zero_mul]

end WPToricPsi


