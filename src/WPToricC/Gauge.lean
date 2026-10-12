import WPToricC.Substitution

noncomputable section

namespace WPToricC

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def sourceG : Matrix (Fin 3) (Fin 3) (K p) :=
  WPToricGamma.T p * WPToricDual.dualV p

def sourceGInverse : Matrix (Fin 3) (Fin 3) (K p) :=
  WPToricDual.dualVInverse p * WPToricGamma.TInverse p

theorem sourceG_inverse_mul (hp7 : 7 ≤ p) : sourceGInverse p * sourceG p = 1 := by
  unfold sourceGInverse sourceG
  calc
    _ = WPToricDual.dualVInverse p *
        (WPToricGamma.TInverse p * WPToricGamma.T p) * WPToricDual.dualV p := by
      simp only [mul_assoc]
    _ = 1 := by rw [WPToricGamma.TInverse_mul_T p hp7, mul_one,
      WPToricDual.dualV_inverse_mul]

theorem sourceG_mul_inverse (hp7 : 7 ≤ p) : sourceG p * sourceGInverse p = 1 := by
  unfold sourceGInverse sourceG
  calc
    _ = WPToricGamma.T p *
        (WPToricDual.dualV p * WPToricDual.dualVInverse p) * WPToricGamma.TInverse p := by
      simp only [mul_assoc]
    _ = 1 := by rw [WPToricDual.dualV_mul_inverse, mul_one,
      WPToricGamma.T_mul_TInverse p hp7]

theorem source_matrix_gauge (hp7 : 7 ≤ p) :
    thetaMatrix p (sourceG p) = sourceG p * (fieldJ p).transpose -
      WPToricGamma.gammaZ p * sourceG p := by
  rw [sourceG, WPToricDual.thetaMatrix_mul, WPToricGamma.theta_T,
    zero_mul, zero_add, WPToricDual.dual_matrix_gauge p hp7, mul_sub]
  simp only [← mul_assoc]
  rw [WPToricGamma.gamma_cyclic_matrix p hp7]

def sigmaMatrix (hp7 : 7 ≤ p) :
    Matrix (Fin 3) (Fin 3) (K p) →+* Matrix (Fin 3) (Fin 3) (K p) :=
  (sigma p hp7).mapMatrix

def cM (hp7 : 7 ≤ p) : Matrix (Fin 3) (Fin 3) (K p) :=
  sigmaMatrix p hp7 (WPToricGamma.gammaM p)

def cG (hp7 : 7 ≤ p) : Matrix (Fin 3) (Fin 3) (K p) :=
  sigmaMatrix p hp7 (sourceG p)

def cGInverse (hp7 : 7 ≤ p) : Matrix (Fin 3) (Fin 3) (K p) :=
  sigmaMatrix p hp7 (sourceGInverse p)

def cJ : Matrix (Fin 3) (Fin 3) (K p) := (3 : K p) • (fieldJ p).transpose

theorem sigmaMatrix_apply (hp7 : 7 ≤ p) (M : Matrix (Fin 3) (Fin 3) (K p))
    (i j : Fin 3) : sigmaMatrix p hp7 M i j = sigma p hp7 (M i j) := rfl

theorem sigmaMatrix_fieldJ (hp7 : 7 ≤ p) :
    sigmaMatrix p hp7 (fieldJ p).transpose = (fieldJ p).transpose := by
  apply Matrix.ext
  intro i j
  change sigma p hp7 (fieldJ p j i) = fieldJ p j i
  rw [fieldJ_entry, sigma_base]

theorem sigmaMatrix_gammaZ (hp7 : 7 ≤ p) :
    sigmaMatrix p hp7 (WPToricGamma.gammaZ p) = (3 : K p)⁻¹ • cM p hp7 := by
  apply Matrix.ext
  intro i j
  change sigma p hp7 ((3 : K p)⁻¹ * WPToricGamma.gammaM p i j) =
    (3 : K p)⁻¹ * sigma p hp7 (WPToricGamma.gammaM p i j)
  rw [map_mul, map_inv₀, map_ofNat]

theorem theta_sigmaMatrix (hp7 : 7 ≤ p) (M : Matrix (Fin 3) (Fin 3) (K p)) :
    thetaMatrix p (sigmaMatrix p hp7 M) = (3 : K p) • sigmaMatrix p hp7 (thetaMatrix p M) := by
  apply Matrix.ext
  intro i j
  exact theta_sigma p hp7 (M i j)

theorem cG_inverse_mul (hp7 : 7 ≤ p) : cGInverse p hp7 * cG p hp7 = 1 := by
  rw [cGInverse, cG, ← map_mul, sourceG_inverse_mul p hp7, map_one]

theorem cG_mul_inverse (hp7 : 7 ≤ p) : cG p hp7 * cGInverse p hp7 = 1 := by
  rw [cGInverse, cG, ← map_mul, sourceG_mul_inverse p hp7, map_one]

theorem cG_det_nonzero (hp7 : 7 ≤ p) : (cG p hp7).det ≠ 0 := by
  have he := congrArg Matrix.det (cG_inverse_mul p hp7)
  rw [Matrix.det_mul, Matrix.det_one] at he
  intro hz
  rw [hz, mul_zero] at he
  exact zero_ne_one he

theorem cGInverse_eq_inv (hp7 : 7 ≤ p) : cGInverse p hp7 = (cG p hp7)⁻¹ := by
  have hu : IsUnit (cG p hp7).det := isUnit_iff_ne_zero.mpr (cG_det_nonzero p hp7)
  calc
    cGInverse p hp7 = cGInverse p hp7 * (cG p hp7 * (cG p hp7)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hu, mul_one]
    _ = (cG p hp7)⁻¹ := by rw [← mul_assoc, cG_inverse_mul p hp7, one_mul]

theorem c_matrix_gauge (hp7 : 7 ≤ p) :
    thetaMatrix p (cG p hp7) = cG p hp7 * cJ p - cM p hp7 * cG p hp7 := by
  rw [cG, theta_sigmaMatrix, source_matrix_gauge p hp7, map_sub, map_mul, map_mul,
    sigmaMatrix_fieldJ, sigmaMatrix_gammaZ, smul_sub]
  have h3 : (3 : K p) ≠ 0 := (field_small_nonzero p hp7).2.1
  have he : (3 : K p) • (((3 : K p)⁻¹ • cM p hp7) * sigmaMatrix p hp7 (sourceG p)) =
      cM p hp7 * sigmaMatrix p hp7 (sourceG p) := by
    rw [Matrix.smul_mul, smul_smul, mul_inv_cancel₀ h3, one_smul]
  rw [he]
  congr 1
  rw [cJ, Matrix.mul_smul]

theorem cJ_third_zero : cJ p ^ 3 = 0 := by
  rw [cJ, smul_pow, ← Matrix.transpose_pow, fieldJ_third_zero,
    Matrix.transpose_zero, smul_zero]

theorem theta_cJ : thetaMatrix p (cJ p) = 0 := by
  apply Matrix.ext
  intro i j
  change theta p (3 * fieldJ p j i) = 0
  have h3 : theta p (3 : K p) = 0 := by
    simpa only [map_ofNat] using (theta p).map_algebraMap (3 : ZMod p)
  rw [(theta p).leibniz]
  simp [theta_fieldJ, smul_eq_mul, h3]

theorem cM_literal (hp7 : 7 ≤ p) : cM p hp7 =
    !![-1 / 2, 0, (1 / 8) * (1 - 27 * c p ^ 3)⁻¹;
        1, -3 / 2, (-13 / 4) * (1 - 27 * c p ^ 3)⁻¹;
        0, 1, (9 / 2) * (1 - 27 * c p ^ 3)⁻¹ - 5 / 2] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cM, sigmaMatrix_apply, WPToricGamma.gammaM, map_div₀, map_ofNat, sigma_oneMinus]

end WPToricC
