import WPToricDual.Connection

noncomputable section

namespace WPToricGamma

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def scaleInv : K p := (3 : K p)⁻¹

def gammaM : Matrix (Fin 3) (Fin 3) (K p) :=
  !![-1 / 2, 0, (1 / 8) * (oneMinus p)⁻¹;
      1, -3 / 2, (-13 / 4) * (oneMinus p)⁻¹;
      0, 1, (9 / 2) * (oneMinus p)⁻¹ - 5 / 2]

def gammaZ : Matrix (Fin 3) (Fin 3) (K p) := scaleInv p • gammaM p

def Tbase : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![1, -1 / 6, 1 / 36; 0, 1 / 3, -2 / 9; 0, 0, 1 / 9]

def T : Matrix (Fin 3) (Fin 3) (K p) :=
  (algebraMap (ZMod p) (K p)).mapMatrix (Tbase p)

def TInverse : Matrix (Fin 3) (Fin 3) (K p) :=
  !![1, 1 / 2, 3 / 4; 0, 3, 6; 0, 0, 9]

theorem T_actual : T p =
    (!![1, -1 / 6, 1 / 36; 0, 1 / 3, -2 / 9; 0, 0, 1 / 9] :
      Matrix (Fin 3) (Fin 3) (K p)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [T, Tbase, map_div₀, map_ofNat]

theorem theta_T : thetaMatrix p (T p) = 0 := by
  apply Matrix.ext
  intro i j
  change theta p (algebraMap (ZMod p) (K p) (Tbase p i j)) = 0
  exact (theta p).map_algebraMap _

theorem T_upper : (T p).IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [T_actual]

theorem det_T (hp7 : 7 ≤ p) : (T p).det = (1 / 27 : K p) := by
  obtain ⟨h2, h3, h6⟩ := field_small_nonzero p hp7
  have h9 : (9 : K p) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h27 : (27 : K p) ≠ 0 := by convert pow_ne_zero 3 h3 using 1; norm_num
  rw [Matrix.det_of_isUpperTriangular (T_upper p)]
  simp [T_actual, Fin.prod_univ_succ]
  field_simp
  ring

theorem det_T_nonzero (hp7 : 7 ≤ p) : (T p).det ≠ 0 := by
  rw [det_T p hp7]
  have h3 : (3 : K p) ≠ 0 := (field_small_nonzero p hp7).2.1
  have h27 : (27 : K p) ≠ 0 := by convert pow_ne_zero 3 h3 using 1; norm_num
  exact div_ne_zero one_ne_zero h27

theorem T_mul_inv (hp7 : 7 ≤ p) : T p * (T p)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_T_nonzero p hp7))

theorem T_inv_mul (hp7 : 7 ≤ p) : (T p)⁻¹ * T p = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (det_T_nonzero p hp7))

theorem TInverse_mul_T (hp7 : 7 ≤ p) : TInverse p * T p = 1 := by
  obtain ⟨h2, h3, h6⟩ := field_small_nonzero p hp7
  have h4 : (4 : K p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h9 : (9 : K p) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h36 : (36 : K p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h3) using 1; norm_num
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [TInverse, T_actual, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring

theorem TInverse_eq_inv (hp7 : 7 ≤ p) : TInverse p = (T p)⁻¹ := by
  calc
    TInverse p = TInverse p * (T p * (T p)⁻¹) := by rw [T_mul_inv p hp7, mul_one]
    _ = (T p)⁻¹ := by rw [← mul_assoc, TInverse_mul_T p hp7, one_mul]

theorem T_mul_TInverse (hp7 : 7 ≤ p) : T p * TInverse p = 1 := by
  rw [TInverse_eq_inv p hp7, T_mul_inv p hp7]

theorem gamma_cyclic_matrix (hp7 : 7 ≤ p) :
    gammaZ p * T p = T p * (fieldN p).transpose := by
  obtain ⟨h2, h3, h6⟩ := field_small_nonzero p hp7
  have h4 : (4 : K p) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h8 : (8 : K p) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  have h9 : (9 : K p) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h36 : (36 : K p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h3) using 1; norm_num
  have h72 : (72 : K p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3) using 1; norm_num
  have hd : oneMinus p ≠ 0 := oneMinus_nonzero p
  have hdLit : (1 - polyMap p Polynomial.X) ≠ 0 := by
    simpa only [oneMinus_literal] using hd
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaZ, gammaM, T_actual, Matrix.mul_apply, Fin.sum_univ_succ,
      fieldN_literal p hp7, scaleInv, oneMinus_literal] <;>
    field_simp <;> ring

end WPToricGamma

