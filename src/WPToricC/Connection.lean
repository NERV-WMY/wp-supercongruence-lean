import WPToricC.Gauge

noncomputable section

namespace WPToricC

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def cJordan : StateEnd p := matrixAction p (cJ p)
def cGauge (hp7 : 7 ≤ p) : StateEnd p := matrixAction p (cG p hp7)
def cGaugeInverse (hp7 : 7 ≤ p) : StateEnd p := matrixAction p (cGInverse p hp7)
def cNabla (hp7 : 7 ≤ p) : StateEnd p := euler p + matrixAction p (cM p hp7)
def cModel : StateEnd p := euler p + cJordan p
def cPsi (hp7 : 7 ≤ p) : StateEnd p := cNabla p hp7 ^ p - cNabla p hp7

theorem cJordan_third_zero : cJordan p ^ 3 = 0 := by
  rw [cJordan, ← map_pow, cJ_third_zero, map_zero]

theorem cJordan_prime_zero (hp7 : 7 ≤ p) : cJordan p ^ p = 0 := by
  have he : p = (p - 3) + 3 := by omega
  calc
    cJordan p ^ p = cJordan p ^ ((p - 3) + 3) := congrArg (fun n => cJordan p ^ n) he
    _ = 0 := by rw [pow_add, cJordan_third_zero, mul_zero]

theorem euler_cJordan_commute : Commute (euler p) (cJordan p) := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (cJ p) v) = matrixAction p (cJ p) (euler p v)
  rw [euler_matrixAction, theta_cJ, map_zero, LinearMap.zero_apply, zero_add]

theorem cNabla_actual_apply (hp7 : 7 ≤ p) (v : StateSpace p) (i : Fin 3) :
    cNabla p hp7 v i = theta p (v i) + ∑ j, cM p hp7 i j * v j := rfl

theorem cNabla_gauge (hp7 : 7 ≤ p) :
    cNabla p hp7 * cGauge p hp7 = cGauge p hp7 * cModel p := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (cG p hp7) v) +
      matrixAction p (cM p hp7) (matrixAction p (cG p hp7) v) =
    matrixAction p (cG p hp7) (euler p v + matrixAction p (cJ p) v)
  rw [euler_matrixAction, c_matrix_gauge, map_sub]
  simp only [LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_add]
  abel

theorem cGauge_inverse_mul (hp7 : 7 ≤ p) :
    cGaugeInverse p hp7 * cGauge p hp7 = 1 := by
  rw [cGaugeInverse, cGauge, ← map_mul, cG_inverse_mul, map_one]

theorem cGauge_mul_inverse (hp7 : 7 ≤ p) :
    cGauge p hp7 * cGaugeInverse p hp7 = 1 := by
  rw [cGaugeInverse, cGauge, ← map_mul, cG_mul_inverse, map_one]

theorem c_connection_conjugation (hp7 : 7 ≤ p) :
    cGaugeInverse p hp7 * cNabla p hp7 * cGauge p hp7 = cModel p := by
  rw [mul_assoc, cNabla_gauge, ← mul_assoc, cGauge_inverse_mul, one_mul]

theorem cNabla_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    cNabla p hp7 ^ n * cGauge p hp7 = cGauge p hp7 * cModel p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, cNabla_gauge, mul_assoc, ← pow_succ']

theorem cModel_prime (hp7 : 7 ≤ p) : cModel p ^ p = euler p := by
  rw [cModel, add_pow_char_of_commute p (euler_cJordan_commute p),
    euler_prime, cJordan_prime_zero p hp7, add_zero]

theorem cPsi_gauge (hp7 : 7 ≤ p) :
    cPsi p hp7 * cGauge p hp7 = cGauge p hp7 * (-cJordan p) := by
  rw [cPsi, sub_mul, cNabla_pow_gauge, cNabla_gauge,
    cModel_prime p hp7, ← mul_sub, cModel]
  congr 1
  abel

theorem c_pcurvature_conjugation (hp7 : 7 ≤ p) :
    cGaugeInverse p hp7 * cPsi p hp7 * cGauge p hp7 = -cJordan p := by
  rw [mul_assoc, cPsi_gauge, ← mul_assoc, cGauge_inverse_mul, one_mul]

theorem cPsi_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    cPsi p hp7 ^ n * cGauge p hp7 = cGauge p hp7 * (-cJordan p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, cPsi_gauge, mul_assoc, ← pow_succ']

theorem c_pcurvature_third_zero (hp7 : 7 ≤ p) : cPsi p hp7 ^ 3 = 0 := by
  calc
    cPsi p hp7 ^ 3 = (cPsi p hp7 ^ 3 * cGauge p hp7) * cGaugeInverse p hp7 := by
      rw [mul_assoc, cGauge_mul_inverse, mul_one]
    _ = (cGauge p hp7 * (-cJordan p) ^ 3) * cGaugeInverse p hp7 := by
      rw [cPsi_pow_gauge]
    _ = 0 := by
      rw [neg_pow (cJordan p) 3, cJordan_third_zero, mul_zero, mul_zero, zero_mul]

theorem actual_c_field_third_zero (hp7 : 7 ≤ p) :
    (cNabla p hp7 ^ p - cNabla p hp7) ^ 3 = 0 := c_pcurvature_third_zero p hp7

theorem cPsi_is_matrix (hp7 : 7 ≤ p) :
    cPsi p hp7 = matrixAction p (cG p hp7 * (-cJ p) * cGInverse p hp7) := by
  calc
    cPsi p hp7 = (cPsi p hp7 * cGauge p hp7) * cGaugeInverse p hp7 := by
      rw [mul_assoc, cGauge_mul_inverse, mul_one]
    _ = (cGauge p hp7 * (-cJordan p)) * cGaugeInverse p hp7 := by rw [cPsi_gauge]
    _ = matrixAction p (cG p hp7 * (-cJ p) * cGInverse p hp7) := by
      simp only [cGauge, cJordan, cGaugeInverse, map_mul, map_neg]

theorem cPsi_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    cPsi p hp7 (a • v) = a • cPsi p hp7 v := by
  rw [cPsi_is_matrix]
  change (cG p hp7 * (-cJ p) * cGInverse p hp7).mulVecLin (a • v) =
    a • (cG p hp7 * (-cJ p) * cGInverse p hp7).mulVecLin v
  exact map_smul _ _ _

end WPToricC
