import WPGamma.Conversion

noncomputable section

namespace WPGamma

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def gammaNabla : StateEnd p := euler p + matrixAction p (gammaZ p)
def gammaGauge : StateEnd p := matrixAction p (T p)
def gammaGaugeInverse : StateEnd p := matrixAction p ((T p)⁻¹)
def gammaPsi : StateEnd p := gammaNabla p ^ p - gammaNabla p
def gammaU : StateEnd p := (6 : ZMod p) • gammaNabla p
def gammaUPsi : StateEnd p := gammaU p ^ p - gammaU p

theorem gammaNabla_actual_apply (v : StateSpace p) (i : Fin 5) :
    gammaNabla p v i = theta p (v i) + ∑ j, gammaZ p i j * v j := rfl

theorem gammaNabla_gauge (hp7 : 7 ≤ p) :
    gammaNabla p * gammaGauge p = gammaGauge p * WPDual.dualNabla p := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (T p) v) +
      matrixAction p (gammaZ p) (matrixAction p (T p) v) =
    matrixAction p (T p) (euler p v + matrixAction p (fieldN p).transpose v)
  rw [euler_matrixAction, theta_T, map_zero, LinearMap.zero_apply, zero_add]
  have hm := congrArg (matrixAction p) (gamma_cyclic_matrix p hp7)
  simp only [map_mul] at hm
  have hv := LinearMap.congr_fun hm v
  change matrixAction p (gammaZ p) (matrixAction p (T p) v) =
    matrixAction p (T p) (matrixAction p (fieldN p).transpose v) at hv
  rw [hv, map_add]

theorem gammaGauge_inverse_mul (hp7 : 7 ≤ p) : gammaGaugeInverse p * gammaGauge p = 1 := by
  rw [gammaGaugeInverse, gammaGauge, ← map_mul, T_inv_mul p hp7, map_one]

theorem gammaGauge_mul_inverse (hp7 : 7 ≤ p) : gammaGauge p * gammaGaugeInverse p = 1 := by
  rw [gammaGaugeInverse, gammaGauge, ← map_mul, T_mul_inv p hp7, map_one]

theorem gamma_connection_conjugation (hp7 : 7 ≤ p) :
    gammaGaugeInverse p * gammaNabla p * gammaGauge p = WPDual.dualNabla p := by
  rw [mul_assoc, gammaNabla_gauge p hp7, ← mul_assoc, gammaGauge_inverse_mul p hp7, one_mul]

theorem gammaNabla_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    gammaNabla p ^ n * gammaGauge p = gammaGauge p * WPDual.dualNabla p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, gammaNabla_gauge p hp7, mul_assoc, ← pow_succ']

theorem gammaPsi_gauge (hp7 : 7 ≤ p) :
    gammaPsi p * gammaGauge p = gammaGauge p * WPDual.dualPsi p := by
  rw [gammaPsi, sub_mul, gammaNabla_pow_gauge p hp7, gammaNabla_gauge p hp7,
    ← mul_sub, WPDual.dualPsi]

theorem gamma_pcurvature_conjugation (hp7 : 7 ≤ p) :
    gammaGaugeInverse p * gammaPsi p * gammaGauge p = WPDual.dualPsi p := by
  rw [mul_assoc, gammaPsi_gauge p hp7, ← mul_assoc, gammaGauge_inverse_mul p hp7, one_mul]

theorem gammaPsi_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    gammaPsi p ^ n * gammaGauge p = gammaGauge p * WPDual.dualPsi p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, gammaPsi_gauge p hp7, mul_assoc, ← pow_succ']

theorem gamma_pcurvature_fifth_zero (hp7 : 7 ≤ p) : gammaPsi p ^ 5 = 0 := by
  calc
    gammaPsi p ^ 5 = (gammaPsi p ^ 5 * gammaGauge p) * gammaGaugeInverse p := by
      rw [mul_assoc, gammaGauge_mul_inverse p hp7, mul_one]
    _ = (gammaGauge p * WPDual.dualPsi p ^ 5) * gammaGaugeInverse p := by
      rw [gammaPsi_pow_gauge p hp7]
    _ = 0 := by rw [WPDual.dual_pcurvature_fifth_zero p hp7, mul_zero, zero_mul]

theorem actual_gamma_field_fifth_zero (hp7 : 7 ≤ p) :
    (gammaNabla p ^ p - gammaNabla p) ^ 5 = 0 := gamma_pcurvature_fifth_zero p hp7

theorem gammaU_actual (hp7 : 7 ≤ p) : gammaU p = WPDual.sixEuler p + matrixAction p (gammaM p) := by
  have h6 : (6 : K p) ≠ 0 := isUnit_iff_ne_zero.mp (WPDual.six_field_unit p hp7)
  apply LinearMap.ext
  intro v
  funext i
  change (6 : ZMod p) • (theta p (v i) + ∑ j, (q p * gammaM p i j) * v j) =
    (6 : ZMod p) • theta p (v i) + ∑ j, gammaM p i j * v j
  rw [Algebra.smul_def, Algebra.smul_def, map_ofNat, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [q]
  calc
    (6 : K p) * ((6 : K p)⁻¹ * gammaM p i j * v j) =
        ((6 : K p) * (6 : K p)⁻¹) * (gammaM p i j * v j) := by ring
    _ = _ := by rw [mul_inv_cancel₀ h6, one_mul]

theorem gamma_six_pcurvature_scaling : gammaUPsi p = (6 : ZMod p) • gammaPsi p := by
  rw [gammaUPsi, gammaU, smul_pow, WPDual.six_frobenius, gammaPsi, smul_sub]

theorem actual_gamma_u_field_fifth_zero (hp7 : 7 ≤ p) :
    (gammaU p ^ p - gammaU p) ^ 5 = 0 := by
  change gammaUPsi p ^ 5 = 0
  rw [gamma_six_pcurvature_scaling, smul_pow, gamma_pcurvature_fifth_zero p hp7, smul_zero]

end WPGamma
