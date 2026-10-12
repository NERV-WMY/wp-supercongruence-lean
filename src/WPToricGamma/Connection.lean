import WPToricGamma.Matrix

noncomputable section

namespace WPToricGamma

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def tripleEuler : StateEnd p := (3 : ZMod p) • euler p

theorem triple_frobenius : (3 : ZMod p) ^ p = 3 := by
  simpa only [ZMod.card] using FiniteField.pow_card (3 : ZMod p)

theorem tripleEuler_prime : tripleEuler p ^ p = tripleEuler p := by
  rw [tripleEuler, smul_pow, triple_frobenius, euler_prime]

def gammaNabla : StateEnd p := euler p + matrixAction p (gammaZ p)
def gammaGauge : StateEnd p := matrixAction p (T p)
def gammaGaugeInverse : StateEnd p := matrixAction p ((T p)⁻¹)
def gammaPsi : StateEnd p := gammaNabla p ^ p - gammaNabla p
def gammaU : StateEnd p := (3 : ZMod p) • gammaNabla p
def gammaUPsi : StateEnd p := gammaU p ^ p - gammaU p

theorem gammaNabla_actual_apply (v : StateSpace p) (i : Fin 3) :
    gammaNabla p v i = theta p (v i) + ∑ j, gammaZ p i j * v j := rfl

theorem gammaNabla_gauge (hp7 : 7 ≤ p) :
    gammaNabla p * gammaGauge p = gammaGauge p * WPToricDual.dualNabla p := by
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
    gammaGaugeInverse p * gammaNabla p * gammaGauge p = WPToricDual.dualNabla p := by
  rw [mul_assoc, gammaNabla_gauge p hp7, ← mul_assoc, gammaGauge_inverse_mul p hp7, one_mul]

theorem gammaNabla_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    gammaNabla p ^ n * gammaGauge p = gammaGauge p * WPToricDual.dualNabla p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, gammaNabla_gauge p hp7, mul_assoc, ← pow_succ']

theorem gammaPsi_gauge (hp7 : 7 ≤ p) :
    gammaPsi p * gammaGauge p = gammaGauge p * WPToricDual.dualPsi p := by
  rw [gammaPsi, sub_mul, gammaNabla_pow_gauge p hp7, gammaNabla_gauge p hp7,
    ← mul_sub, WPToricDual.dualPsi]

theorem gamma_pcurvature_conjugation (hp7 : 7 ≤ p) :
    gammaGaugeInverse p * gammaPsi p * gammaGauge p = WPToricDual.dualPsi p := by
  rw [mul_assoc, gammaPsi_gauge p hp7, ← mul_assoc, gammaGauge_inverse_mul p hp7, one_mul]

theorem gammaPsi_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    gammaPsi p ^ n * gammaGauge p = gammaGauge p * WPToricDual.dualPsi p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, gammaPsi_gauge p hp7, mul_assoc, ← pow_succ']

theorem gamma_pcurvature_third_zero (hp7 : 7 ≤ p) : gammaPsi p ^ 3 = 0 := by
  calc
    gammaPsi p ^ 3 = (gammaPsi p ^ 3 * gammaGauge p) * gammaGaugeInverse p := by
      rw [mul_assoc, gammaGauge_mul_inverse p hp7, mul_one]
    _ = (gammaGauge p * WPToricDual.dualPsi p ^ 3) * gammaGaugeInverse p := by
      rw [gammaPsi_pow_gauge p hp7]
    _ = 0 := by rw [WPToricDual.dual_pcurvature_third_zero p hp7, mul_zero, zero_mul]

theorem actual_gamma_field_third_zero (hp7 : 7 ≤ p) :
    (gammaNabla p ^ p - gammaNabla p) ^ 3 = 0 := gamma_pcurvature_third_zero p hp7

theorem gammaU_actual (hp7 : 7 ≤ p) : gammaU p = tripleEuler p + matrixAction p (gammaM p) := by
  have h3 : (3 : K p) ≠ 0 := (field_small_nonzero p hp7).2.1
  apply LinearMap.ext
  intro v
  funext i
  change (3 : ZMod p) • (theta p (v i) + ∑ j, (scaleInv p * gammaM p i j) * v j) =
    (3 : ZMod p) • theta p (v i) + ∑ j, gammaM p i j * v j
  rw [Algebra.smul_def, Algebra.smul_def, map_ofNat, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scaleInv]
  calc
    (3 : K p) * ((3 : K p)⁻¹ * gammaM p i j * v j) =
        ((3 : K p) * (3 : K p)⁻¹) * (gammaM p i j * v j) := by ring
    _ = _ := by rw [mul_inv_cancel₀ h3, one_mul]

theorem gamma_triple_pcurvature_scaling : gammaUPsi p = (3 : ZMod p) • gammaPsi p := by
  rw [gammaUPsi, gammaU, smul_pow, triple_frobenius, gammaPsi, smul_sub]

theorem actual_gamma_u_field_third_zero (hp7 : 7 ≤ p) :
    (gammaU p ^ p - gammaU p) ^ 3 = 0 := by
  change gammaUPsi p ^ 3 = 0
  rw [gamma_triple_pcurvature_scaling, smul_pow, gamma_pcurvature_third_zero p hp7, smul_zero]

end WPToricGamma


