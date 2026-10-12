import WPDual.Gauge

noncomputable section

namespace WPDual

open WPPsi

variable (p : ℕ) [Fact p.Prime]

def dualJordan : StateEnd p := matrixAction p (fieldJ p).transpose
def dualGauge : StateEnd p := matrixAction p (dualV p)
def dualGaugeInverse : StateEnd p := matrixAction p (dualVInverse p)
def dualNabla : StateEnd p := euler p + matrixAction p (fieldN p).transpose
def dualModel : StateEnd p := euler p + dualJordan p
def dualPsi : StateEnd p := dualNabla p ^ p - dualNabla p

def pairing (v w : StateSpace p) : K p := dotProduct v w

theorem euler_pairing (v w : StateSpace p) :
    theta p (pairing p v w) = pairing p (euler p v) w + pairing p v (euler p w) := by
  change theta p (∑ i, v i * w i) =
    (∑ i, theta p (v i) * w i) + ∑ i, v i * theta p (w i)
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [(theta p).leibniz]
  simp only [smul_eq_mul]
  ring

theorem matrix_pairing (M : Matrix (Fin 5) (Fin 5) (K p)) (v w : StateSpace p) :
    pairing p (matrixAction p M v) w = pairing p v (matrixAction p M.transpose w) := by
  change dotProduct (M.mulVec v) w = dotProduct v (M.transpose.mulVec w)
  rw [dotProduct_comm (M.mulVec v) w]
  exact (Matrix.dotProduct_transpose_mulVec M v w).symm

theorem actual_dual_pairing (v w : StateSpace p) :
    theta p (pairing p v w) = pairing p (nabla p v) w + pairing p v (dualNabla p w) := by
  change theta p (pairing p v w) =
    pairing p (euler p v - matrixAction p (fieldN p) v) w +
      pairing p v (euler p w + matrixAction p (fieldN p).transpose w)
  rw [euler_pairing]
  simp only [pairing, sub_dotProduct, dotProduct_add]
  have he := matrix_pairing p (fieldN p) v w
  change dotProduct (matrixAction p (fieldN p) v) w =
    dotProduct v (matrixAction p (fieldN p).transpose w) at he
  rw [he]
  abel

theorem dualNabla_actual_apply (v : StateSpace p) (i : Fin 5) :
    dualNabla p v i = theta p (v i) + ∑ j, fieldN p j i * v j := rfl

theorem dualNabla_leibniz (a : K p) (v : StateSpace p) :
    dualNabla p (a • v) = theta p a • v + a • dualNabla p v := by
  funext i
  change theta p (a * v i) + ∑ j, fieldN p j i * (a * v j) =
    theta p a * v i + a * (theta p (v i) + ∑ j, fieldN p j i * v j)
  rw [(theta p).leibniz]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  have hs : (∑ j, fieldN p j i * (a * v j)) = ∑ j, a * (fieldN p j i * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem dualJordan_fifth_zero : dualJordan p ^ 5 = 0 := by
  rw [dualJordan, ← map_pow, ← Matrix.transpose_pow, fieldJ_fifth_zero,
    Matrix.transpose_zero, map_zero]

theorem dualJordan_prime_zero (hp7 : 7 ≤ p) : dualJordan p ^ p = 0 := by
  have he : p = (p - 5) + 5 := by omega
  calc
    dualJordan p ^ p = dualJordan p ^ ((p - 5) + 5) := congrArg (fun n => dualJordan p ^ n) he
    _ = 0 := by rw [pow_add, dualJordan_fifth_zero, mul_zero]

theorem euler_dualJordan_commute : Commute (euler p) (dualJordan p) := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (fieldJ p).transpose v) =
    matrixAction p (fieldJ p).transpose (euler p v)
  rw [euler_matrixAction]
  have hz : thetaMatrix p (fieldJ p).transpose = 0 := by
    apply Matrix.ext
    intro i j
    exact theta_fieldJ p j i
  rw [hz, map_zero, LinearMap.zero_apply, zero_add]

theorem dualNabla_gauge (hp7 : 7 ≤ p) :
    dualNabla p * dualGauge p = dualGauge p * dualModel p := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (dualV p) v) +
      matrixAction p (fieldN p).transpose (matrixAction p (dualV p) v) =
    matrixAction p (dualV p) (euler p v + matrixAction p (fieldJ p).transpose v)
  rw [euler_matrixAction, dual_matrix_gauge p hp7, map_sub]
  simp only [LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_add]
  abel

theorem dualGauge_inverse_mul : dualGaugeInverse p * dualGauge p = 1 := by
  rw [dualGaugeInverse, dualGauge, ← map_mul, dualV_inverse_mul, map_one]

theorem dualGauge_mul_inverse : dualGauge p * dualGaugeInverse p = 1 := by
  rw [dualGaugeInverse, dualGauge, ← map_mul, dualV_mul_inverse, map_one]

theorem dual_connection_conjugation (hp7 : 7 ≤ p) :
    dualGaugeInverse p * dualNabla p * dualGauge p = dualModel p := by
  rw [mul_assoc, dualNabla_gauge p hp7, ← mul_assoc, dualGauge_inverse_mul, one_mul]

theorem dualNabla_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    dualNabla p ^ n * dualGauge p = dualGauge p * dualModel p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, dualNabla_gauge p hp7, mul_assoc, ← pow_succ']

theorem dualModel_prime (hp7 : 7 ≤ p) : dualModel p ^ p = euler p := by
  rw [dualModel, add_pow_char_of_commute p (euler_dualJordan_commute p), euler_prime,
    dualJordan_prime_zero p hp7, add_zero]

theorem dualPsi_gauge (hp7 : 7 ≤ p) : dualPsi p * dualGauge p = dualGauge p * (-dualJordan p) := by
  rw [dualPsi, sub_mul, dualNabla_pow_gauge p hp7, dualNabla_gauge p hp7,
    dualModel_prime p hp7, ← mul_sub, dualModel]
  congr 1
  abel

theorem dual_pcurvature_conjugation (hp7 : 7 ≤ p) :
    dualGaugeInverse p * dualPsi p * dualGauge p = -dualJordan p := by
  rw [mul_assoc, dualPsi_gauge p hp7, ← mul_assoc, dualGauge_inverse_mul, one_mul]

theorem dualPsi_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    dualPsi p ^ n * dualGauge p = dualGauge p * (-dualJordan p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, dualPsi_gauge p hp7, mul_assoc, ← pow_succ']

theorem dual_pcurvature_fifth_zero (hp7 : 7 ≤ p) : dualPsi p ^ 5 = 0 := by
  calc
    dualPsi p ^ 5 = (dualPsi p ^ 5 * dualGauge p) * dualGaugeInverse p := by
      rw [mul_assoc, dualGauge_mul_inverse, mul_one]
    _ = (dualGauge p * (-dualJordan p) ^ 5) * dualGaugeInverse p := by
      rw [dualPsi_pow_gauge p hp7]
    _ = 0 := by
      rw [neg_pow (dualJordan p) 5, dualJordan_fifth_zero, mul_zero, mul_zero, zero_mul]

theorem actual_dual_fifth_zero (hp7 : 7 ≤ p) :
    (dualNabla p ^ p - dualNabla p) ^ 5 = 0 := dual_pcurvature_fifth_zero p hp7

end WPDual
