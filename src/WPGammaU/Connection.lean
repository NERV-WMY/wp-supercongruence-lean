import WPGammaU.Substitution

noncomputable section

namespace WPGammaU

open WPPsi

variable (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)

def fullFieldGauge : Matrix (Fin 5) (Fin 5) (K p) :=
  WPGamma.T p*WPDual.dualV p
def fullFieldGaugeInverse : Matrix (Fin 5) (Fin 5) (K p) :=
  WPDual.dualVInverse p*(WPGamma.T p)⁻¹

include hp7 in
theorem fullFieldGauge_equation :
    thetaMatrix p (fullFieldGauge p)=
      fullFieldGauge p*(fieldJ p).transpose-WPGamma.gammaZ p*fullFieldGauge p := by
  rw [fullFieldGauge, WPDual.thetaMatrix_mul, WPGamma.theta_T,
    zero_mul, zero_add, WPDual.dual_matrix_gauge p hp7]
  rw [← mul_assoc (WPGamma.gammaZ p) (WPGamma.T p),
    WPGamma.gamma_cyclic_matrix p hp7]
  noncomm_ring

include hp7 in
theorem fullFieldGauge_inverse_mul : fullFieldGaugeInverse p*fullFieldGauge p=1 := by
  rw [fullFieldGaugeInverse, fullFieldGauge]
  calc
    _ = WPDual.dualVInverse p*((WPGamma.T p)⁻¹*WPGamma.T p)*WPDual.dualV p := by
      simp only [mul_assoc]
    _ = 1 := by rw [WPGamma.T_inv_mul p hp7, mul_one, WPDual.dualV_inverse_mul]

include hp7 in
theorem fullFieldGauge_mul_inverse : fullFieldGauge p*fullFieldGaugeInverse p=1 := by
  rw [fullFieldGaugeInverse, fullFieldGauge]
  calc
    _ = WPGamma.T p*(WPDual.dualV p*WPDual.dualVInverse p)*(WPGamma.T p)⁻¹ := by
      simp only [mul_assoc]
    _ = 1 := by rw [WPDual.dualV_mul_inverse, mul_one, WPGamma.T_mul_inv p hp7]

def mappedMatrix (M : Matrix (Fin 5) (Fin 5) (K p)) := (substitute p hp7).mapMatrix M
def gammaM : Matrix (Fin 5) (Fin 5) (K p) := mappedMatrix p hp7 (WPGamma.gammaM p)
def frame : Matrix (Fin 5) (Fin 5) (K p) := mappedMatrix p hp7 (fullFieldGauge p)
def frameInverse : Matrix (Fin 5) (Fin 5) (K p) := mappedMatrix p hp7 (fullFieldGaugeInverse p)
def constantJ : Matrix (Fin 5) (Fin 5) (K p) := mappedMatrix p hp7 (fieldJ p).transpose

theorem mappedMatrix_theta (M : Matrix (Fin 5) (Fin 5) (K p)) :
    thetaMatrix p (mappedMatrix p hp7 M)=(6 : K p) • mappedMatrix p hp7 (thetaMatrix p M) := by
  apply Matrix.ext
  intro i j
  exact theta_substitute p hp7 (M i j)

include hp7 in
theorem gammaZ_six : (6 : K p) • WPGamma.gammaZ p=WPGamma.gammaM p := by
  apply Matrix.ext
  intro i j
  change 6*(WPGamma.q p*WPGamma.gammaM p i j)=WPGamma.gammaM p i j
  rw [WPGamma.q, ← mul_assoc, mul_inv_cancel₀ (WPDual.six_field_unit p hp7).ne_zero, one_mul]

theorem mappedMatrix_six (M : Matrix (Fin 5) (Fin 5) (K p)) :
    mappedMatrix p hp7 ((6 : K p) • M)=(6 : K p) • mappedMatrix p hp7 M := by
  apply Matrix.ext
  intro i j
  change substitute p hp7 (6*M i j)=6*substitute p hp7 (M i j)
  rw [map_mul, map_ofNat]

theorem frame_equation : thetaMatrix p (frame p hp7)=
    frame p hp7*((6 : K p) • constantJ p hp7)-gammaM p hp7*frame p hp7 := by
  rw [frame, mappedMatrix_theta, fullFieldGauge_equation p hp7]
  simp only [mappedMatrix, map_sub, map_mul]
  change (6 : K p) •
    (frame p hp7*constantJ p hp7-
      mappedMatrix p hp7 (WPGamma.gammaZ p)*frame p hp7)=_
  rw [smul_sub, ← Matrix.mul_smul, ← Matrix.smul_mul, ← mappedMatrix_six,
    gammaZ_six p hp7]
  rfl

theorem frame_inverse_mul : frameInverse p hp7*frame p hp7=1 := by
  rw [frameInverse, frame, mappedMatrix, mappedMatrix, ← map_mul,
    fullFieldGauge_inverse_mul p hp7, map_one]

theorem frame_mul_inverse : frame p hp7*frameInverse p hp7=1 := by
  rw [frameInverse, frame, mappedMatrix, mappedMatrix, ← map_mul,
    fullFieldGauge_mul_inverse p hp7, map_one]

theorem constantJ_theta : thetaMatrix p (constantJ p hp7)=0 := by
  rw [constantJ, mappedMatrix_theta]
  have hz : thetaMatrix p (fieldJ p).transpose=0 := by
    apply Matrix.ext
    intro i j
    exact theta_fieldJ p j i
  rw [hz]
  simp [mappedMatrix]

theorem constantJ_fifth_zero : constantJ p hp7^5=0 := by
  rw [constantJ, mappedMatrix, ← map_pow, ← Matrix.transpose_pow,
    fieldJ_fifth_zero, Matrix.transpose_zero, map_zero]

def nabla : StateEnd p := euler p+matrixAction p (gammaM p hp7)
def gauge : StateEnd p := matrixAction p (frame p hp7)
def gaugeInverse : StateEnd p := matrixAction p (frameInverse p hp7)
def jordan : StateEnd p := (6 : ZMod p) • matrixAction p (constantJ p hp7)
def model : StateEnd p := euler p+jordan p hp7
def psi : StateEnd p := nabla p hp7^p-nabla p hp7

theorem jordan_fifth_zero : jordan p hp7^5=0 := by
  rw [jordan, smul_pow, ← map_pow, constantJ_fifth_zero, map_zero, smul_zero]

theorem jordan_prime_zero : jordan p hp7^p=0 := by
  have he : p=(p-5)+5 := by omega
  calc
    jordan p hp7^p=jordan p hp7^((p-5)+5) := congrArg (fun n => jordan p hp7^n) he
    _ = 0 := by rw [pow_add, jordan_fifth_zero, mul_zero]

theorem euler_jordan_commute : Commute (euler p) (jordan p hp7) := by
  apply LinearMap.ext
  intro v
  change euler p ((6 : ZMod p) • matrixAction p (constantJ p hp7) v)=
    (6 : ZMod p) • matrixAction p (constantJ p hp7) (euler p v)
  rw [map_smul, euler_matrixAction, constantJ_theta, map_zero,
    LinearMap.zero_apply, zero_add]

theorem nabla_gauge : nabla p hp7*gauge p hp7=gauge p hp7*model p hp7 := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (frame p hp7) v)+
    matrixAction p (gammaM p hp7) (matrixAction p (frame p hp7) v)=
    matrixAction p (frame p hp7) (euler p v+(6 : ZMod p) • matrixAction p (constantJ p hp7) v)
  rw [euler_matrixAction, frame_equation, map_sub]
  simp only [LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_add]
  have hs : matrixAction p ((6 : K p) • constantJ p hp7) v=
      (6 : ZMod p) • matrixAction p (constantJ p hp7) v := by
    funext i
    change (∑ j, (6*constantJ p hp7 i j)*v j)=(6 : ZMod p) • (∑ j, constantJ p hp7 i j*v j)
    rw [Algebra.smul_def, map_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  abel

theorem gauge_inverse_mul : gaugeInverse p hp7*gauge p hp7=1 := by
  rw [gaugeInverse, gauge, ← map_mul, frame_inverse_mul, map_one]

theorem gauge_mul_inverse : gauge p hp7*gaugeInverse p hp7=1 := by
  rw [gaugeInverse, gauge, ← map_mul, frame_mul_inverse, map_one]

theorem nabla_pow_gauge (n : ℕ) :
    nabla p hp7^n*gauge p hp7=gauge p hp7*model p hp7^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, nabla_gauge,
      mul_assoc, ← pow_succ']

theorem model_prime : model p hp7^p=euler p := by
  rw [model, add_pow_char_of_commute p (euler_jordan_commute p hp7),
    euler_prime, jordan_prime_zero, add_zero]

theorem psi_gauge : psi p hp7*gauge p hp7=gauge p hp7*(-jordan p hp7) := by
  rw [psi, sub_mul, nabla_pow_gauge, nabla_gauge, model_prime,
    ← mul_sub, model]
  congr 1
  abel

theorem psi_pow_gauge (n : ℕ) :
    psi p hp7^n*gauge p hp7=gauge p hp7*(-jordan p hp7)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, psi_gauge,
      mul_assoc, ← pow_succ']

theorem actual_u_field_fifth_zero : (nabla p hp7^p-nabla p hp7)^5=0 := by
  change psi p hp7^5=0
  calc
    psi p hp7^5=(psi p hp7^5*gauge p hp7)*gaugeInverse p hp7 := by
      rw [mul_assoc, gauge_mul_inverse, mul_one]
    _ = (gauge p hp7*(-jordan p hp7)^5)*gaugeInverse p hp7 := by rw [psi_pow_gauge]
    _ = 0 := by rw [neg_pow (jordan p hp7) 5, jordan_fifth_zero,
      mul_zero, mul_zero, zero_mul]

end WPGammaU
