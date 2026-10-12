import WPPsi.FieldCompanion
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.Algebra.CharP.Lemmas

noncomputable section

namespace WPPsi

variable (p : ℕ) [Fact p.Prime]

abbrev StateSpace := Fin 5 → K p
abbrev StateEnd := Module.End (ZMod p) (StateSpace p)

def matrixAction : Matrix (Fin 5) (Fin 5) (K p) →+* StateEnd p where
  toFun M := M.mulVecLin.restrictScalars (ZMod p)
  map_one' := by apply LinearMap.ext; intro v; exact Matrix.one_mulVec v
  map_zero' := by apply LinearMap.ext; intro v; exact Matrix.zero_mulVec v
  map_add' M N := by apply LinearMap.ext; intro v; exact Matrix.add_mulVec M N v
  map_mul' M N := by apply LinearMap.ext; intro v; exact (Matrix.mulVec_mulVec v M N).symm

def euler : StateEnd p where
  toFun v := fun i => theta p (v i)
  map_add' v w := by funext i; exact map_add (theta p) (v i) (w i)
  map_smul' a v := by funext i; exact (theta p).map_smul a (v i)

def jordan : StateEnd p := matrixAction p (fieldJ p)
def gauge : StateEnd p := matrixAction p (WPState.fieldV p)
def nabla : StateEnd p := euler p - matrixAction p (fieldN p)
def modelNabla : StateEnd p := euler p - jordan p
def psi : StateEnd p := nabla p ^ p - nabla p
def gaugeInverse : StateEnd p := matrixAction p ((WPState.fieldV p)⁻¹)

instance stateEnd_charP : CharP (StateEnd p) p :=
  charP_of_injective_ringHom (algebraMap (ZMod p) (StateEnd p)).injective p

theorem euler_pow_entry (n : ℕ) (v : StateSpace p) (i : Fin 5) :
    (euler p ^ n) v i = (theta p)^[n] (v i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change theta p ((euler p ^ n) v i) = _
    rw [ih, Function.iterate_succ_apply']

theorem euler_prime : euler p ^ p = euler p := by
  apply LinearMap.ext
  intro v
  funext i
  rw [euler_pow_entry]
  exact theta_prime_field p _

theorem jordan_fifth_zero : jordan p ^ 5 = 0 := by
  rw [jordan, ← map_pow, fieldJ_fifth_zero, map_zero]

theorem jordan_prime_zero (hp7 : 7 ≤ p) : jordan p ^ p = 0 := by
  have hp5 : 5 ≤ p := by omega
  have he : p = (p - 5) + 5 := by omega
  calc
    jordan p ^ p = jordan p ^ ((p - 5) + 5) := congrArg (fun n => jordan p ^ n) he
    _ = 0 := by rw [pow_add, jordan_fifth_zero, mul_zero]

theorem euler_matrixAction (M : Matrix (Fin 5) (Fin 5) (K p)) (v : StateSpace p) :
    euler p (matrixAction p M v) =
      matrixAction p (thetaMatrix p M) v + matrixAction p M (euler p v) := by
  funext i
  change theta p (∑ j, M i j * v j) =
    (∑ j, theta p (M i j) * v j) + ∑ j, M i j * theta p (v j)
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(theta p).leibniz]
  simp only [smul_eq_mul]
  ring

theorem euler_jordan_commute : Commute (euler p) (jordan p) := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (fieldJ p) v) = matrixAction p (fieldJ p) (euler p v)
  rw [euler_matrixAction]
  have hz : thetaMatrix p (fieldJ p) = 0 := by
    apply Matrix.ext
    intro i j
    exact theta_fieldJ p i j
  rw [hz, map_zero, LinearMap.zero_apply, zero_add]

theorem nabla_gauge (hp7 : 7 ≤ p) : nabla p * gauge p = gauge p * modelNabla p := by
  apply LinearMap.ext
  intro v
  change euler p (matrixAction p (WPState.fieldV p) v) -
      matrixAction p (fieldN p) (matrixAction p (WPState.fieldV p) v) =
    matrixAction p (WPState.fieldV p) (euler p v - matrixAction p (fieldJ p) v)
  rw [euler_matrixAction, field_gauge_equation p hp7, map_sub]
  simp only [LinearMap.sub_apply, map_mul, Module.End.mul_apply, map_sub]
  abel

theorem gauge_inverse_mul : gaugeInverse p * gauge p = 1 := by
  have hu : IsUnit (WPState.fieldV p).det :=
    isUnit_iff_ne_zero.mpr (WPState.fieldV_det_nonzero p)
  rw [gaugeInverse, gauge, ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]

theorem gauge_mul_inverse : gauge p * gaugeInverse p = 1 := by
  have hu : IsUnit (WPState.fieldV p).det :=
    isUnit_iff_ne_zero.mpr (WPState.fieldV_det_nonzero p)
  rw [gaugeInverse, gauge, ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]

theorem connection_conjugation (hp7 : 7 ≤ p) :
    gaugeInverse p * nabla p * gauge p = modelNabla p := by
  rw [mul_assoc, nabla_gauge p hp7, ← mul_assoc, gauge_inverse_mul, one_mul]

theorem nabla_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    nabla p ^ n * gauge p = gauge p * modelNabla p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, nabla_gauge p hp7, mul_assoc, ← pow_succ']

theorem modelNabla_prime (hp7 : 7 ≤ p) : modelNabla p ^ p = euler p := by
  rw [modelNabla, sub_pow_char_of_commute p (euler_jordan_commute p), euler_prime,
    jordan_prime_zero p hp7, sub_zero]

theorem psi_gauge (hp7 : 7 ≤ p) : psi p * gauge p = gauge p * jordan p := by
  rw [psi, sub_mul, nabla_pow_gauge p hp7, nabla_gauge p hp7,
    modelNabla_prime p hp7, ← mul_sub, modelNabla]
  congr 1
  abel

theorem pcurvature_conjugation (hp7 : 7 ≤ p) :
    gaugeInverse p * psi p * gauge p = jordan p := by
  rw [mul_assoc, psi_gauge p hp7, ← mul_assoc, gauge_inverse_mul, one_mul]

theorem psi_pow_gauge (hp7 : 7 ≤ p) (n : ℕ) :
    psi p ^ n * gauge p = gauge p * jordan p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, psi_gauge p hp7, mul_assoc, ← pow_succ']

theorem companion_pcurvature_fifth_zero (hp7 : 7 ≤ p) : psi p ^ 5 = 0 := by
  calc
    psi p ^ 5 = (psi p ^ 5 * gauge p) * gaugeInverse p := by
      rw [mul_assoc, gauge_mul_inverse, mul_one]
    _ = (gauge p * jordan p ^ 5) * gaugeInverse p := by rw [psi_pow_gauge p hp7]
    _ = 0 := by rw [jordan_fifth_zero, mul_zero, zero_mul]

theorem actual_companion_fifth_zero (hp7 : 7 ≤ p) :
    (nabla p ^ p - nabla p) ^ 5 = 0 := companion_pcurvature_fifth_zero p hp7

theorem actual_companion_iterate_fifth_zero (hp7 : 7 ≤ p) (v : StateSpace p) :
    (fun w => (nabla p)^[p] w - nabla p w)^[5] v = 0 := by
  have he := LinearMap.congr_fun (actual_companion_fifth_zero p hp7) v
  rw [Module.End.pow_apply] at he
  have hs : (fun w => (nabla p)^[p] w - nabla p w) =
      (nabla p ^ p - nabla p : StateEnd p) := by
    funext w
    simp only [LinearMap.sub_apply, Module.End.pow_apply]
  rw [hs]
  exact he

end WPPsi
