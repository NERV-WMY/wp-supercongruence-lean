import WPToricGamma.Connection

noncomputable section

namespace WPToricGamma

open WPPsi WPToricPsi

variable (p : ℕ) [Fact p.Prime]

def unit (i : Fin 3) : StateSpace p := Pi.single i 1

def gammaThree : StateSpace p := (oneMinus p)⁻¹ • ![1 / 8, -13 / 4, 9 / 2]

theorem euler_unit (i : Fin 3) : euler p (unit p i) = 0 := by
  funext j
  by_cases h : j = i <;> simp [euler, unit, h]

theorem matrixAction_unit (M : Matrix (Fin 3) (Fin 3) (K p)) (i : Fin 3) :
    matrixAction p M (unit p i) = fun j => M j i := by
  change M.mulVec (Pi.single i 1) = _
  exact Matrix.mulVec_single_one M i

theorem gammaU_unit (hp7 : 7 ≤ p) (i : Fin 3) :
    gammaU p (unit p i) = fun j => gammaM p j i := by
  rw [gammaU_actual p hp7]
  change (3 : ZMod p) • euler p (unit p i) + matrixAction p (gammaM p) (unit p i) = _
  rw [euler_unit, smul_zero, zero_add, matrixAction_unit]

theorem gammaU_first_two (hp7 : 7 ≤ p) (i : Fin 2) :
    gammaU p (unit p i.castSucc) = unit p i.succ -
      ((((2 * i.val + 1 : ℕ) : K p) / 2) • unit p i.castSucc) := by
  rw [gammaU_unit p hp7]
  funext j
  fin_cases i <;> fin_cases j <;> simp [gammaM, unit, div_eq_mul_inv]

theorem gammaU_last (hp7 : 7 ≤ p) :
    gammaU p (unit p 2) = gammaThree p - (5 / 2 : K p) • unit p 2 := by
  rw [gammaU_unit p hp7]
  funext j
  fin_cases j <;> simp [gammaM, gammaThree, unit] <;> ring

theorem dual_basis_succ (i : Fin 2) :
    WPToricDual.dualNabla p (unit p i.castSucc) = unit p i.succ := by
  change euler p (unit p i.castSucc) +
    matrixAction p (fieldN p).transpose (unit p i.castSucc) = _
  rw [euler_unit, zero_add, matrixAction_unit]
  funext j
  change fieldN p i.castSucc j = unit p i.succ j
  rw [fieldN_actual_entry]
  fin_cases i <;> fin_cases j <;> simp [unit]

theorem dual_cyclic_basis (r : Fin 3) :
    (WPToricDual.dualNabla p)^[r.val] (unit p 0) = unit p r := by
  have h0 := dual_basis_succ p 0
  have h1 := dual_basis_succ p 1
  change WPToricDual.dualNabla p (unit p 0) = unit p 1 at h0
  change WPToricDual.dualNabla p (unit p 1) = unit p 2 at h1
  fin_cases r <;> simp [Function.iterate_succ_apply', h0, h1]

theorem T_col_zero : (fun j => T p j 0) = unit p 0 := by
  rw [T_actual]
  funext j
  fin_cases j <;> simp [unit]

theorem gamma_cyclic_columns (hp7 : 7 ≤ p) (r : Fin 3) :
    (gammaNabla p)^[r.val] (unit p 0) = fun j => T p j r := by
  have he := LinearMap.congr_fun (gammaNabla_pow_gauge p hp7 r.val) (unit p 0)
  simp only [Module.End.mul_apply, Module.End.pow_apply, gammaGauge] at he
  rw [matrixAction_unit, T_col_zero, dual_cyclic_basis, matrixAction_unit] at he
  exact he

theorem gammaNabla_leibniz (a : K p) (v : StateSpace p) :
    gammaNabla p (a • v) = theta p a • v + a • gammaNabla p v := by
  funext i
  change theta p (a * v i) + ∑ j, gammaZ p i j * (a * v j) =
    theta p a * v i + a * (theta p (v i) + ∑ j, gammaZ p i j * v j)
  rw [(theta p).leibniz]
  simp only [smul_eq_mul, mul_add, Finset.mul_sum]
  have hs : (∑ j, gammaZ p i j * (a * v j)) = ∑ j, a * (gammaZ p i j * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem gammaU_leibniz (a : K p) (v : StateSpace p) :
    gammaU p (a • v) = ((3 : ZMod p) • theta p a) • v + a • gammaU p v := by
  change (3 : ZMod p) • gammaNabla p (a • v) = _
  rw [gammaNabla_leibniz, smul_add]
  rw [smul_assoc, smul_comm (3 : ZMod p) a]
  rfl

theorem gammaPsi_is_matrix (hp7 : 7 ≤ p) :
    gammaPsi p = matrixAction p (T p * WPToricDual.dualPsiMatrix p * (T p)⁻¹) := by
  calc
    gammaPsi p = (gammaPsi p * gammaGauge p) * gammaGaugeInverse p := by
      rw [mul_assoc, gammaGauge_mul_inverse p hp7, mul_one]
    _ = (gammaGauge p * WPToricDual.dualPsi p) * gammaGaugeInverse p := by
      rw [gammaPsi_gauge p hp7]
    _ = _ := by
      rw [WPToricDual.dualPsi_is_matrix p hp7]
      simp only [gammaGauge, gammaGaugeInverse, map_mul]

theorem gammaPsi_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    gammaPsi p (a • v) = a • gammaPsi p v := by
  rw [gammaPsi_is_matrix p hp7]
  change (T p * WPToricDual.dualPsiMatrix p * (T p)⁻¹).mulVecLin (a • v) =
    a • (T p * WPToricDual.dualPsiMatrix p * (T p)⁻¹).mulVecLin v
  exact map_smul _ _ _

theorem gammaUPsi_K_linear (hp7 : 7 ≤ p) (a : K p) (v : StateSpace p) :
    gammaUPsi p (a • v) = a • gammaUPsi p v := by
  rw [gamma_triple_pcurvature_scaling]
  change (3 : ZMod p) • gammaPsi p (a • v) = a • ((3 : ZMod p) • gammaPsi p v)
  rw [gammaPsi_K_linear p hp7, smul_comm (3 : ZMod p) a]

end WPToricGamma
