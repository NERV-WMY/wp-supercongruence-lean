import WPState.Companion

noncomputable section

namespace WPState

open Polynomial Module

variable (p : ℕ) [Fact p.Prime]

def V : Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p)) :=
  fun i j => coordPoly p j (state p i)

def J : Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p)) :=
  fun i j => C (jordan p i j)

def Npoly : Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p)) :=
  fun i j => if i.val < 4 then
    (if j.val = i.val + 1 then 1 - X else 0)
  else X * C (lowerCoeff p j)

def thetaMatrix (M : Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p))) :
    Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p)) :=
  fun i j => WPRho.theta (M i j)

def scaleMatrix (s : Polynomial (ZMod p))
    (M : Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p))) :
    Matrix (Fin 5) (Fin 5) (Polynomial (ZMod p)) := fun i j => s * M i j

theorem coeff_V (i j : Fin 5) (n : ℕ) :
    (V p i j).coeff n = rhoCoord p j ((state p i).coeff n) :=
  coeff_coordPoly p j (state p i) n

theorem state_reconstruction (i : Fin 5) :
    state p i = ∑ j : Fin 5, (V p i j).map (base p) * C (rho p ^ j.val) := by
  ext n
  simp only [finsetSum_coeff, coeff_mul_C, coeff_map, coeff_V]
  have he := (rhoBasis p).sum_repr ((state p i).coeff n)
  simpa [rhoCoord, Basis.coord_apply, rhoBasis_pow, Algebra.smul_def,
    base, AdjoinRoot.algebraMap_eq] using he.symm

theorem V_at_zero : (fun i j => (V p i j).eval 0) =
    (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) := by
  ext i j
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_V, state_at_zero, rhoCoord_power]
  rfl

theorem coordPoly_sum (j : Fin 5) (P : Fin 5 → Polynomial (TruncRing p)) :
    coordPoly p j (∑ i : Fin 5, P i) = ∑ i : Fin 5, coordPoly p j (P i) := by
  ext n
  simp [coeff_coordPoly, finsetSum_coeff]

theorem V_mul_J (i j : Fin 5) :
    (V p * J p) i j = ∑ k : Fin 5, C (jordan p k j) * V p i k := by
  simp only [Matrix.mul_apply, J]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem Npoly_mul_V (i j : Fin 5) :
    (Npoly p * V p) i j =
      if i.val < 4 then (1 - X) * coordPoly p j (stateNat p (i.val + 1))
      else X * ∑ k : Fin 5, C (lowerCoeff p k) * V p k j := by
  fin_cases i <;>
    simp [Npoly, Matrix.mul_apply, Fin.sum_univ_succ, V, state]
  ring

theorem cleared_coordinate_state (hp7 : 7 ≤ p) (i j : Fin 5) :
    (1 - X) * (WPRho.theta (V p i j) + (V p * J p) i j) =
      (Npoly p * V p) i j := by
  have he := congrArg (coordPoly p j) (cleared_state p hp7 i)
  simp only [sub_mul, one_mul, coordPoly_sub, coordPoly_X_mul, coordPoly_add,
    coordPoly_theta, coordPoly_rho_C_mul] at he
  rw [Npoly_mul_V, V_mul_J]
  change (1 - X) * (WPRho.theta (coordPoly p j (state p i)) +
    ∑ k : Fin 5, C (jordan p k j) * coordPoly p k (state p i)) = _
  by_cases hi : i.val < 4
  · rw [if_pos hi] at he ⊢
    simp only [coordPoly_sub, coordPoly_X_mul] at he
    simp only [sub_mul, one_mul]
    exact he
  · rw [if_neg hi] at he ⊢
    simp only [coordPoly_X_mul, coordPoly_sum, coordPoly_base_C_mul] at he
    simp only [sub_mul, one_mul]
    exact he

theorem cleared_gauge_equation (hp7 : 7 ≤ p) :
    scaleMatrix p (1 - X) (thetaMatrix p (V p)) =
      Npoly p * V p - scaleMatrix p (1 - X) (V p * J p) := by
  apply Matrix.ext
  intro i j
  change (1 - X) * WPRho.theta (V p i j) =
    (Npoly p * V p) i j - (1 - X) * (V p * J p) i j
  rw [eq_sub_iff_add_eq, ← mul_add]
  exact cleared_coordinate_state p hp7 i j

theorem J_fifth_zero : J p ^ 5 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, jordan, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

end WPState
