import WPToricState.Truncation

noncomputable section

namespace WPToricState

open Polynomial

def lowerCoeff (p : ℕ) : Fin 3 → ZMod p :=
  ![15 * (6 : ZMod p)⁻¹ ^ 3, 23 * (6 : ZMod p)⁻¹ ^ 2, 9 * (6 : ZMod p)⁻¹]

def scalarProduct (p : ℕ) : Polynomial (ZMod p) :=
  ∏ j : Fin 3, (X + C (WPToricRho.shift p j))

theorem scalar_product_expansion (p : ℕ) :
    scalarProduct p = X ^ 3 + ∑ i : Fin 3, C (lowerCoeff p i) * X ^ i.val := by
  simp [scalarProduct, lowerCoeff, WPToricRho.shift,
    Fin.prod_univ_succ, Fin.sum_univ_succ, map_ofNat]
  ring

theorem threeShift_expansion {p : ℕ} {R : Type*} [CommRing R]
    (f : ZMod p →+* R) (r : R) (P : Polynomial R) :
    WPToricRho.threeShift f r P = WPRho.rhoPower r 3 P +
      ∑ i : Fin 3, C (f (lowerCoeff p i)) * WPRho.rhoPower r i.val P := by
  ext n
  have he := congrArg (fun Q : Polynomial (ZMod p) => Q.eval₂ f ((n : R) + r))
    (scalar_product_expansion p)
  have hs : WPToricRho.stepProduct f r n = ((n : R) + r) ^ 3 +
      ∑ i : Fin 3, f (lowerCoeff p i) * ((n : R) + r) ^ i.val := by
    simpa [scalarProduct, WPToricRho.stepProduct, WPToricRho.factor,
      Polynomial.eval₂_finsetProd, Polynomial.eval₂_finsetSum,
      add_comm, add_left_comm, add_assoc] using he
  simp only [WPToricRho.coeff_threeShift, coeff_add, WPRho.coeff_rhoPower,
    finsetSum_coeff, coeff_C_mul]
  rw [hs, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc]

variable (p : ℕ)

def stateNat (i : ℕ) : Polynomial (TruncRing p) :=
  WPRho.rhoPower (rho p) i (WPToricRho.finiteH (base p) (rho p))

def state (i : Fin 3) : Polynomial (TruncRing p) := stateNat p i.val

theorem stateNat_succ (i : ℕ) :
    stateNat p (i + 1) = WPRho.theta (stateNat p i) + C (rho p) * stateNat p i := by
  unfold stateNat WPRho.rhoPower
  rw [Function.iterate_succ_apply']
  rfl

variable [Fact p.Prime]

theorem state_at_zero (i : Fin 3) : (state p i).coeff 0 = rho p ^ i.val := by
  simp [state, stateNat, WPRho.coeff_rhoPower, WPToricRho.finiteH_at_zero,
    Fact.out]

theorem cleared_third_state (hp7 : 7 ≤ p) :
    (1 - X) * stateNat p 3 =
      X * ∑ i : Fin 3, C (base p (lowerCoeff p i)) * state p i := by
  have he := WPToricRho.finite_rho_connection_equation (Fact.out : p.Prime) hp7
    (base p) (rho p) (rho_third_zero p)
  rw [threeShift_expansion] at he
  have hs : stateNat p 3 = X * (stateNat p 3 +
      ∑ i : Fin 3, C (base p (lowerCoeff p i)) * state p i) := sub_eq_zero.mp he
  calc
    (1 - X) * stateNat p 3 = stateNat p 3 - X * stateNat p 3 := by ring
    _ = X * (stateNat p 3 + ∑ i : Fin 3, C (base p (lowerCoeff p i)) * state p i) -
        X * stateNat p 3 := by
      exact congrArg (fun Q => Q - X * stateNat p 3) hs
    _ = _ := by ring

theorem cleared_state (hp7 : 7 ≤ p) (i : Fin 3) :
    (1 - X) * (WPRho.theta (state p i) + C (rho p) * state p i) =
      if i.val < 2 then (1 - X) * stateNat p (i.val + 1)
      else X * ∑ k : Fin 3, C (base p (lowerCoeff p k)) * state p k := by
  change (1 - X) * (WPRho.theta (stateNat p i.val) + C (rho p) * stateNat p i.val) = _
  rw [← stateNat_succ]
  by_cases hi : i.val < 2
  · rw [if_pos hi]
  · have hi2 : i.val = 2 := by omega
    rw [if_neg hi, hi2]
    exact cleared_third_state p hp7

end WPToricState

