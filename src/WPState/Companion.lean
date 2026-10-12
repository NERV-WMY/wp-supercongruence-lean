import WPState.Truncation

noncomputable section

namespace WPState

open Polynomial

def lowerCoeff (p : ℕ) : Fin 5 → ZMod p :=
  ![120 * (6 : ZMod p)⁻¹ ^ 5, 274 * (6 : ZMod p)⁻¹ ^ 4,
    225 * (6 : ZMod p)⁻¹ ^ 3, 85 * (6 : ZMod p)⁻¹ ^ 2, 15 * (6 : ZMod p)⁻¹]

def scalarProduct (p : ℕ) : Polynomial (ZMod p) :=
  ∏ j : Fin 5, (X + C (WPFiveFactor.sixthShift p j))

theorem scalar_product_expansion (p : ℕ) :
    scalarProduct p = X ^ 5 + ∑ i : Fin 5, C (lowerCoeff p i) * X ^ i.val := by
  simp [scalarProduct, lowerCoeff, WPFiveFactor.sixthShift,
    Fin.prod_univ_succ, Fin.sum_univ_succ, map_ofNat]
  ring

theorem fiveShift_expansion {p : ℕ} {R : Type*} [CommRing R]
    (f : ZMod p →+* R) (r : R) (P : Polynomial R) :
    WPRho.fiveShift f r P = WPRho.rhoPower r 5 P +
      ∑ i : Fin 5, C (f (lowerCoeff p i)) * WPRho.rhoPower r i.val P := by
  ext n
  have he := congrArg (fun Q : Polynomial (ZMod p) => Q.eval₂ f ((n : R) + r))
    (scalar_product_expansion p)
  have hs : WPRho.stepProduct f r n = ((n : R) + r) ^ 5 +
      ∑ i : Fin 5, f (lowerCoeff p i) * ((n : R) + r) ^ i.val := by
    simpa [scalarProduct, WPRho.stepProduct, WPRho.factor,
      Polynomial.eval₂_finsetProd, Polynomial.eval₂_finsetSum,
      add_comm, add_left_comm, add_assoc] using he
  simp only [WPRho.coeff_fiveShift, coeff_add, WPRho.coeff_rhoPower,
    finsetSum_coeff, coeff_C_mul]
  rw [hs, add_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc]

variable (p : ℕ)

def stateNat (i : ℕ) : Polynomial (TruncRing p) :=
  WPRho.rhoPower (rho p) i (WPRho.finiteH (base p) (rho p))

def state (i : Fin 5) : Polynomial (TruncRing p) := stateNat p i.val

theorem stateNat_succ (i : ℕ) :
    stateNat p (i + 1) = WPRho.theta (stateNat p i) + C (rho p) * stateNat p i := by
  unfold stateNat WPRho.rhoPower
  rw [Function.iterate_succ_apply']
  rfl

variable [Fact p.Prime]

theorem state_at_zero (i : Fin 5) : (state p i).coeff 0 = rho p ^ i.val := by
  simp [state, stateNat, WPRho.coeff_rhoPower, WPRho.finiteH_at_zero,
    Fact.out]

theorem cleared_fifth_state (hp7 : 7 ≤ p) :
    (1 - X) * stateNat p 5 =
      X * ∑ i : Fin 5, C (base p (lowerCoeff p i)) * state p i := by
  have he := WPRho.finite_rho_connection_equation (Fact.out : p.Prime) hp7
    (base p) (rho p) (rho_fifth_zero p)
  rw [fiveShift_expansion] at he
  have hs : stateNat p 5 = X * (stateNat p 5 +
      ∑ i : Fin 5, C (base p (lowerCoeff p i)) * state p i) := sub_eq_zero.mp he
  calc
    (1 - X) * stateNat p 5 = stateNat p 5 - X * stateNat p 5 := by ring
    _ = X * (stateNat p 5 + ∑ i : Fin 5, C (base p (lowerCoeff p i)) * state p i) -
        X * stateNat p 5 := by
      exact congrArg (fun Q => Q - X * stateNat p 5) hs
    _ = _ := by ring

theorem cleared_state (hp7 : 7 ≤ p) (i : Fin 5) :
    (1 - X) * (WPRho.theta (state p i) + C (rho p) * state p i) =
      if i.val < 4 then (1 - X) * stateNat p (i.val + 1)
      else X * ∑ k : Fin 5, C (base p (lowerCoeff p k)) * state p k := by
  change (1 - X) * (WPRho.theta (stateNat p i.val) + C (rho p) * stateNat p i.val) = _
  rw [← stateNat_succ]
  by_cases hi : i.val < 4
  · rw [if_pos hi]
  · have hi4 : i.val = 4 := by omega
    rw [if_neg hi, hi4]
    exact cleared_fifth_state p hp7

end WPState
