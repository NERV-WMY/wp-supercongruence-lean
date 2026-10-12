import WPToricRho.Coefficients

noncomputable section

namespace WPToricRho

open Polynomial

variable {p : ℕ} {R : Type*} [CommRing R]

def threeShift (f : ZMod p →+* R) (rho : R) (P : Polynomial R) : Polynomial R :=
  WPRho.shiftedTheta (rho + f (shift p 2))
    (WPRho.shiftedTheta (rho + f (shift p 1))
      (WPRho.shiftedTheta (rho + f (shift p 0)) P))

def finiteH (f : ZMod p →+* R) (rho : R) : Polynomial R :=
  ∑ n ∈ Finset.range p, monomial n (hCoeff f rho n)

def residual (f : ZMod p →+* R) (rho : R) : Polynomial R :=
  WPRho.rhoPower rho 3 (finiteH f rho) - X * threeShift f rho (finiteH f rho)

theorem coeff_threeShift (f : ZMod p →+* R) (rho : R) (P : Polynomial R) (n : ℕ) :
    (threeShift f rho P).coeff n = stepProduct f rho n * P.coeff n := by
  simp [threeShift, WPRho.coeff_shiftedTheta, stepProduct, factor,
    Fin.prod_univ_succ, shift, map_ofNat]
  ring

theorem coeff_finiteH (f : ZMod p →+* R) (rho : R) (n : ℕ) :
    (finiteH f rho).coeff n = if n < p then hCoeff f rho n else 0 := by
  simp [finiteH, finsetSum_coeff, coeff_monomial]

theorem finiteH_sum_powers (f : ZMod p →+* R) (rho : R) :
    finiteH f rho = ∑ n ∈ Finset.range p, C (hCoeff f rho n) * X ^ n := by
  simp only [finiteH, C_mul_X_pow_eq_monomial]

theorem finiteH_at_zero (f : ZMod p →+* R) (rho : R) (hp : p.Prime) :
    (finiteH f rho).coeff 0 = 1 := by
  rw [coeff_finiteH, if_pos hp.pos, hCoeff_zero]

theorem residual_coeff_zero (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) : (residual f rho).coeff 0 = 0 := by
  rw [residual, coeff_sub, WPRho.coeff_rhoPower, coeff_X_mul_zero, finiteH_at_zero f rho hp]
  simpa using hrho

theorem residual_coeff_interior (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) (n : ℕ) (hn : n + 1 < p) :
    (residual f rho).coeff (n + 1) = 0 := by
  have hn0 : n < p := by omega
  rw [residual, coeff_sub, WPRho.coeff_rhoPower, coeff_X_mul, coeff_threeShift,
    coeff_finiteH, if_pos hn, coeff_finiteH, if_pos hn0]
  rw [add_comm ((n + 1 : ℕ) : R) rho, hCoeff_recurrence hp f rho hrho n hn, sub_self]

theorem residual_coeff_terminal (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) : (residual f rho).coeff p = 0 := by
  have heq : p - 1 + 1 = p := by have := hp.two_le; omega
  have hlt : p - 1 < p := by have := hp.pos; omega
  have hc : (residual f rho).coeff (p - 1 + 1) = 0 := by
    rw [residual, coeff_sub, WPRho.coeff_rhoPower, coeff_X_mul, coeff_threeShift,
      coeff_finiteH, if_neg (by omega : ¬ p - 1 + 1 < p), mul_zero,
      coeff_finiteH, if_pos hlt, hCoeff_terminal hp f rho hrho, sub_self]
  exact (congrArg (fun n : ℕ => (residual f rho).coeff n) heq).symm.trans hc

theorem residual_coeff_above (f : ZMod p →+* R) (rho : R)
    (n : ℕ) (hn : p < n + 1) : (residual f rho).coeff (n + 1) = 0 := by
  have hn0 : ¬ n < p := by omega
  have hn1 : ¬ n + 1 < p := by omega
  rw [residual, coeff_sub, WPRho.coeff_rhoPower, coeff_X_mul, coeff_threeShift,
    coeff_finiteH, if_neg hn1, coeff_finiteH, if_neg hn0]
  simp

theorem finite_rho_residual (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) : residual f rho = 0 := by
  ext n
  rw [coeff_zero]
  cases n with
  | zero => exact residual_coeff_zero hp f rho hrho
  | succ n =>
    rcases lt_trichotomy (n + 1) p with hn | hn | hn
    · exact residual_coeff_interior hp f rho hrho n hn
    · simpa only [hn] using residual_coeff_terminal hp f rho hrho
    · exact residual_coeff_above f rho n hn

theorem finite_rho_connection_equation (hp : p.Prime) (_hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (rho : R) (hrho : rho ^ 3 = 0) :
    WPRho.rhoPower rho 3 (finiteH f rho) - X * threeShift f rho (finiteH f rho) = 0 :=
  finite_rho_residual hp f rho hrho

end WPToricRho
