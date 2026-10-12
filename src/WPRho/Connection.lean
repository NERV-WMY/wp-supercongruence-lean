import WPRho.Coefficients

noncomputable section

namespace WPRho

open Polynomial

variable {p : ℕ} {R : Type*} [CommRing R]

def theta (P : Polynomial R) : Polynomial R := X * P.derivative

def shiftedTheta (c : R) (P : Polynomial R) : Polynomial R :=
  theta P + C c * P

def rhoPower (rho : R) (m : ℕ) (P : Polynomial R) : Polynomial R :=
  (shiftedTheta rho)^[m] P

def fiveShift (f : ZMod p →+* R) (rho : R) (P : Polynomial R) : Polynomial R :=
  shiftedTheta (rho + f (WPFiveFactor.sixthShift p 4))
    (shiftedTheta (rho + f (WPFiveFactor.sixthShift p 3))
      (shiftedTheta (rho + f (WPFiveFactor.sixthShift p 2))
        (shiftedTheta (rho + f (WPFiveFactor.sixthShift p 1))
          (shiftedTheta (rho + f (WPFiveFactor.sixthShift p 0)) P))))

def finiteH (f : ZMod p →+* R) (rho : R) : Polynomial R :=
  ∑ n ∈ Finset.range p, monomial n (hCoeff f rho n)

def residual (f : ZMod p →+* R) (rho : R) : Polynomial R :=
  rhoPower rho 5 (finiteH f rho) - X * fiveShift f rho (finiteH f rho)

theorem coeff_theta (P : Polynomial R) (n : ℕ) :
    (theta P).coeff n = (n : R) * P.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n =>
    rw [theta, coeff_X_mul, coeff_derivative]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_shiftedTheta (c : R) (P : Polynomial R) (n : ℕ) :
    (shiftedTheta c P).coeff n = ((n : R) + c) * P.coeff n := by
  rw [shiftedTheta, coeff_add, coeff_theta, coeff_C_mul]
  ring

theorem shiftedTheta_commute (a b : R) (P : Polynomial R) :
    shiftedTheta a (shiftedTheta b P) = shiftedTheta b (shiftedTheta a P) := by
  ext n
  simp only [coeff_shiftedTheta]
  ring

theorem coeff_rhoPower (rho : R) (m : ℕ) (P : Polynomial R) (n : ℕ) :
    (rhoPower rho m P).coeff n = ((n : R) + rho) ^ m * P.coeff n := by
  induction m with
  | zero => simp [rhoPower]
  | succ m ih =>
    rw [rhoPower, Function.iterate_succ_apply', coeff_shiftedTheta]
    change ((n : R) + rho) * (rhoPower rho m P).coeff n = _
    rw [ih, pow_succ]
    ring

theorem coeff_fiveShift (f : ZMod p →+* R) (rho : R) (P : Polynomial R) (n : ℕ) :
    (fiveShift f rho P).coeff n = stepProduct f rho n * P.coeff n := by
  simp [fiveShift, coeff_shiftedTheta, stepProduct, factor,
    Fin.prod_univ_succ, WPFiveFactor.sixthShift, map_ofNat]
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
    (rho : R) (hrho : rho ^ 5 = 0) : (residual f rho).coeff 0 = 0 := by
  rw [residual, coeff_sub, coeff_rhoPower, coeff_X_mul_zero, finiteH_at_zero f rho hp]
  simpa using hrho

theorem residual_coeff_interior (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) (n : ℕ) (hn : n + 1 < p) :
    (residual f rho).coeff (n + 1) = 0 := by
  have hn0 : n < p := by omega
  rw [residual, coeff_sub, coeff_rhoPower, coeff_X_mul, coeff_fiveShift,
    coeff_finiteH, if_pos hn, coeff_finiteH, if_pos hn0]
  rw [add_comm ((n + 1 : ℕ) : R) rho, hCoeff_recurrence hp f rho hrho n hn, sub_self]

theorem residual_coeff_terminal (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) : (residual f rho).coeff p = 0 := by
  have heq : p - 1 + 1 = p := by have := hp.two_le; omega
  have hlt : p - 1 < p := by have := hp.pos; omega
  have hc : (residual f rho).coeff (p - 1 + 1) = 0 := by
    rw [residual, coeff_sub, coeff_rhoPower, coeff_X_mul, coeff_fiveShift,
      coeff_finiteH, if_neg (by omega : ¬ p - 1 + 1 < p), mul_zero,
      coeff_finiteH, if_pos hlt, hCoeff_terminal hp f rho hrho, sub_self]
  exact (congrArg (fun n : ℕ => (residual f rho).coeff n) heq).symm.trans hc

theorem residual_coeff_above (f : ZMod p →+* R) (rho : R)
    (n : ℕ) (hn : p < n + 1) : (residual f rho).coeff (n + 1) = 0 := by
  have hn0 : ¬ n < p := by omega
  have hn1 : ¬ n + 1 < p := by omega
  rw [residual, coeff_sub, coeff_rhoPower, coeff_X_mul, coeff_fiveShift,
    coeff_finiteH, if_neg hn1, coeff_finiteH, if_neg hn0]
  simp

theorem finite_rho_residual (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) : residual f rho = 0 := by
  ext n
  rw [coeff_zero]
  cases n with
  | zero => exact residual_coeff_zero hp f rho hrho
  | succ n =>
    rcases lt_trichotomy (n + 1) p with hn | hn | hn
    · exact residual_coeff_interior hp f rho hrho n hn
    · simpa only [hn] using residual_coeff_terminal hp f rho hrho
    · exact residual_coeff_above f rho n hn

theorem mapped_six_unit (hp : p.Prime) (hp7 : 7 ≤ p) (f : ZMod p →+* R) :
    IsUnit (6 : R) := by
  simpa only [map_ofNat] using (WPFiveFactor.six_unit p hp hp7).map f

theorem mapped_shift_normalized (hp : p.Prime) (hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (j : Fin 5) :
    (6 : R) * f (WPFiveFactor.sixthShift p j) = ((j.val + 1 : ℕ) : R) := by
  simpa [map_ofNat] using congrArg f (WPFiveFactor.sixthShift_normalized p hp hp7 j)

theorem mapped_shift_division (hp : p.Prime) (hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (j : Fin 5) :
    f (WPFiveFactor.sixthShift p j) =
      ((j.val + 1 : ℕ) : R) * Ring.inverse (6 : R) := by
  calc
    f (WPFiveFactor.sixthShift p j) =
        Ring.inverse (6 : R) * ((6 : R) * f (WPFiveFactor.sixthShift p j)) := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ (mapped_six_unit hp hp7 f), one_mul]
    _ = Ring.inverse (6 : R) * ((j.val + 1 : ℕ) : R) := by
      rw [mapped_shift_normalized hp hp7 f j]
    _ = _ := mul_comm _ _

theorem finite_rho_connection (hp : p.Prime) (hp7 : 7 ≤ p) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) :
    IsUnit (6 : R) ∧
      rhoPower rho 5 (finiteH f rho) - X * fiveShift f rho (finiteH f rho) = 0 := by
  exact ⟨mapped_six_unit hp hp7 f, finite_rho_residual hp f rho hrho⟩

theorem finite_rho_connection_equation (hp : p.Prime) (hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (rho : R) (hrho : rho ^ 5 = 0) :
    rhoPower rho 5 (finiteH f rho) - X * fiveShift f rho (finiteH f rho) = 0 := by
  exact (finite_rho_connection hp hp7 f rho hrho).2

end WPRho
