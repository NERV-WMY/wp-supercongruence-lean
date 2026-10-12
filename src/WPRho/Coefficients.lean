import WPFiveFactor
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section

namespace WPRho

open Polynomial

variable {p : ℕ} {R : Type*} [CommRing R]

def factor (f : ZMod p →+* R) (rho : R) (j : Fin 5) (k : ℕ) : R :=
  rho + f (WPFiveFactor.sixthShift p j + (k : ZMod p))

def stepProduct (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  ∏ j : Fin 5, factor f rho j n

def numerator (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  ∏ j : Fin 5, ∏ k ∈ Finset.range n, factor f rho j k

def denominator (rho : R) (n : ℕ) : R :=
  ∏ k ∈ Finset.range n, (rho + ((k + 1 : ℕ) : R)) ^ 5

def hCoeff (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  numerator f rho n * Ring.inverse (denominator rho n)

theorem residue_unit (hp : p.Prime) (f : ZMod p →+* R)
    (k : ℕ) (hk0 : 0 < k) (hkp : k < p) : IsUnit (k : R) := by
  let : Fact p.Prime := ⟨hp⟩
  have hk : (k : ZMod p) ≠ 0 := by
    change ¬ (k : ZMod p) = 0
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hk0 hd
    omega
  simpa using (isUnit_iff_ne_zero.mpr hk).map f

theorem denominator_factor_unit (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) (k : ℕ) (hk0 : 0 < k) (hkp : k < p) :
    IsUnit (rho + (k : R)) := by
  exact (show IsNilpotent rho from ⟨5, hrho⟩).isUnit_add_right_of_commute
    (residue_unit hp f k hk0 hkp) (Commute.all _ _)

theorem denominator_unit (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) (n : ℕ) (hn : n < p) :
    IsUnit (denominator rho n) := by
  apply IsUnit.prod_iff.mpr
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  exact (denominator_factor_unit hp f rho hrho (k + 1) (by omega) (by omega)).pow 5

theorem numerator_zero (f : ZMod p →+* R) (rho : R) : numerator f rho 0 = 1 := by
  simp [numerator]

theorem denominator_zero (rho : R) : denominator rho 0 = 1 := by
  simp [denominator]

theorem hCoeff_zero (f : ZMod p →+* R) (rho : R) : hCoeff f rho 0 = 1 := by
  simp [hCoeff, numerator_zero, denominator_zero, Ring.inverse_one]

theorem numerator_succ (f : ZMod p →+* R) (rho : R) (n : ℕ) :
    numerator f rho (n + 1) = numerator f rho n * stepProduct f rho n := by
  simp only [numerator, stepProduct, Finset.prod_range_succ]
  exact Finset.prod_mul_distrib

theorem denominator_succ (rho : R) (n : ℕ) :
    denominator rho (n + 1) = denominator rho n * (rho + ((n + 1 : ℕ) : R)) ^ 5 := by
  exact Finset.prod_range_succ _ _

theorem denominator_hCoeff (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) (n : ℕ) (hn : n < p) :
    denominator rho n * hCoeff f rho n = numerator f rho n := by
  unfold hCoeff
  calc
    denominator rho n * (numerator f rho n * Ring.inverse (denominator rho n)) =
        numerator f rho n * (denominator rho n * Ring.inverse (denominator rho n)) := by ring
    _ = numerator f rho n := by
      rw [Ring.mul_inverse_cancel _ (denominator_unit hp f rho hrho n hn), mul_one]

theorem hCoeff_recurrence (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) (n : ℕ) (hn : n + 1 < p) :
    (rho + ((n + 1 : ℕ) : R)) ^ 5 * hCoeff f rho (n + 1) =
      stepProduct f rho n * hCoeff f rho n := by
  have hunit := denominator_unit hp f rho hrho n (by omega)
  have hnext := (denominator_factor_unit hp f rho hrho (n + 1) (by omega) hn).pow 5
  unfold hCoeff
  rw [numerator_succ, denominator_succ, Ring.inverse_mul (Or.inl hunit)]
  calc
    (rho + ((n + 1 : ℕ) : R)) ^ 5 *
        (numerator f rho n * stepProduct f rho n *
          (Ring.inverse ((rho + ((n + 1 : ℕ) : R)) ^ 5) *
            Ring.inverse (denominator rho n))) =
      ((rho + ((n + 1 : ℕ) : R)) ^ 5 *
        Ring.inverse ((rho + ((n + 1 : ℕ) : R)) ^ 5)) *
          (stepProduct f rho n * (numerator f rho n * Ring.inverse (denominator rho n))) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hnext, one_mul]

theorem numerator_full_block_zero (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) : numerator f rho p = 0 := by
  have hz := WPFiveFactor.five_factor_nilpotent_product p hp f rho hrho
  have heq : numerator f rho p = ∏ j : Fin 5, ∏ k : Fin p, factor f rho j k.val := by
    unfold numerator
    apply Finset.prod_congr rfl
    intro j _
    exact (Fin.prod_univ_eq_prod_range (factor f rho j) p).symm
  rw [heq]
  exact hz

theorem hCoeff_terminal (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 5 = 0) :
    stepProduct f rho (p - 1) * hCoeff f rho (p - 1) = 0 := by
  have heq : p - 1 + 1 = p := by have := hp.two_le; omega
  unfold hCoeff
  calc
    stepProduct f rho (p - 1) *
        (numerator f rho (p - 1) * Ring.inverse (denominator rho (p - 1))) =
      (numerator f rho (p - 1) * stepProduct f rho (p - 1)) *
        Ring.inverse (denominator rho (p - 1)) := by ring
    _ = numerator f rho p * Ring.inverse (denominator rho (p - 1)) := by
      rw [← numerator_succ, heq]
    _ = 0 := by rw [numerator_full_block_zero hp f rho hrho, zero_mul]

end WPRho
