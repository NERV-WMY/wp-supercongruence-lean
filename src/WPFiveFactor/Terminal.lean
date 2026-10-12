import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

noncomputable section

namespace WPFiveFactor

open Polynomial

def pBlock (p : ℕ) (a : ZMod p) : Polynomial (ZMod p) :=
  ∏ k : Fin p, (X + C (a + (k.val : ZMod p)))

def sixthShift (p : ℕ) (j : Fin 5) : ZMod p :=
  ((j.val + 1 : ℕ) : ZMod p) * (6 : ZMod p)⁻¹

def fiveFactorBlock (p : ℕ) : Polynomial (ZMod p) :=
  ∏ j : Fin 5, pBlock p (sixthShift p j)

theorem six_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : IsUnit (6 : ZMod p) := by
  apply (ZMod.isUnit_iff_coprime 6 p).mpr
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd (by norm_num : 0 < 6) hd
  omega

theorem six_nonzero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : (6 : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  exact (six_unit p hp hp7).ne_zero

theorem sixthShift_normalized (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (j : Fin 5) :
    6 * sixthShift p j = ((j.val + 1 : ℕ) : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  unfold sixthShift
  field_simp [six_nonzero p hp hp7]

theorem sixthShift_nonzero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (j : Fin 5) :
    sixthShift p j ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hj : 0 < j.val + 1 := by omega
  have hjp : j.val + 1 < p := by omega
  have hnum : ((j.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    change ¬ ((j.val + 1 : ℕ) : ZMod p) = 0
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hj hd
    omega
  exact mul_ne_zero hnum (inv_ne_zero (six_nonzero p hp hp7))

theorem zero_residue (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    ∃ k : Fin p, a + (k.val : ZMod p) = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨⟨(-a).val, ZMod.val_lt (-a)⟩, ?_⟩
  simp

theorem zero_residue_unique (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    ∃! k : Fin p, a + (k.val : ZMod p) = 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨k, hk⟩ := zero_residue p hp a
  refine ⟨k, hk, ?_⟩
  intro l hl
  have heq : (l.val : ZMod p) = (k.val : ZMod p) := by
    exact add_left_cancel (hl.trans hk.symm)
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt l.isLt, ZMod.val_natCast_of_lt k.isLt] at hval
  exact Fin.ext hval

theorem pBlock_X_divides (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    (X : Polynomial (ZMod p)) ∣ pBlock p a := by
  obtain ⟨k, hk⟩ := zero_residue p hp a
  have hd := Finset.dvd_prod_of_mem
    (fun k : Fin p => (X + C (a + (k.val : ZMod p)) : Polynomial (ZMod p)))
    (Finset.mem_univ k)
  simpa [pBlock, hk] using hd

theorem pBlock_zero_evaluation (p : ℕ) (hp : p.Prime) (a : ZMod p) :
    (pBlock p a).eval 0 = 0 := by
  obtain ⟨Q, hQ⟩ := pBlock_X_divides p hp a
  rw [hQ]
  simp

theorem five_factor_X5_divides (p : ℕ) (hp : p.Prime) :
    (X : Polynomial (ZMod p)) ^ 5 ∣ fiveFactorBlock p := by
  have hd := Finset.prod_dvd_prod_of_dvd (s := (Finset.univ : Finset (Fin 5)))
    (fun _ : Fin 5 => (X : Polynomial (ZMod p)))
    (fun j : Fin 5 => pBlock p (sixthShift p j))
    (fun j _ => pBlock_X_divides p hp (sixthShift p j))
  simpa [fiveFactorBlock] using hd

theorem sixthShift_zero_residue_nonzero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (j : Fin 5) :
    ∃ k : Fin p, k.val ≠ 0 ∧ sixthShift p j + (k.val : ZMod p) = 0 := by
  obtain ⟨k, hk⟩ := zero_residue p hp (sixthShift p j)
  refine ⟨k, ?_, hk⟩
  intro hk0
  have hzero : sixthShift p j = 0 := by simpa [hk0] using hk
  exact sixthShift_nonzero p hp hp7 j hzero

theorem five_factor_terminal (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    IsUnit (6 : ZMod p) ∧ (X : Polynomial (ZMod p)) ^ 5 ∣ fiveFactorBlock p := by
  exact ⟨six_unit p hp hp7, five_factor_X5_divides p hp⟩

theorem five_factor_low_coefficients (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : n < 5) :
    (fiveFactorBlock p).coeff n = 0 := by
  exact (Polynomial.X_pow_dvd_iff.mp (five_factor_X5_divides p hp)) n hn

theorem five_factor_constant_zero (p : ℕ) (hp : p.Prime) :
    (fiveFactorBlock p).coeff 0 = 0 := by
  exact five_factor_low_coefficients p hp 0 (by norm_num)

theorem five_factor_mod_X5_zero (p : ℕ) (hp : p.Prime) :
    fiveFactorBlock p %ₘ (X : Polynomial (ZMod p)) ^ 5 = 0 := by
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (monic_X.pow 5)).mpr
    (five_factor_X5_divides p hp)

theorem five_factor_nilpotent_evaluation (p : ℕ) (hp : p.Prime)
    {R : Type*} [CommRing R] (f : ZMod p →+* R) (rho : R) (hrho : rho ^ 5 = 0) :
    (fiveFactorBlock p).eval₂ f rho = 0 := by
  obtain ⟨Q, hQ⟩ := five_factor_X5_divides p hp
  rw [hQ]
  simp [hrho]

theorem five_factor_nilpotent_product (p : ℕ) (hp : p.Prime)
    {R : Type*} [CommRing R] (f : ZMod p →+* R) (rho : R) (hrho : rho ^ 5 = 0) :
    (∏ j : Fin 5, ∏ k : Fin p, (rho + f (sixthShift p j + (k.val : ZMod p)))) = 0 := by
  simpa [fiveFactorBlock, pBlock, Polynomial.eval₂_finsetProd] using
    five_factor_nilpotent_evaluation p hp f rho hrho

end WPFiveFactor
