import WPRho

noncomputable section

namespace WPToricRho

open Polynomial

def shift (p : ℕ) (j : Fin 3) : ZMod p :=
  ((2 * j.val + 1 : ℕ) : ZMod p) * (6 : ZMod p)⁻¹

theorem shift_literal (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    shift p = ![(1 / 6 : ZMod p), 1 / 2, 5 / 6] := by
  have h6 : (6 : ZMod p) ≠ 0 := (WPFiveFactor.six_unit p Fact.out hp7).ne_zero
  have h23 : (2 : ZMod p) * 3 ≠ 0 := by norm_num; exact h6
  have h2 : (2 : ZMod p) ≠ 0 := (mul_ne_zero_iff.mp h23).1
  funext j
  fin_cases j <;> simp [shift, div_eq_mul_inv]
  field_simp
  ring

variable {p : ℕ} {R : Type*} [CommRing R]

def factor (f : ZMod p →+* R) (rho : R) (j : Fin 3) (k : ℕ) : R :=
  rho + f (shift p j + (k : ZMod p))

def stepProduct (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  ∏ j : Fin 3, factor f rho j n

def numerator (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  ∏ j : Fin 3, ∏ k ∈ Finset.range n, factor f rho j k

def denominator (rho : R) (n : ℕ) : R :=
  ∏ k ∈ Finset.range n, (rho + ((k + 1 : ℕ) : R)) ^ 3

def hCoeff (f : ZMod p →+* R) (rho : R) (n : ℕ) : R :=
  numerator f rho n * Ring.inverse (denominator rho n)

theorem numerator_literal [Fact p.Prime] (hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (rho : R) (n : ℕ) :
    numerator f rho n = ∏ k ∈ Finset.range n,
      (rho + f ((1 / 6 : ZMod p) + (k : ZMod p))) *
      (rho + f ((1 / 2 : ZMod p) + (k : ZMod p))) *
      (rho + f ((5 / 6 : ZMod p) + (k : ZMod p))) := by
  unfold numerator
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  simp [factor, shift_literal p hp7, Fin.prod_univ_succ, mul_assoc]

theorem hCoeff_literal [Fact p.Prime] (hp7 : 7 ≤ p)
    (f : ZMod p →+* R) (rho : R) (n : ℕ) :
    hCoeff f rho n =
      (∏ k ∈ Finset.range n, (rho + f ((1 / 6 : ZMod p) + (k : ZMod p))) *
        (rho + f ((1 / 2 : ZMod p) + (k : ZMod p))) * (rho + f ((5 / 6 : ZMod p) + (k : ZMod p)))) *
      Ring.inverse (∏ k ∈ Finset.range n, (rho + ((k + 1 : ℕ) : R)) ^ 3) := by
  rw [hCoeff, numerator_literal hp7]
  rfl

theorem denominator_factor_unit (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) (k : ℕ) (hk0 : 0 < k) (hkp : k < p) :
    IsUnit (rho + (k : R)) := by
  exact (show IsNilpotent rho from ⟨3, hrho⟩).isUnit_add_right_of_commute
    (WPRho.residue_unit hp f k hk0 hkp) (Commute.all _ _)

theorem denominator_unit (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) (n : ℕ) (hn : n < p) :
    IsUnit (denominator rho n) := by
  apply IsUnit.prod_iff.mpr
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  exact (denominator_factor_unit hp f rho hrho (k + 1) (by omega) (by omega)).pow 3

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
    denominator rho (n + 1) = denominator rho n * (rho + ((n + 1 : ℕ) : R)) ^ 3 := by
  exact Finset.prod_range_succ _ _

theorem hCoeff_recurrence (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) (n : ℕ) (hn : n + 1 < p) :
    (rho + ((n + 1 : ℕ) : R)) ^ 3 * hCoeff f rho (n + 1) =
      stepProduct f rho n * hCoeff f rho n := by
  have hunit := denominator_unit hp f rho hrho n (by omega)
  have hnext := (denominator_factor_unit hp f rho hrho (n + 1) (by omega) hn).pow 3
  unfold hCoeff
  rw [numerator_succ, denominator_succ, Ring.inverse_mul (Or.inl hunit)]
  calc
    (rho + ((n + 1 : ℕ) : R)) ^ 3 *
        (numerator f rho n * stepProduct f rho n *
          (Ring.inverse ((rho + ((n + 1 : ℕ) : R)) ^ 3) *
            Ring.inverse (denominator rho n))) =
      ((rho + ((n + 1 : ℕ) : R)) ^ 3 *
        Ring.inverse ((rho + ((n + 1 : ℕ) : R)) ^ 3)) *
          (stepProduct f rho n * (numerator f rho n * Ring.inverse (denominator rho n))) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hnext, one_mul]

theorem numerator_full_block (hp : p.Prime) (f : ZMod p →+* R) (rho : R) :
    numerator f rho p = (rho ^ p - rho) ^ 3 := by
  have hb (j : Fin 3) : (∏ k ∈ Finset.range p, factor f rho j k) = rho ^ p - rho := by
    have hh := Fin.prod_univ_eq_prod_range
      (fun k : ℕ => (X + C (shift p j + (k : ZMod p)) : Polynomial (ZMod p))) p
    have he := congrArg (fun P : Polynomial (ZMod p) => P.eval₂ f rho)
      (hh.symm.trans (WPFiveFactor.pBlock_exact p hp (shift p j)))
    simpa [Polynomial.eval₂_finsetProd, factor] using he
  simp only [numerator, hb, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem numerator_full_block_zero (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) : numerator f rho p = 0 := by
  rw [numerator_full_block hp f rho]
  have hpEq : p = (p - 1) + 1 := by have := hp.pos; omega
  have he : rho ^ p - rho = rho * (rho ^ (p - 1) - 1) := by
    calc
      rho ^ p - rho = rho ^ ((p - 1) + 1) - rho :=
        congrArg (fun n : ℕ => rho ^ n - rho) hpEq
      _ = rho * (rho ^ (p - 1) - 1) := by rw [pow_succ', mul_sub, mul_one]
  rw [he, mul_pow, hrho, zero_mul]

theorem hCoeff_terminal (hp : p.Prime) (f : ZMod p →+* R)
    (rho : R) (hrho : rho ^ 3 = 0) :
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

end WPToricRho

