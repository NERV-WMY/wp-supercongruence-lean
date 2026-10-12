import WPGammaArithmetic.Basic
import Mathlib.Tactic

namespace WPGammaArithmetic

theorem gamma_ne_zero (k : ℕ) : gamma k ≠ 0 := by
  unfold gamma
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem factorial_valuation_below_square (p n : ℕ) (hp : p.Prime)
    (hn : n < p ^ 2) : padicValNat p n.factorial = n / p := by
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (p := p) (b := 2)
    (Nat.log_lt_of_lt_pow' (by decide) hn)]
  norm_num [Finset.sum_Ico_succ_top]

theorem gamma_cutoff_bounds (p k : ℕ) (hp7 : 7 ≤ p) (hk : k ≤ 3 * p - 1) :
    k < p ^ 2 ∧ 2 * k + 1 < p ^ 2 := by
  have hk' : k + 1 ≤ 3 * p := by omega
  constructor <;> nlinarith [sq_nonneg (p : ℤ)]

theorem four_valuation_zero (p : ℕ) (_hp : p.Prime) (hp7 : 7 ≤ p) :
    padicValRat p (4 : ℚ) = 0 := by
  have hnd : ¬ p ∣ 4 := by
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 4) hd
    omega
  simpa only [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num,
    padicValRat.of_nat, Int.natCast_eq_zero] using padicValNat.eq_zero_of_not_dvd hnd

theorem gamma_valuation_formula (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) :
    padicValRat p (gamma k) =
      2 * (k / p : ℕ) - (((2 * k + 1) / p : ℕ) : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hb := gamma_cutoff_bounds p k hp7 hk
  have hf : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((2 * k + 1).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold gamma
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hf)) hd,
    padicValRat.mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hf),
    padicValRat.pow, padicValRat.pow, four_valuation_zero p hp hp7,
    padicValRat.of_nat, padicValRat.of_nat,
    factorial_valuation_below_square p k hp hb.1,
    factorial_valuation_below_square p (2 * k + 1) hp hb.2]
  ring

theorem gamma_residue_cutoff (p a r : ℕ) (ha : a ≤ 2) (hr : r < p) :
    a * p + r ≤ 3 * p - 1 := by
  have ham := Nat.mul_le_mul_right p ha
  omega

theorem gamma_residue_valuation (p a r : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ha : a ≤ 2) (hr : r < p) :
    padicValRat p (gamma (a * p + r)) = -(((2 * r + 1) / p : ℕ) : ℤ) := by
  have hq : (a * p + r) / p = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right r a hp.pos, Nat.div_eq_of_lt hr]
    omega
  have hq2 : (2 * (a * p + r) + 1) / p = 2 * a + (2 * r + 1) / p := by
    have he : 2 * (a * p + r) + 1 = (2 * r + 1) + (2 * a) * p := by ring
    rw [he, Nat.add_mul_div_right (2 * r + 1) (2 * a) hp.pos]
    omega
  rw [gamma_valuation_formula p (a * p + r) hp hp7 (gamma_residue_cutoff p a r ha hr),
    hq, hq2]
  push_cast
  ring

theorem gamma_residue_low_band (p a r : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ha : a ≤ 2) (hr : r < p) (hband : 2 * r + 1 < p) :
    padicValRat p (gamma (a * p + r)) = 0 := by
  rw [gamma_residue_valuation p a r hp hp7 ha hr, Nat.div_eq_of_lt hband]
  simp

theorem gamma_residue_high_band (p a r : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (ha : a ≤ 2) (hr : r < p) (hband : p ≤ 2 * r + 1) :
    padicValRat p (gamma (a * p + r)) = -1 := by
  have hq : (2 * r + 1) / p = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [gamma_residue_valuation p a r hp hp7 ha hr, hq]
  simp

theorem gamma_valuation_values (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) :
    padicValRat p (gamma k) = 0 ∨ padicValRat p (gamma k) = -1 := by
  have ha : k / p ≤ 2 := by
    have hk' : k < 3 * p := by omega
    have := (Nat.div_lt_iff_lt_mul hp.pos).mpr hk'
    omega
  have hr := Nat.mod_lt k hp.pos
  have he : k = (k / p) * p + k % p := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod k p).symm
  rw [he]
  by_cases hb : 2 * (k % p) + 1 < p
  · exact Or.inl (gamma_residue_low_band p (k / p) (k % p) hp hp7 ha hr hb)
  · exact Or.inr (gamma_residue_high_band p (k / p) (k % p) hp hp7 ha hr (by omega))

theorem gamma_valuation_ge_neg_one (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) : -1 ≤ padicValRat p (gamma k) := by
  rcases gamma_valuation_values p k hp hp7 hk with h | h <;> omega

theorem p_mul_gamma_integral (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) : 0 ≤ padicValRat p ((p : ℚ) * gamma k) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValRat.mul (Nat.cast_ne_zero.mpr hp.ne_zero) (gamma_ne_zero k),
    padicValRat.self hp.one_lt]
  have := gamma_valuation_ge_neg_one p k hp hp7 hk
  omega

end WPGammaArithmetic
