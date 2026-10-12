import WPFiniteEntropy
import WPFiniteReflection

namespace WPFiniteInversion

theorem R_neg_one_eq_zero (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    R p (-1) = 0 := by
  have he := R_inversion p (-1) (neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0))
  rw [ZMod.pow_card] at he
  simp only [inv_neg, inv_one, neg_mul, one_mul] at he
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hz : (2 : ZMod p) * R p (-1) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left htwo

theorem R_two_eq_fermat (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    R p 2 = -(integerFermatQuotient p 2 : ZMod p) ^ 2 := by
  have he := R_weight_two_reflection p (by omega) (2 : ZMod p)
  rw [ZMod.pow_card, ZMod.pow_card, ell_two_eq_fermat p (by omega)] at he
  norm_num only [show (1 - 2 : ZMod p) = -1 by ring,
    R_neg_one_eq_zero p hp19, mul_zero, add_zero] at he
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  field_simp [htwo] at he
  exact he

theorem R_four_eq_fermat (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    R p 4 = -6 * (integerFermatQuotient p 2 : ZMod p) ^ 2 - 2 * R p (-2) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have he := R_quadratic_distribution p hodd (2 : ZMod p)
  rw [ZMod.pow_card, R_two_eq_fermat p hp19] at he
  norm_num only [show (2 : ZMod p) ^ 2 = 4 by ring] at he
  linear_combination he

theorem R_neg_four_five_reflection (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    -4 * R p (-4) + 5 * R p 5 =
      -(8 * (integerFermatQuotient p 2 : ZMod p) -
        5 * (integerFermatQuotient p 5 : ZMod p)) ^ 2 / 2 := by
  have he := R_weight_two_reflection p (by omega) (-4 : ZMod p)
  rw [ZMod.pow_card, ZMod.pow_card, ell_neg_four_eq_fermat p (by omega)] at he
  norm_num only [show (1 - (-4) : ZMod p) = 5 by ring] at he
  exact he

theorem R_sixteen_distribution (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    R p 16 = 10 * R p 4 - 6 * R p (-4) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have he := R_quadratic_distribution p hodd (4 : ZMod p)
  rw [ZMod.pow_card] at he
  norm_num only [show (4 : ZMod p) ^ 2 = 16 by ring] at he
  linear_combination he

theorem rational_weight_two_aggregate (p : ℕ) [Fact p.Prime] (hp19 : 19 ≤ p) :
    R p 16 + 20 * R p (-2) + (15 / 2 : ZMod p) * R p 5 =
      -108 * (integerFermatQuotient p 2 : ZMod p) ^ 2 +
        60 * (integerFermatQuotient p 2 : ZMod p) *
          (integerFermatQuotient p 5 : ZMod p) -
        (75 / 4 : ZMod p) * (integerFermatQuotient p 5 : ZMod p) ^ 2 := by
  rw [R_sixteen_distribution p hp19, R_four_eq_fermat p hp19]
  have he := R_neg_four_five_reflection p hp19
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact mul_ne_zero htwo htwo
  field_simp [htwo] at he
  field_simp [htwo, hfour]
  linear_combination 6 * he

end WPFiniteInversion
