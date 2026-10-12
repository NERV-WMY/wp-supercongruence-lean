import WPFiniteHomogeneousD

open scoped BigOperators

namespace WPFiniteJNormalization

variable {K : Type*} [Field K]

noncomputable def Z (p : ℕ) (r t : K) : K :=
  (WPFiniteLoop.D (p - 1) (r * t) (-r) - WPFiniteLoop.D (p - 1) (r * t) r) / 2 +
    WPFiniteLoop.D (p - 1) (r * t) (r / 2) - WPFiniteLoop.D (p - 1) (r * t) (-(r / 2))

noncomputable def r (p : ℕ) : K := (WPFiniteInversion.integerFermatQuotient p 3 : K)

private theorem base_D (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (x y : ZMod p)
    (hy : y ≠ 0) (h1y : 1 - y ≠ 0) :
    WPFiniteLoop.D (p - 1) x y =
      (1 - y) * WPFiniteField.R p ((x - y) / (1 - y)) -
      (1 - y) * WPFiniteField.R p (-y / (1 - y)) +
      y * WPFiniteField.R p ((y - x) / y) := by
  rw [WPFiniteHomogeneousD.full_D_three_H2 p hp,
    WPFiniteHomogeneousD.H2_scaled_R p _ _ h1y,
    WPFiniteHomogeneousD.H2_scaled_R p _ _ h1y,
    WPFiniteHomogeneousD.H2_scaled_R p _ _ hy]
  simp only [ZMod.pow_card]

private theorem base_R_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (0 : ZMod p) = 0 ∧ WPFiniteField.R p (1 : ZMod p) = 0 ∧
      WPFiniteField.R p (-1 : ZMod p) = 0 := by
  constructor
  · unfold WPFiniteField.R
    apply Finset.sum_eq_zero
    intro j hj
    rw [zero_pow (by have h := (Finset.mem_Ico.mp hj).1; omega : j ≠ 0), zero_div]
  constructor
  · exact WPFiniteInversion.R_one_eq_zero p (by omega)
  · exact WPFiniteInversion.R_neg_one_eq_zero p hp

theorem R_three (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (3 : ZMod p) = 2 * WPFiniteField.R p (-2 : ZMod p) / 3 -
      2 * (WPFiniteNC122.q p) ^ 2 / 3 + 2 * WPFiniteNC122.q p * r p - 3 * (r p) ^ 2 / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have he := WPFiniteField.R_weight_two_reflection p (by omega) (3 : ZMod p)
  have hl := WPFiniteField.ell_reflection p (by omega) (3 : ZMod p)
  rw [show (1 - 3 : ZMod p) = -2 by ring, WPFiniteLoop.ell_neg_two p hp] at hl
  rw [ZMod.pow_card, ZMod.pow_card, show (1 - 3 : ZMod p) = -2 by ring, ← hl] at he
  unfold WPFiniteNC122.q r at *
  field_simp [h2, h3] at he ⊢
  linear_combination he

theorem R_neg_three (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (-3 : ZMod p) = 8 * (WPFiniteNC122.q p) ^ 2 / 3 -
      8 * WPFiniteField.R p (-2 : ZMod p) / 3 -
      8 * WPFiniteNC122.q p * r p + 3 * (r p) ^ 2 / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hl := WPFiniteField.ell_quadratic_distribution p
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (2 : ZMod p)
  rw [show (2 : ZMod p) ^ 2 = 4 by ring, ZMod.pow_card,
    WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp] at hl
  have he := WPFiniteField.R_weight_two_reflection p (by omega) (4 : ZMod p)
  rw [ZMod.pow_card, ZMod.pow_card, show (1 - 4 : ZMod p) = -3 by ring, hl] at he
  have hR4 : WPFiniteField.R p (4 : ZMod p) =
      -6 * (WPFiniteNC122.q p) ^ 2 - 2 * WPFiniteField.R p (-2 : ZMod p) :=
    WPFiniteInversion.R_four_eq_fermat p hp
  rw [hR4] at he
  unfold WPFiniteNC122.q r at *
  field_simp [h2, h3] at he ⊢
  linear_combination -he

theorem R_three_half (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (3 / 2 : ZMod p) = -WPFiniteField.R p (-2 : ZMod p) / 6 -
      (WPFiniteNC122.q p) ^ 2 / 3 + WPFiniteNC122.q p * r p - 3 * (r p) ^ 2 / 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  have hRn := WPFiniteField.R_inversion p (-2 : ZMod p) (neg_ne_zero.mpr h2)
  rw [ZMod.pow_card] at hRn
  have hln := WPFiniteField.ell_inversion p (-2 : ZMod p) (neg_ne_zero.mpr h2)
  rw [ZMod.pow_card, WPFiniteLoop.ell_neg_two p hp] at hln
  have harg : (-2 : ZMod p)⁻¹ = -(1 / 2) := by simp only [inv_neg, one_div]
  rw [harg] at hRn hln
  have he := WPFiniteField.R_weight_two_reflection p (by omega) (-(1 / 2) : ZMod p)
  rw [ZMod.pow_card, ZMod.pow_card,
    show (1 - -(1 / 2) : ZMod p) = 3 / 2 by field_simp [h2]; ring, hRn, hln] at he
  unfold WPFiniteNC122.q r at *
  field_simp [h2, h3, h4, h6] at he ⊢
  linear_combination 6 * he

theorem R_four_third (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteField.R p (4 / 3 : ZMod p) =
      -(8 * WPFiniteNC122.q p - 3 * r p) ^ 2 / 24 - WPFiniteField.R p (-3 : ZMod p) / 12 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h12 : (12 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 12 (Finset.mem_Ico.mpr (by omega))
  have h24 : (24 : ZMod p) ≠ 0 := by
    have he : (24 : ZMod p) = 2 * 12 := by ring
    rw [he]; exact mul_ne_zero h2 h12
  have hl := WPFiniteField.ell_quadratic_distribution p
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (2 : ZMod p)
  rw [show (2 : ZMod p) ^ 2 = 4 by ring, ZMod.pow_card,
    WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp] at hl
  have hln := WPFiniteField.ell_reflection p (by omega) (-3 : ZMod p)
  rw [show (1 - -3 : ZMod p) = 4 by ring, hl] at hln
  have hn3 : (-3 : ZMod p) ≠ 0 := neg_ne_zero.mpr h3
  have hi := WPFiniteField.ell_inversion p (-3 : ZMod p) hn3
  have hRi := WPFiniteField.R_inversion p (-3 : ZMod p) hn3
  rw [ZMod.pow_card, ← hln] at hi
  rw [ZMod.pow_card] at hRi
  have harg : (-3 : ZMod p)⁻¹ = -(1 / 3) := by simp only [inv_neg, one_div]
  rw [harg] at hi hRi
  have href := WPFiniteField.ell_reflection p (by omega) (4 / 3 : ZMod p)
  rw [show (1 - 4 / 3 : ZMod p) = -(1 / 3) by field_simp [h3]; ring, hi] at href
  have he := WPFiniteField.R_weight_two_reflection p (by omega) (4 / 3 : ZMod p)
  rw [ZMod.pow_card, ZMod.pow_card,
    show (1 - 4 / 3 : ZMod p) = -(1 / 3) by field_simp [h3]; ring, ← href, hRi] at he
  unfold WPFiniteNC122.q r at *
  field_simp [h2, h3, h12, h24] at he ⊢
  linear_combination 12 * he

private theorem base_D_end_rows (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (y : ZMod p)
    (hy : y ≠ 0) (h1y : 1 - y ≠ 0) :
    WPFiniteLoop.D (p - 1) 1 y = 2 * y * WPFiniteField.R p ((y - 1) / y) ∧
      WPFiniteLoop.D (p - 1) y y = y * WPFiniteField.R p ((y - 1) / y) := by
  have hz : (-y / (1 - y) : ZMod p) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hy) h1y
  have hi := WPFiniteField.R_inversion p (-y / (1 - y)) hz
  rw [ZMod.pow_card] at hi
  have harg : (-y / (1 - y) : ZMod p)⁻¹ = (y - 1) / y := by
    field_simp [hy, h1y]
    ring
  rw [harg] at hi
  have hc : (1 - y) * WPFiniteField.R p (-y / (1 - y)) =
      -y * WPFiniteField.R p ((y - 1) / y) := by
    rw [hi]
    field_simp [hy]
    ring
  have hr := base_R_zero p hp
  constructor
  · rw [base_D p hp 1 y hy h1y, div_self h1y, hr.2.1, mul_zero, zero_sub, hc]
    ring
  · rw [base_D p hp y y hy h1y, sub_self, zero_div, hr.1, mul_zero, zero_sub, hc]
    rw [zero_div, hr.1, mul_zero, add_zero]
    ring

theorem Z_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Z p (1 : ZMod p) 1 = 2 * WPFiniteField.R p (-2 : ZMod p) / 3 +
      (WPFiniteNC122.q p) ^ 2 / 3 + 2 * WPFiniteNC122.q p * r p - 3 * (r p) ^ 2 / 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hr := base_R_zero p hp
  have hR2 : WPFiniteField.R p (2 : ZMod p) = -(WPFiniteNC122.q p) ^ 2 :=
    WPFiniteInversion.R_two_eq_fermat p hp
  have hn := (base_D_end_rows p hp (-1) (neg_ne_zero.mpr one_ne_zero)
    (by simpa only [sub_neg_eq_add, show (1 + 1 : ZMod p) = 2 by ring] using h2)).1
  rw [show ((-1 : ZMod p) - 1) / -1 = 2 by field_simp; ring, hR2] at hn
  have hhalf : (1 / 2 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h2
  have hhalf1 : (1 - 1 / 2 : ZMod p) = 1 / 2 := by field_simp [h2]; ring
  have hh := (base_D_end_rows p hp (1 / 2) hhalf (by rw [hhalf1]; exact hhalf)).1
  rw [show ((1 / 2 : ZMod p) - 1) / (1 / 2) = -1 by field_simp [h2]; ring, hr.2.2] at hh
  have hnHalf1 : (1 - -(1 / 2) : ZMod p) = 3 / 2 := by field_simp [h2]; ring
  have hnh := (base_D_end_rows p hp (-(1 / 2)) (neg_ne_zero.mpr hhalf)
    (by rw [hnHalf1]; exact div_ne_zero h3 h2)).1
  rw [show ((-(1 / 2) : ZMod p) - 1) / -(1 / 2) = 3 by field_simp [h2]; ring] at hnh
  have h11 := WPFiniteDSource.D_at_one p hp (1 : ZMod p)
  rw [sub_self, hr.1] at h11
  unfold Z
  simp only [one_mul]
  rw [hn, h11, hh, hnh, R_three p hp]
  field_simp [h2, h3]
  ring

theorem Z_neg_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Z p (-1 : ZMod p) 1 = 2 * WPFiniteField.R p (-2 : ZMod p) -
      3 * (WPFiniteNC122.q p) ^ 2 + 6 * WPFiniteNC122.q p * r p := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hr := base_R_zero p hp
  have hR2 : WPFiniteField.R p (2 : ZMod p) = -(WPFiniteNC122.q p) ^ 2 :=
    WPFiniteInversion.R_two_eq_fermat p hp
  have hhalf : (1 / 2 : ZMod p) ≠ 0 := div_ne_zero one_ne_zero h2
  have hhalf1 : (1 - 1 / 2 : ZMod p) = 1 / 2 := by field_simp [h2]; ring
  have hnHalf1 : (1 - -(1 / 2) : ZMod p) = 3 / 2 := by field_simp [h2]; ring
  have hDneg := base_D p hp (-1) (-(1 / 2)) (neg_ne_zero.mpr hhalf)
    (by rw [hnHalf1]; exact div_ne_zero h3 h2)
  have hDpos := base_D p hp (-1) (1 / 2) hhalf (by rw [hhalf1]; exact hhalf)
  rw [hnHalf1,
    show ((-1 : ZMod p) - -(1 / 2)) / (3 / 2) = -(1 / 3) by field_simp [h2, h3]; ring,
    show (-(-(1 / 2)) : ZMod p) / (3 / 2) = 1 / 3 by field_simp [h2, h3],
    show ((-(1 / 2) : ZMod p) - -1) / -(1 / 2) = -1 by field_simp [h2]; ring,
    hr.2.2, mul_zero, add_zero] at hDneg
  rw [hhalf1,
    show ((-1 : ZMod p) - 1 / 2) / (1 / 2) = -3 by field_simp [h2]; ring,
    show (-(1 / 2) : ZMod p) / (1 / 2) = -1 by field_simp [h2],
    show ((1 / 2 : ZMod p) - -1) / (1 / 2) = 3 by field_simp [h2]; ring,
    hr.2.2, mul_zero, sub_zero] at hDpos
  have hRthird := WPFiniteField.R_inversion p (3 : ZMod p) h3
  have hRnthird := WPFiniteField.R_inversion p (-3 : ZMod p) (neg_ne_zero.mpr h3)
  rw [ZMod.pow_card] at hRthird hRnthird
  simp only [inv_neg] at hRnthird
  simp only [← one_div] at hRthird hRnthird
  rw [hRthird, hRnthird] at hDneg
  have hdiag := (base_D_end_rows p hp (-1) (neg_ne_zero.mpr one_ne_zero)
    (by simpa only [sub_neg_eq_add, show (1 + 1 : ZMod p) = 2 by ring] using h2)).2
  rw [show ((-1 : ZMod p) - 1) / -1 = 2 by field_simp; ring, hR2] at hdiag
  have hD1 := WPFiniteDSource.D_at_one p hp (-1 : ZMod p)
  rw [show (1 - -1 : ZMod p) = 2 by ring, hR2] at hD1
  unfold Z
  simp only [mul_one, neg_neg, neg_div]
  rw [hD1, hdiag, hDneg, hDpos, R_three p hp, R_neg_three p hp]
  field_simp [h2, h3]
  ring

theorem Z_two (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Z p (2 : ZMod p) 1 = 3 * WPFiniteField.R p (-2 : ZMod p) / 2 -
      7 * (WPFiniteNC122.q p) ^ 2 / 2 + 3 * WPFiniteNC122.q p * r p := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  have h12 : (12 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 12 (Finset.mem_Ico.mpr (by omega))
  have h24 : (24 : ZMod p) ≠ 0 := by rw [show (24 : ZMod p) = 2 * 12 by ring]; exact mul_ne_zero h2 h12
  have hr := base_R_zero p hp
  have hR2 : WPFiniteField.R p (2 : ZMod p) = -(WPFiniteNC122.q p) ^ 2 :=
    WPFiniteInversion.R_two_eq_fermat p hp
  have hDh := WPFiniteField.R_inversion p (2 : ZMod p) h2
  rw [ZMod.pow_card] at hDh
  simp only [← one_div] at hDh
  have hDneg := base_D p hp 2 (-2) (neg_ne_zero.mpr h2)
    (by rw [show (1 - -2 : ZMod p) = 3 by ring]; exact h3)
  rw [show (1 - -2 : ZMod p) = 3 by ring,
    show (2 - -2 : ZMod p) = 4 by ring,
    show (-(-2) : ZMod p) = 2 by ring,
    show ((-2 : ZMod p) - 2) / -2 = 2 by field_simp [h2]; ring, hR2] at hDneg
  have hDdiag := (base_D_end_rows p hp 2 h2
    (by rw [show (1 - 2 : ZMod p) = -1 by ring]; exact neg_ne_zero.mpr one_ne_zero)).2
  rw [show ((2 : ZMod p) - 1) / 2 = 1 / 2 by ring, hDh, hR2] at hDdiag
  have hD1 := WPFiniteDSource.D_at_one p hp (2 : ZMod p)
  rw [show (1 - 2 : ZMod p) = -1 by ring, hr.2.2] at hD1
  have hDn1 := WPFiniteDSource.D_at_neg_one p hp (2 : ZMod p)
  rw [show ((1 + 2) / 2 : ZMod p) = 3 / 2 by ring,
    show (1 + 2 : ZMod p) = 3 by ring] at hDn1
  have hRi := WPFiniteField.R_inversion p (3 / 2 : ZMod p) (div_ne_zero h3 h2)
  rw [ZMod.pow_card, show (3 / 2 : ZMod p)⁻¹ = 2 / 3 by field_simp [h2, h3]] at hRi
  rw [hRi] at hDneg
  unfold Z
  simp only [mul_one]
  rw [div_self h2, hDneg, hDdiag, hD1, hDn1, R_four_third p hp,
    R_three_half p hp, R_three p hp, R_neg_three p hp]
  field_simp [h2, h3, h4, h6, h12, h24]
  ring

theorem F_b_Z (p : ℕ) (t : K) (h2 : (2 : K) ≠ 0) :
    WPFiniteLogProduct.F_b p t = 2 * Z p 1 t + 2 * Z p (-1) t -
      2 * Z p 2 t - 2 * Z p (-2) t := by
  unfold WPFiniteLogProduct.F_b WPFiniteDReciprocity.N_o Z
  simp only [one_mul, neg_mul, neg_neg, neg_div, div_self h2]
  field_simp [h2]
  ring

theorem F_d_Z (p : ℕ) (t : K) (h2 : (2 : K) ≠ 0) :
    WPFiniteDReciprocity.F_d p t = 2 * Z p 1 t - 2 * Z p (-1) t -
      Z p 2 t + Z p (-2) t := by
  unfold WPFiniteDReciprocity.F_d WPFiniteDReciprocity.M Z
  simp only [one_mul, neg_mul, neg_neg, neg_div, div_self h2]
  field_simp [h2]
  ring

noncomputable def F_e (p : ℕ) (t : K) : K := (Z p 1 t + Z p (-1) t) / 2 + Z p 2 t + Z p (-2) t

noncomputable def M_E (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (8 * WPFiniteNC122.q p - 6 * r p) * WPFiniteField.E p t +
    (4 * WPFiniteNC122.q p - 3 * r p) * WPFiniteField.E p (2 * t)

noncomputable def M_O (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  -3 * r p * WPFiniteField.O p t + 3 * r p * WPFiniteField.O p (2 * t) / 2

noncomputable def V_cub (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (t ^ p) ^ 2 * WPFiniteLogProduct.F_b p t + t ^ p * WPFiniteDReciprocity.F_d p t +
    F_e p t + t ^ p * M_E p t + M_O p t

/-- The actual original endpoint normalization, before any value theorem. -/
noncomputable def K_J (p : ℕ) [Fact p.Prime] [CharP K p] : K := V_cub p (1 : K)

theorem Z_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (a b : ZMod p) :
    (ZMod.castHom (dvd_refl p) K) (Z p a b) =
      Z p ((ZMod.castHom (dvd_refl p) K) a) ((ZMod.castHom (dvd_refl p) K) b) := by
  have hd : ∀ x y : ZMod p,
      (ZMod.castHom (dvd_refl p) K) (WPFiniteLoop.D (p - 1) x y) =
        WPFiniteLoop.D (p - 1) ((ZMod.castHom (dvd_refl p) K) x)
          ((ZMod.castHom (dvd_refl p) K) y) := by
    intro x y
    simp only [WPFiniteLoop.D, map_sum, map_div₀, map_mul, map_pow, map_natCast]
  simp only [Z, map_sub, map_add, map_div₀, map_mul, map_neg, map_ofNat, hd]

theorem Z_rational_values (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    Z p (1 : K) 1 = 2 * WPFiniteField.R p (-2 : K) / 3 +
      (WPFiniteNC122.q p) ^ 2 / 3 + 2 * WPFiniteNC122.q p * r p - 3 * (r p) ^ 2 / 2 ∧
    Z p (-1 : K) 1 = 2 * WPFiniteField.R p (-2 : K) -
      3 * (WPFiniteNC122.q p) ^ 2 + 6 * WPFiniteNC122.q p * r p ∧
    Z p (2 : K) 1 = 3 * WPFiniteField.R p (-2 : K) / 2 -
      7 * (WPFiniteNC122.q p) ^ 2 / 2 + 3 * WPFiniteNC122.q p * r p := by
  have h1 := congrArg (ZMod.castHom (dvd_refl p) K) (Z_one p hp)
  have hn := congrArg (ZMod.castHom (dvd_refl p) K) (Z_neg_one p hp)
  have h2 := congrArg (ZMod.castHom (dvd_refl p) K) (Z_two p hp)
  simp only [Z_castHom, map_sub, map_add, map_div₀, map_mul, map_neg, map_pow,
    map_ofNat, map_one, WPFiniteNC122.q, r, map_intCast] at h1 hn h2
  have hr : (ZMod.castHom (dvd_refl p) K) (WPFiniteField.R p (-2 : ZMod p)) =
      WPFiniteField.R p (-2 : K) := by
    change (ZMod.castHom (dvd_refl p) K) (WPFiniteInversion.R p (-2)) = WPFiniteField.R p (-2 : K)
    rw [← WPFiniteField.R_castHom, map_neg, map_ofNat]
  rw [hr] at h1 hn h2
  exact ⟨h1, hn, h2⟩

theorem K_J_actual_endpoint (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (K_J p : K) = 9 * Z p (1 : K) 1 / 2 + Z p (-1 : K) 1 / 2 - 2 * Z p (2 : K) 1 -
      8 * (WPFiniteNC122.q p) ^ 2 - 6 * WPFiniteNC122.q p * r p + 27 * (r p) ^ 2 / 4 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have hl1 : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K) (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hlN1 : WPFiniteField.ell p (-1 : K) = -2 * WPFiniteNC122.q p := by
    have he := WPFiniteField.ell_reflection p (by omega) (-1 : K)
    rw [show (1 - -1 : K) = 2 by ring, WPFiniteLoop.ell_two p hp] at he
    exact he.symm
  have hE1 : WPFiniteField.E p (1 : K) = -WPFiniteNC122.q p := by
    unfold WPFiniteField.E; rw [hl1, hlN1]; field_simp [h2]; ring
  have hO1 : WPFiniteField.O p (1 : K) = WPFiniteNC122.q p := by
    unfold WPFiniteField.O; rw [hl1, hlN1]; field_simp [h2]; ring
  have hE2 : WPFiniteField.E p (2 : K) = -3 * r p / 2 := by
    unfold WPFiniteField.E; rw [WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp]
    unfold r; field_simp [h2]; ring
  have hO2 : WPFiniteField.O p (2 : K) = -2 * WPFiniteNC122.q p + 3 * r p / 2 := by
    unfold WPFiniteField.O; rw [WPFiniteLoop.ell_two p hp, WPFiniteLoop.ell_neg_two p hp]
    unfold WPFiniteNC122.q r; field_simp [h2]; ring
  unfold K_J V_cub
  rw [F_b_Z p _ h2, F_d_Z p _ h2]
  simp only [one_pow, one_mul]
  unfold F_e M_E M_O
  rw [hE1, hO1, mul_one, hE2, hO2]
  field_simp [h2, h4]
  ring

theorem K_J_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (K_J p : K) = WPFiniteField.R p (-2 : K) - (WPFiniteNC122.q p) ^ 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have he := Z_rational_values (K := K) p hp
  rw [K_J_actual_endpoint p hp, he.1, he.2.1, he.2.2]
  field_simp [h2, h3, h4]
  ring

noncomputable def U_J (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  t ^ p * WPFiniteLogProduct.F_b p t + WPFiniteDReciprocity.F_d p t + M_E p t - K_J p

theorem U_J_original_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (t : K) (ht : t ≠ 0) :
    U_J p t = WPFiniteLoop.A p t - WPFiniteLoop.B p t + WPFiniteDReciprocity.At p t -
      WPFiniteDReciprocity.Bt p t + WPFiniteLoop.Chi p t -
      2 * (WPFiniteField.E p (2 * t) - WPFiniteField.E p t) ^ 2 +
      (4 * WPFiniteNC122.q p - 3 * r p) *
        (2 * WPFiniteField.E p t + WPFiniteField.E p (2 * t)) - 2 * (WPFiniteNC122.q p) ^ 2 := by
  unfold U_J
  rw [WPFiniteLogProduct.F_b_original_contraction p hp t ht,
    WPFiniteDReciprocity.F_d_original_contraction p hp, K_J_value p hp]
  unfold M_E
  ring

end WPFiniteJNormalization
