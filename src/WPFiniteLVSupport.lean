import WPFiniteLVSource

open Polynomial

namespace WPFiniteLVSupport

open WPFiniteAffineLog WPFiniteKSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPFiniteABSourceTail WPFiniteWSource WPFinitePSource WPFiniteLVSource

variable {K : Type*} [Field K]

noncomputable def regularRemainder (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[X] :=
  LV p - 3 * X ^ p * A p (W p) u

noncomputable def lowConic (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  C (WPFiniteNC122.q p / 5) + 3 * EP p +
    C (6 / 5 : K) * ((EP p).comp (2 * X) - EP p) +
    4 * X ^ p * OP p - 2 * X ^ p * (OP p).comp (2 * X)

theorem regularRemainder_conic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (regularRemainder p u).comp conic = lowConic p := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hc5 : 5 * C (5 : K)⁻¹ = (1 : K[X]) := by
    change C (5 : K) * C (5 : K)⁻¹ = 1
    rw [← C_mul, mul_inv_cancel₀ h5, C_1]
  have hc15 : 15 * C (15 : K)⁻¹ = (1 : K[X]) := by
    change C (15 : K) * C (15 : K)⁻¹ = 1
    rw [← C_mul, mul_inv_cancel₀ h15, C_1]
  have h15poly : (15 : K[X]) ≠ 0 := by
    change C (15 : K) ≠ 0
    exact C_ne_zero.mpr h15
  have h5pow : (5 : K[X]) ^ p = 5 := by
    change C (5 : K) ^ p = C (5 : K)
    rw [← map_pow]
    congr 1
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have hconic : (conic : K[X]) ^ p = 5 * X ^ (2 * p) - 1 := by
    unfold conic
    rw [sub_pow_char, one_pow, mul_pow, h5pow, ← pow_mul]
  have ha := congrArg (fun Q : K[X] => Q.comp conic)
    (A_literal_even_difference (K := K) p hp u hu)
  simp only [mul_comp, C_comp, add_comp, comp_assoc, squaredCoordinate_conic p hp,
    deltaE_square p hp] at ha
  rw [regularRemainder, sub_comp, mul_comp, mul_comp, ofNat_comp, pow_comp,
    X_comp, LV_conic p hp, ha, hconic, UW1_polynomial p hp]
  unfold lowConic UW1rhs
  apply mul_left_cancel₀ h15poly
  simp only [div_eq_mul_inv, map_mul, map_neg, map_ofNat, Nat.cast_ofNat]
  linear_combination
    12 * (5 * X ^ (2 * p) - 1) *
      (C (WPFiniteNC122.q p) + (EP p).comp (2 * X) - EP p) * hc15 -
    3 * (C (WPFiniteNC122.q p) + 6 * ((EP p).comp (2 * X) - EP p)) * hc5

theorem even_odd_degree (p : ℕ) :
    (EP p : K[X]).natDegree ≤ p - 1 ∧ (OP p : K[X]).natDegree ≤ p - 1 := by
  have hneg : ((LP p : K[X]).comp (-X)).natDegree ≤ p - 1 := by
    have h := natDegree_comp_le (p := LP p) (q := (-X : K[X]))
    simpa only [Nat.mul_one] using h.trans
      (Nat.mul_le_mul (LP_natDegree_le p) (show (-X : K[X]).natDegree ≤ 1 by simp))
  constructor
  · unfold EP
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans
      (max_le (LP_natDegree_le p) hneg))
  · unfold OP
    exact (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
      (max_le (LP_natDegree_le p) hneg))

private theorem degree_scaled (c : K) (Q : K[X]) (n : ℕ) (hQ : Q.natDegree ≤ n) :
    (C c * Q).natDegree ≤ n := (natDegree_C_mul_le c Q).trans hQ

private theorem degree_comp_two (Q : K[X]) (n : ℕ) (hQ : Q.natDegree ≤ n) :
    (Q.comp (2 * X)).natDegree ≤ n := by
  have h2X : (2 * X : K[X]).natDegree ≤ 1 := by
    change (C (2 : K) * X).natDegree ≤ 1
    exact (natDegree_C_mul_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by simpa using Nat.mul_le_mul hQ h2X)

theorem lowConic_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (lowConic p : K[X]).natDegree ≤ 2 * p - 1 := by
  have hEO := even_odd_degree (K := K) p
  have hE2 := degree_comp_two (EP p : K[X]) (p - 1) hEO.1
  have hO2 := degree_comp_two (OP p : K[X]) (p - 1) hEO.2
  have hdelta : ((EP p).comp (2 * X) - EP p : K[X]).natDegree ≤ p - 1 :=
    (natDegree_sub_le _ _).trans (max_le hE2 hEO.1)
  have h3E : (3 * EP p : K[X]).natDegree ≤ p - 1 := by
    change (C (3 : K) * EP p).natDegree ≤ p - 1
    exact degree_scaled _ _ _ hEO.1
  have hd : (C (6 / 5 : K) * ((EP p).comp (2 * X) - EP p)).natDegree ≤ p - 1 :=
    degree_scaled _ _ _ hdelta
  have hpO : (X ^ p * OP p : K[X]).natDegree ≤ 2 * p - 1 := by
    exact natDegree_mul_le.trans ((Nat.add_le_add (by simp : (X ^ p : K[X]).natDegree ≤ p) hEO.2).trans (by omega))
  have hpO2 : (X ^ p * (OP p).comp (2 * X) : K[X]).natDegree ≤ 2 * p - 1 := by
    exact natDegree_mul_le.trans ((Nat.add_le_add (by simp : (X ^ p : K[X]).natDegree ≤ p) hO2).trans (by omega))
  have h4O : (4 * X ^ p * OP p : K[X]).natDegree ≤ 2 * p - 1 := by
    rw [mul_assoc]
    change (C (4 : K) * (X ^ p * OP p)).natDegree ≤ 2 * p - 1
    exact degree_scaled _ _ _ hpO
  have h2O : (2 * X ^ p * (OP p).comp (2 * X) : K[X]).natDegree ≤ 2 * p - 1 := by
    rw [mul_assoc]
    change (C (2 : K) * (X ^ p * (OP p).comp (2 * X))).natDegree ≤ 2 * p - 1
    exact degree_scaled _ _ _ hpO2
  unfold lowConic
  apply natDegree_sub_le _ _ |>.trans
  apply max_le _ h2O
  apply natDegree_add_le _ _ |>.trans
  apply max_le _ h4O
  apply natDegree_add_le _ _ |>.trans
  apply max_le _ (hd.trans (by omega))
  exact (natDegree_add_le _ _).trans (max_le (by simp) (h3E.trans (by omega)))

/-- UW1 bounds the entire regular difference below p, before any derivative kernel step. -/
theorem regularRemainder_prebound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (regularRemainder p u).natDegree ≤ p - 1 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hconic : (conic : K[X]).natDegree = 2 := by
    unfold conic
    change (C (5 : K) * X ^ 2 - 1).natDegree = 2
    compute_degree
    exact h5
  have h := lowConic_degree (K := K) p hp
  rw [← regularRemainder_conic p hp u hu, natDegree_comp, hconic] at h
  omega

end WPFiniteLVSupport
