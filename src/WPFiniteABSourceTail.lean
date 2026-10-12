import WPFiniteProductTail

open scoped BigOperators
open Polynomial

namespace WPFiniteABSourceTail

open WPFiniteAffineLog WPFiniteProductTail WPFiniteCubicLog

variable {K : Type*} [Field K]

theorem strictTail_add (p : ℕ) (hp : 0 < p) (P Q : K[X]) :
    strictTail p (P + Q) = strictTail p P + strictTail p Q := by
  ext j
  simp only [strictTail_coeff p hp, coeff_add]
  split_ifs <;> ring

theorem strictTail_sub (p : ℕ) (hp : 0 < p) (P Q : K[X]) :
    strictTail p (P - Q) = strictTail p P - strictTail p Q := by
  ext j
  simp only [strictTail_coeff p hp, coeff_sub]
  split_ifs <;> ring

theorem strictTail_C_mul (p : ℕ) (hp : 0 < p) (a : K) (P : K[X]) :
    strictTail p (C a * P) = C a * strictTail p P := by
  ext j
  simp only [strictTail_coeff p hp, coeff_C_mul]
  split_ifs <;> ring

theorem strictTail_low (p : ℕ) (hp : 0 < p) (P : K[X]) (hP : P.natDegree ≤ p) :
    strictTail p P = 0 := by
  ext j
  rw [strictTail_coeff p hp, coeff_zero]
  by_cases hj0 : j = 0
  · rw [if_pos hj0]
  · rw [if_neg hj0]
    by_cases hjp : j < p
    · rw [if_pos hjp]
      exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega))
    · rw [if_neg hjp]

noncomputable def epsilon (p : ℕ) : K := (5 : K) ^ ((p - 1) / 2)

noncomputable def uSlot (p : ℕ) [Fact p.Prime] [CharP K p] : K → K := fun u =>
  -4 * (WPFiniteNC122.q p + WPFifthEntropy.C p u) / 15

noncomputable def A (p : ℕ) [Fact p.Prime] [CharP K p] (W : K[X]) (u : K) : K[X] :=
  C (uSlot p u) - C (2 / epsilon p) * W

noncomputable def Bpoly (p : ℕ) [Fact p.Prime] [CharP K p] (W : K[X]) (u : K) : K[X] :=
  C (17 * WPFifthEntropy.C p u / 15) + C (17 / (2 * epsilon p)) * W

noncomputable def logTrace (p : ℕ) : K[X] :=
  -C (1 / 4 : K) * (LP p).comp (C 4 * X) +
    C 4 * (LP p).comp (C (1 / 4) * X)

noncomputable def B0 (p : ℕ) [Fact p.Prime] [CharP K p] (W : K[X]) (u : K) : K[X] :=
  Bpoly p W u + C (2 / 15 : K) * logTrace p

noncomputable def JdifferenceP (p : ℕ) (W : K[X]) : K[X] :=
  primitiveDifferenceP p W (1 / 4) - primitiveDifferenceP p W 4

theorem JdifferenceP_eval (p : ℕ) (W : K[X]) (z : K) :
    (JdifferenceP p W).eval z = unitPrimitive p W z (1 / 4) - unitPrimitive p W z 4 -
      originPrimitive p W (1 / 4) + originPrimitive p W 4 := by
  rw [JdifferenceP, eval_sub, primitiveDifference_eval, primitiveDifference_eval]
  ring

theorem logTrace_degree (p : ℕ) : (logTrace p : K[X]).natDegree ≤ p - 1 := by
  have hscale (c : K) : ((LP p : K[X]).comp (C c * X)).natDegree ≤ p - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [LP_scaled_coeff, if_neg (by omega)]
  unfold logTrace
  rw [← map_neg]
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_C_mul_le _ _).trans (hscale 4))
    ((natDegree_C_mul_le _ _).trans (hscale (1 / 4))))

theorem W_logTrace_tail (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) :
    strictTail p (W * logTrace p) = JdifferenceP p W := by
  have hp0 : 0 < p := by omega
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := div_ne_zero one_ne_zero h4
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  unfold logTrace
  rw [mul_add]
  have he (a : K) (P : K[X]) : W * (C a * P) = C a * (W * P) := by ring
  rw [neg_mul, mul_neg, strictTail_add p hp0]
  have hn : - (W * (C (1 / 4 : K) * (LP p).comp (C 4 * X))) =
      C (- (1 / 4 : K)) * (W * (LP p).comp (C 4 * X)) := by rw [map_neg]; ring
  rw [hn, he, strictTail_C_mul p hp0, strictTail_C_mul p hp0,
    strict_product_tail p W hW h0 4 h4, strict_product_tail p W hW h0 (1 / 4) ha,
    h4p, hap]
  unfold JdifferenceP
  have hunit : (- (1 / 4 : K)) * (-4) = 1 := by field_simp [h4]
  have hunit' : (4 : K) * (- (1 / 4)) = -1 := by field_simp [h4]
  rw [← mul_assoc, ← C_mul, hunit, C_1, one_mul,
    ← mul_assoc, ← C_mul, hunit', map_neg, C_1, neg_one_mul]
  simp only [one_div, inv_inv, sub_eq_add_neg]

set_option maxHeartbeats 800000 in
theorem actual_AB0_tail (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (W : K[X]) (hW : W.natDegree ≤ (p - 1) / 2 - 1) (h0 : W.coeff 0 = 0) (u : K) :
    strictTail p (A p W u * B0 p W u) = C (-4 / (15 * epsilon p)) * JdifferenceP p W := by
  have hp0 : 0 < p := by omega
  have hWp : W.natDegree < p := by omega
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by rw [show (15 : K) = 3 * 5 by ring]; exact mul_ne_zero h3 h5
  have heps : (epsilon p : K) ≠ 0 := pow_ne_zero _ h5
  have hA : (A p W u).natDegree ≤ W.natDegree := by
    unfold A
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hB : (Bpoly p W u).natDegree ≤ W.natDegree := by
    unfold Bpoly
    exact (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hAB : (A p W u * Bpoly p W u).natDegree ≤ p := by
    have hd := (natDegree_mul_le (p := A p W u) (q := Bpoly p W u)).trans (Nat.add_le_add hA hB)
    omega
  have hlog : (C (uSlot p u) * C (2 / 15 : K) * logTrace p).natDegree ≤ p := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_C_mul_le _ _).trans ((logTrace_degree p).trans (by omega)))
  have he : A p W u * B0 p W u = A p W u * Bpoly p W u +
      C (uSlot p u) * C (2 / 15 : K) * logTrace p -
        C (2 / epsilon p) * C (2 / 15 : K) * (W * logTrace p) := by
    unfold A B0
    ring
  rw [he, strictTail_sub p hp0, strictTail_add p hp0,
    strictTail_low p hp0 _ hAB, strictTail_low p hp0 _ hlog, add_zero, zero_sub]
  rw [mul_assoc (C (2 / epsilon p)), strictTail_C_mul p hp0,
    strictTail_C_mul p hp0, W_logTrace_tail p hp W hWp h0]
  have hc : -((2 / epsilon p : K) * (2 / 15)) = -4 / (15 * epsilon p) := by
    field_simp [heps, h15]
    ring
  rw [← mul_assoc, ← C_mul, ← neg_mul, ← map_neg, hc]

theorem actual_AB0_tail_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (W : K[X]) (hW : W.natDegree ≤ (p - 1) / 2 - 1) (h0 : W.coeff 0 = 0) (u z : K) :
    (strictTail p (A p W u * B0 p W u)).eval z =
      -4 / (15 * epsilon p) *
        (unitPrimitive p W z (1 / 4) - unitPrimitive p W z 4 -
          originPrimitive p W (1 / 4) + originPrimitive p W 4) := by
  rw [actual_AB0_tail p hp W hW h0 u, eval_mul, eval_C, JdifferenceP_eval]

end WPFiniteABSourceTail
