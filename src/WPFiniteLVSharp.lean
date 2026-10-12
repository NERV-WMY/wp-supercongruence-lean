import WPFiniteLVSupport

open Polynomial

namespace WPFiniteLVSharp

open WPFiniteAffineLog WPFiniteABSourceTail WPFiniteWSource WPFinitePSource
  WPFiniteLVSource WPFiniteLVSupport

variable {K : Type*} [Field K]

noncomputable def positiveDifference (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[X] :=
  regularRemainder p u - 3 * B0 p (W p) u

theorem original_phase_degrees (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (B0 p (W p) u : K[X]).natDegree ≤ p - 1 ∧ (Cminus p u : K[X]).natDegree ≤ p - 1 := by
  have hW : (W p : K[X]).natDegree ≤ p - 1 := (W_degree p hp).trans (by omega)
  have hscale (c : K) : ((LP p : K[X]).comp (C c * X)).natDegree ≤ p - 1 := by
    have hX : (C c * X : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    exact natDegree_comp_le.trans (by simpa using Nat.mul_le_mul (LP_natDegree_le p) hX)
  have hd : (logDifference p : K[X]).natDegree ≤ p - 1 := by
    unfold logDifference
    exact (natDegree_sub_le _ _).trans (max_le (hscale 4) (hscale (1 / 4)))
  constructor
  · unfold B0 Bpoly
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans hW)))
      ((natDegree_C_mul_le _ _).trans (logTrace_degree p)))
  · unfold Cminus
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans hW)))
      ((natDegree_C_mul_le _ _).trans hd))

theorem positiveDifference_prebound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (positiveDifference p u : K[X]).natDegree ≤ p - 1 := by
  unfold positiveDifference
  apply (natDegree_sub_le _ _).trans
  apply max_le (regularRemainder_prebound p hp u hu)
  change (C (3 : K) * B0 p (W p) u).natDegree ≤ p - 1
  exact (natDegree_C_mul_le _ _).trans (original_phase_degrees p hp u).1

theorem sourceRemainder_phases (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    (sourceRemainder p u : K[X]) = X ^ p * positiveDifference p u - 3 * Cminus p u := by
  have hxp2 : (X : K[X]) ^ (2 * p) = X ^ p * X ^ p := by
    rw [← pow_add]
    congr 1
    omega
  unfold sourceRemainder positiveDifference regularRemainder Pnumerator
  rw [hxp2]
  ring

theorem sourceRemainder_prebound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (sourceRemainder p u : K[X]).natDegree ≤ 2 * p - 1 := by
  rw [sourceRemainder_phases]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans ((Nat.add_le_add
      (by simp : (X ^ p : K[X]).natDegree ≤ p) (positiveDifference_prebound p hp u hu)).trans (by omega))
  · change (C (3 : K) * Cminus p u).natDegree ≤ 2 * p - 1
    exact (natDegree_C_mul_le _ _).trans ((original_phase_degrees p hp u).2.trans (by omega))

theorem sourceRemainder_derivative_bound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ((sourceRemainder p u : K[X]).derivative).natDegree ≤ p + (p - 1) / 2 - 2 := by
  have hS : (squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hSN : (squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤ (p - 1) / 2 :=
    by simpa using natDegree_pow_le_of_le ((p - 1) / 2) hS
  have hB : (4 * X - 11 : K[X]).natDegree ≤ 1 := by
    have h4X : (4 * X : K[X]).natDegree ≤ 1 := by
      change (C (4 : K) * X).natDegree ≤ 1
      exact (natDegree_C_mul_le _ _).trans (by simp)
    exact (natDegree_sub_le _ _).trans (max_le h4X (by simp))
  have hpB : (X ^ p * (4 * X - 11) : K[X]).natDegree ≤ p + 1 :=
    natDegree_mul_le.trans (Nat.add_le_add (by simp) hB)
  have hpSN : (X ^ p * squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤ p + (p - 1) / 2 :=
    natDegree_mul_le.trans (Nat.add_le_add (by simp) hSN)
  have h6 : (6 * X ^ p * squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤ p + (p - 1) / 2 := by
    rw [mul_assoc]
    change (C (6 : K) * (X ^ p * squaredCoordinate ^ ((p - 1) / 2))).natDegree ≤ _
    exact (natDegree_C_mul_le _ _).trans hpSN
  have h4 : (4 * squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤ (p - 1) / 2 := by
    change (C (4 : K) * squaredCoordinate ^ ((p - 1) / 2)).natDegree ≤ _
    exact (natDegree_C_mul_le _ _).trans hSN
  have hrow : (X ^ p * (4 * X - 11) - 6 * X ^ p * squaredCoordinate ^ ((p - 1) / 2) +
      4 * squaredCoordinate ^ ((p - 1) / 2) : K[X]).natDegree ≤ p + (p - 1) / 2 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le (hpB.trans (by omega)) h6)) (h4.trans (by omega)))
  have h4u : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hA : ((4 - X) * (4 * X - 1) : K[X]).natDegree = 2 := by
    compute_degree
    simpa using (neg_ne_zero.mpr h4u)
    all_goals norm_num
  have hAn : ((4 - X) * (4 * X - 1) : K[X]) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hA
    omega
  have hlast : ((4 - X) * (4 * X - 1) * X ^ (p - 1) : K[X]).natDegree ≤ p + 1 :=
    natDegree_mul_le.trans (by rw [hA]; simp only [natDegree_X_pow]; omega)
  have hbound : ((4 - X) * (4 * X - 1) * (sourceRemainder p u).derivative : K[X]).natDegree ≤ p + (p - 1) / 2 := by
    rw [sourceRemainder_cleared_source p hp u]
    have hlast' : (C (3 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1)).natDegree ≤ p + (p - 1) / 2 := by
      have he : C (3 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) =
          C (3 / 2 : K) * ((4 - X) * (4 * X - 1) * X ^ (p - 1)) := by ring
      rw [he]
      exact (natDegree_C_mul_le _ _).trans (hlast.trans (by omega))
    exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hrow) hlast')
  by_cases hd : (sourceRemainder p u : K[X]).derivative = 0
  · simp only [hd, natDegree_zero]
    omega
  · rw [natDegree_mul hAn hd, hA] at hbound
    omega

theorem sourceRemainder_sharp_bound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (sourceRemainder p u : K[X]).natDegree ≤ p + (p - 1) / 2 - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hQ := sourceRemainder_prebound (K := K) p hp u hu
  by_cases hhigh : 2 * p ≤ j
  · exact coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (by omega))
  have hsmall : j - p ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hcast : (j : K) = ((j - p : ℕ) : K) := by
    calc
      _ = (((j - p) + p : ℕ) : K) := congrArg (fun m : ℕ => (m : K)) (by omega)
      _ = _ := by rw [Nat.cast_add, CharP.cast_eq_zero K p, add_zero]
  have hju : (j : K) ≠ 0 := by
    rw [hcast]
    exact WPFiniteField.denominator_ne_zero p (j - p) hsmall
  have he : ((sourceRemainder p u : K[X]).derivative).coeff (j - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((sourceRemainder_derivative_bound p hp u).trans_lt (by omega))
  rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (by omega : 1 ≤ j)] at he
  exact (mul_eq_zero.mp he).resolve_right hju

/-- Every positive coefficient at N or above vanishes, with the full negative phase retained. -/
theorem positiveDifference_sharp_bound (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (positiveDifference p u : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hC : (Cminus p u : K[X]).coeff (p + j) = 0 :=
    coeff_eq_zero_of_natDegree_lt ((original_phase_degrees p hp u).2.trans_lt (by omega))
  have he : (sourceRemainder p u : K[X]).coeff (p + j) = (positiveDifference p u).coeff j := by
    rw [sourceRemainder_phases, coeff_sub, coeff_ofNat_mul, coeff_X_pow_mul',
      if_pos (by omega), Nat.add_sub_cancel_left, hC, mul_zero, sub_zero]
  rw [← he]
  exact coeff_eq_zero_of_natDegree_lt ((sourceRemainder_sharp_bound p hp u hu).trans_lt (by omega))

end WPFiniteLVSharp
