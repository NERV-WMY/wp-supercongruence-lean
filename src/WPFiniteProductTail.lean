import WPFiniteJWeightedResidue
import Mathlib.Algebra.Ring.GeomSum

open scoped BigOperators
open Polynomial

namespace WPFiniteProductTail

open WPFiniteAffineLog WPFiniteJHighCoefficient

variable {K : Type*} [Field K]

/-- Full strict positive band above p, shifted down by p. -/
noncomputable def strictTail (p : ℕ) (P : K[X]) : K[X] :=
  highBand p P - C (P.coeff p)

theorem strictTail_coeff (p : ℕ) (hp : 0 < p) (P : K[X]) (j : ℕ) :
    (strictTail p P).coeff j = if j = 0 then 0 else if j < p then P.coeff (p + j) else 0 := by
  rw [strictTail, coeff_sub, highBand_coeff, coeff_C]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.add_zero, if_pos hp, if_true, sub_self]
  · simp only [if_neg hj, sub_zero]

theorem LP_scaled_coeff (p : ℕ) (c : K) (j : ℕ) :
    ((LP p : K[X]).comp (C c * X)).coeff j =
      if 1 ≤ j ∧ j < p then c ^ j / (j : K) else 0 := by
  have hexp : (LP p : K[X]).comp (C c * X) =
      ∑ b ∈ Finset.Ico 1 p, C (c ^ b / (b : K)) * X ^ b := by
    unfold LP
    simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow,
      ← mul_assoc, ← C_mul]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    simp only [div_eq_mul_inv]
    ring
  rw [hexp]
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_Ico]

theorem reversed_unit (p : ℕ) [Fact p.Prime] [CharP K p] (k : ℕ)
    (hk : k ∈ Finset.Ico 1 p) :
    (((p - k : ℕ) : K)⁻¹) = -(k : K)⁻¹ := by
  have he : ((p - k : ℕ) : K) = -(k : K) := by
    rw [Nat.cast_sub (by have ht := (Finset.mem_Ico.mp hk).2; omega), CharP.cast_eq_zero]
    ring
  rw [he, inv_neg]

/-- Entire divided geometric primitive from the literal coefficients of W. -/
noncomputable def unitPrimitive (p : ℕ) (W : K[X]) (z y : K) : K :=
  ∑ i ∈ Finset.Ico 1 p, W.coeff i *
    ∑ k ∈ Finset.Ico 1 (i + 1), y ^ k * z ^ (i - k) / (k : K)

noncomputable def originPrimitive (p : ℕ) (W : K[X]) (y : K) : K :=
  ∑ i ∈ Finset.Ico 1 p, W.coeff i * y ^ i / (i : K)

/-- Coefficients of H_z(y)-H_x(y), with its entire k=i boundary separated. -/
noncomputable def primitiveDifferenceP (p : ℕ) (W : K[X]) (y : K) : K[X] :=
  ∑ i ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 i,
    C (W.coeff i * y ^ k / (k : K)) * X ^ (i - k)

noncomputable def monomialDifference (i : ℕ) (y : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 i, C (y ^ (i - j) / ((i - j : ℕ) : K)) * X ^ j

theorem monomialDifference_coeff (i : ℕ) (y : K) (j : ℕ) :
    (monomialDifference i y).coeff j =
      if 1 ≤ j ∧ j < i then y ^ (i - j) / ((i - j : ℕ) : K) else 0 := by
  simp [monomialDifference]

theorem strict_product_monomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (i : ℕ) (hi : i ∈ Finset.Ico 1 p) (a c : K) (hc : c ≠ 0) :
    strictTail p (C a * X ^ i * (LP p).comp (C c * X)) =
      C (-a * c ^ p) * monomialDifference i c⁻¹ := by
  have hip := (Finset.mem_Ico.mp hi).2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  ext j
  rw [strictTail_coeff p hp, coeff_C_mul, monomialDifference_coeff]
  by_cases hj0 : j = 0
  · subst j
    rw [if_pos rfl, if_neg (by omega : ¬(1 ≤ 0 ∧ 0 < i)), mul_zero]
  · rw [if_neg hj0]
    by_cases hji : j < i
    · rw [if_pos (by omega), if_pos ⟨by omega, hji⟩]
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), LP_scaled_coeff,
        if_pos (by omega)]
      have hk : i - j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
      have he : p + j - i = p - (i - j) := by omega
      rw [he, div_eq_mul_inv, reversed_unit p (i - j) hk]
      have hpow : c ^ (p - (i - j)) = c ^ p * (c⁻¹) ^ (i - j) := by
        rw [pow_sub₀ c hc (by omega), ← inv_pow]
      rw [hpow]
      ring
    · rw [if_neg (by omega : ¬(1 ≤ j ∧ j < i))]
      by_cases hjp : j < p
      · rw [if_pos hjp, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
          LP_scaled_coeff, if_neg (by omega), mul_zero]
        ring
      · rw [if_neg hjp]
        ring

theorem strictTail_sum (p : ℕ) (hp : 0 < p) {ι : Type*} (s : Finset ι) (f : ι → K[X]) :
    strictTail p (∑ i ∈ s, f i) = ∑ i ∈ s, strictTail p (f i) := by
  ext j
  simp only [strictTail_coeff p hp, finsetSum_coeff]
  by_cases hj0 : j = 0
  · simp only [if_pos hj0, Finset.sum_const_zero]
  · rw [if_neg hj0]
    by_cases hjp : j < p
    · simp only [if_pos hjp, if_neg hj0]
    · simp only [if_neg hjp, if_neg hj0, Finset.sum_const_zero]

theorem W_full_cutoff (p : ℕ) (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) :
    W = ∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * X ^ i := by
  ext j
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hj : j ∈ Finset.Ico 1 p
  · rw [if_pos hj]
  · rw [if_neg hj]
    by_cases hj0 : j = 0
    · simpa only [hj0] using h0
    · exact coeff_eq_zero_of_natDegree_lt (hW.trans_le (by
        have hm : ¬(1 ≤ j ∧ j < p) := by simpa only [Finset.mem_Ico] using hj
        omega))

theorem monomialDifference_reindex (i : ℕ) (y : K) :
    monomialDifference i y =
      ∑ k ∈ Finset.Ico 1 i, C (y ^ k / (k : K)) * X ^ (i - k) := by
  unfold monomialDifference
  apply Finset.sum_bij (fun j _ => i - j)
  · intro j hj
    have hm := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr (by omega)
  · intro j hj k hk he
    have hm := Finset.mem_Ico.mp hj
    have hn := Finset.mem_Ico.mp hk
    omega
  · intro k hk
    have hm := Finset.mem_Ico.mp hk
    refine ⟨i - k, Finset.mem_Ico.mpr (by omega), by omega⟩
  · intro j hj
    have hm := Finset.mem_Ico.mp hj
    rw [show i - (i - j) = j by omega]

theorem primitiveDifference_expansion (p : ℕ) (W : K[X]) (y : K) :
    primitiveDifferenceP p W y =
      ∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * monomialDifference i y := by
  unfold primitiveDifferenceP
  apply Finset.sum_congr rfl
  intro i _
  rw [monomialDifference_reindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, ← C_mul]
  congr 1
  simp only [div_eq_mul_inv]
  ring

theorem strict_product_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) (c : K) (hc : c ≠ 0) :
    strictTail p (W * (LP p).comp (C c * X)) =
      C (-(c ^ p)) * primitiveDifferenceP p W c⁻¹ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  conv_lhs => rw [W_full_cutoff p W hW h0]
  rw [Finset.sum_mul, strictTail_sum p hp, primitiveDifference_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [strict_product_monomial p i hi _ c hc, ← mul_assoc, ← C_mul]
  congr 1
  ring

theorem primitiveDifference_eval (p : ℕ) (W : K[X]) (z y : K) :
    (primitiveDifferenceP p W y).eval z =
      unitPrimitive p W z y - originPrimitive p W y := by
  unfold primitiveDifferenceP unitPrimitive originPrimitive
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := Finset.mem_Ico.mp hi
  rw [Finset.sum_Ico_succ_top hm.1]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [mul_add]
  have he : ∑ k ∈ Finset.Ico 1 i, W.coeff i * y ^ k / (k : K) * z ^ (i - k) =
      W.coeff i * ∑ k ∈ Finset.Ico 1 i, y ^ k * z ^ (i - k) / (k : K) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  simp only [div_eq_mul_inv]
  ring

theorem full_product_tail_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) (c : K) (hc : c ≠ 0) (z : K) :
    (strictTail p (W * (LP p).comp (C c * X))).eval z =
      -(c ^ p) * (unitPrimitive p W z c⁻¹ - originPrimitive p W c⁻¹) := by
  rw [strict_product_tail p W hW h0 c hc, eval_mul, eval_C, primitiveDifference_eval]

noncomputable def integratedGeometric (i : ℕ) (z : K) : K[X] :=
  ∑ k ∈ Finset.Ico 1 (i + 1), C (z ^ (i - k) / (k : K)) * X ^ k

noncomputable def unitPrimitiveP (p : ℕ) (W : K[X]) (z : K) : K[X] :=
  ∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * integratedGeometric i z

theorem unitPrimitiveP_eval (p : ℕ) (W : K[X]) (z y : K) :
    (unitPrimitiveP p W z).eval y = unitPrimitive p W z y := by
  simp only [unitPrimitiveP, integratedGeometric, unitPrimitive, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem integratedGeometric_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (i : ℕ) (hi : i < p) (z : K) :
    (integratedGeometric i z).derivative =
      ∑ j ∈ Finset.range i, C (z ^ (i - 1 - j)) * X ^ j := by
  unfold integratedGeometric
  rw [derivative_sum]
  have he : (∑ k ∈ Finset.Ico 1 (i + 1), (C (z ^ (i - k) / (k : K)) * X ^ k).derivative) =
      ∑ k ∈ Finset.Ico 1 (i + 1), C (z ^ (i - k)) * X ^ (k - 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k ∈ Finset.Ico 1 p := by
      have hm := Finset.mem_Ico.mp hk
      exact Finset.mem_Ico.mpr (by omega)
    rw [derivative_C_mul_X_pow, div_mul_cancel₀ _ (WPFiniteField.denominator_ne_zero p k hkp)]
  rw [he, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_range.mp hj
  rw [show i - (1 + j) = i - 1 - j by omega, show 1 + j - 1 = j by omega]

theorem integratedGeometric_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (i : ℕ) (hi : i < p) (z : K) :
    (X - C z) * (integratedGeometric i z).derivative = X ^ i - C (z ^ i) := by
  rw [integratedGeometric_derivative p i hi z]
  have he : (∑ j ∈ Finset.range i, C (z ^ (i - 1 - j)) * X ^ j : K[X]) =
      ∑ j ∈ Finset.range i, X ^ j * C z ^ (i - 1 - j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← C_pow, mul_comm]
  rw [he, mul_comm (X - C z), geom_sum₂_mul, ← C_pow]

theorem unitPrimitiveP_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) (z : K) :
    (X - C z) * (unitPrimitiveP p W z).derivative = W - C (W.eval z) := by
  unfold unitPrimitiveP
  rw [derivative_sum, Finset.mul_sum]
  have he : (∑ i ∈ Finset.Ico 1 p, (X - C z) *
      (C (W.coeff i) * integratedGeometric i z).derivative) =
      ∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * (X ^ i - C (z ^ i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [derivative_C_mul]
    rw [mul_left_comm, integratedGeometric_source p i (Finset.mem_Ico.mp hi).2 z]
  rw [he]
  have hcut := W_full_cutoff p W hW h0
  have hval := congrArg (fun F : K[X] => C (F.eval z)) hcut
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_mul] at hval
  have hright : W - C (W.eval z) =
      (∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * X ^ i) -
        (∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * C (z ^ i)) :=
    congrArg₂ (fun A B : K[X] => A - B) hcut hval
  rw [hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem unitPrimitiveP_zero (p : ℕ) (W : K[X]) (z : K) :
    (unitPrimitiveP p W z).eval 0 = 0 := by
  rw [unitPrimitiveP_eval]
  unfold unitPrimitive
  apply Finset.sum_eq_zero
  intro i _
  have he : ∑ k ∈ Finset.Ico 1 (i + 1), (0 : K) ^ k * z ^ (i - k) / (k : K) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hm := Finset.mem_Ico.mp hk
    rw [zero_pow (by omega : k ≠ 0), zero_mul, zero_div]
  rw [he, mul_zero]

theorem unitPrimitive_origin (p : ℕ) (W : K[X]) (y : K) :
    unitPrimitive p W 0 y = originPrimitive p W y := by
  unfold unitPrimitive originPrimitive
  apply Finset.sum_congr rfl
  intro i hi
  have hm := Finset.mem_Ico.mp hi
  have he : ∑ k ∈ Finset.Ico 1 (i + 1), y ^ k * (0 : K) ^ (i - k) / (k : K) =
      y ^ i / (i : K) := by
    rw [Finset.sum_eq_single i]
    · rw [Nat.sub_self, pow_zero, mul_one]
    · intro k hk hki
      have hn := Finset.mem_Ico.mp hk
      rw [zero_pow (by omega : i - k ≠ 0), mul_zero, zero_div]
    · intro hni
      exact False.elim (hni (Finset.mem_Ico.mpr (by omega)))
  rw [he]
  simp only [div_eq_mul_inv]
  ring

theorem originPrimitiveP_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) :
    X * (unitPrimitiveP p W 0).derivative = W := by
  have he := unitPrimitiveP_source p W hW h0 (0 : K)
  simpa only [map_zero, sub_zero, ← coeff_zero_eq_eval_zero, h0] using he

theorem unitPrimitiveP_degree (p : ℕ) (W : K[X]) (z : K) :
    (unitPrimitiveP p W z).natDegree ≤ p - 1 := by
  unfold unitPrimitiveP
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hm := Finset.mem_Ico.mp hi
  apply (natDegree_C_mul_le _ _).trans
  unfold integratedGeometric
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hn := Finset.mem_Ico.mp hk
  apply (natDegree_C_mul_le _ _).trans
  simpa only [natDegree_X_pow] using (show k ≤ p - 1 by omega)

end WPFiniteProductTail
