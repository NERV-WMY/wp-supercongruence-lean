import WPFieldAssembly.ActualSB72Finite
import WPFiniteProductTail
import WPFieldAssembly.ActualFullA2
import WPFiniteHomogeneousD
import WPFiniteLogProduct

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPFiniteKSource WPFiniteAffineLog WPFiniteProductTail
open LaurentPolynomial (T invert T_zero)

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- Every positive exponent after a phase shift is retained; only the strict diagonal is removed. -/
noncomputable def fullStrictPositive (p k : ℕ) (F : K[T;T⁻¹]) : K[X] :=
  LaurentPolynomial.trunc (T (-((k * p : ℕ) : ℤ)) * F) - C (F.coeff ((k * p : ℕ) : ℤ))

theorem fullStrictPositive_coeff (p k : ℕ) (F : K[T;T⁻¹]) (j : ℕ) :
    (fullStrictPositive p k F).coeff j =
      if j = 0 then 0 else F.coeff (((k * p + j : ℕ) : ℤ)) := by
  rw [fullStrictPositive, coeff_sub, WPFiniteJWeightedResidue.trunc_coeff, coeff_C]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-((k * p : ℕ) : ℤ)) (j : ℤ) F
  simp only [map_one, one_mul] at hs
  rw [hs, show (j : ℤ) - -((k * p : ℕ) : ℤ) = ((k * p + j : ℕ) : ℤ) by omega]
  by_cases hj : j = 0
  · subst j; simp
  · rw [if_neg hj, sub_zero, if_neg hj]

theorem fullStrictPositive_add (p k : ℕ) (F G : K[T;T⁻¹]) :
    fullStrictPositive p k (F + G) = fullStrictPositive p k F + fullStrictPositive p k G := by
  ext j
  simp only [fullStrictPositive_coeff, coeff_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]
  split_ifs <;> simp

theorem fullStrictPositive_sub (p k : ℕ) (F G : K[T;T⁻¹]) :
    fullStrictPositive p k (F - G) = fullStrictPositive p k F - fullStrictPositive p k G := by
  ext j
  simp only [fullStrictPositive_coeff, coeff_sub, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply]
  split_ifs <;> simp

theorem fullStrictPositive_C_mul (p k : ℕ) (a : K) (F : K[T;T⁻¹]) :
    fullStrictPositive p k (LaurentPolynomial.C a * F) = C a * fullStrictPositive p k F := by
  ext j
  rw [fullStrictPositive_coeff, coeff_C_mul, fullStrictPositive_coeff]
  have hc := WPFiniteJCarrier.shifted_coeff a 0 (((k * p + j : ℕ) : ℤ)) F
  simp only [T_zero, mul_one, sub_zero] at hc
  split_ifs <;> simp only [hc, mul_zero]

theorem fullStrictPositive_polynomial_coeff (p k : ℕ) (P : K[X]) (j : ℕ) :
    (fullStrictPositive p k P.toLaurent).coeff j =
      if j = 0 then 0 else P.coeff (k * p + j) := by
  rw [fullStrictPositive_coeff, WPFiniteJCarrier.toLaurent_coeff_nat]

theorem fullStrictPositive_small (p k : ℕ) (P : K[X]) (hP : P.natDegree ≤ k * p) :
    fullStrictPositive p k P.toLaurent = 0 := by
  ext j
  rw [fullStrictPositive_polynomial_coeff, coeff_zero]
  by_cases hj : j = 0
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem fullStrictPositive_one_eq_strictTail (p : ℕ) (hp : 0 < p) (P : K[X])
    (hP : P.natDegree < 2 * p) : fullStrictPositive p 1 P.toLaurent = strictTail p P := by
  ext j
  rw [fullStrictPositive_polynomial_coeff, strictTail_coeff p hp, one_mul]
  by_cases hj : j = 0
  · simp only [if_pos hj]
  · rw [if_neg hj, if_neg hj]
    by_cases hjp : j < p
    · rw [if_pos hjp]
    · rw [if_neg hjp]
      exact coeff_eq_zero_of_natDegree_lt (hP.trans_le (by omega))

/-- The original strict weighted functional on the whole Laurent support. -/
noncomputable def fullStrictTail (p k : ℕ) (F : K[T;T⁻¹]) : K :=
  2 * (fullStrictPositive p k F).eval 4 + (fullStrictPositive p k F).eval (1 / 4)

theorem fullStrictTail_infinityQ (p k : ℕ) (F : K[T;T⁻¹]) :
    fullStrictTail p k F = -WPFiniteJWeightedResidue.infinityQ (T (-((k * p : ℕ) : ℤ)) * F) := by
  have hc : (LaurentPolynomial.trunc (T (-((k * p : ℕ) : ℤ)) * F)).coeff 0 =
      F.coeff ((k * p : ℕ) : ℤ) := by
    rw [WPFiniteJWeightedResidue.trunc_coeff]
    have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-((k * p : ℕ) : ℤ)) 0 F
    simpa only [map_one, one_mul, zero_sub, neg_neg, Nat.cast_zero] using hs
  simp only [fullStrictTail, fullStrictPositive, eval_sub, eval_C,
    WPFiniteJWeightedResidue.infinityQ, hc]
  ring

private theorem LP_scaled_degree (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (C c * X)).natDegree ≤ p - 1 := by
  have hCX : (C c * X : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hdeg := Nat.mul_le_mul (LP_natDegree_le (K := K) p) hCX
  exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using hdeg)

theorem unitPrimitive_C_mul (p : ℕ) (a : K) (W : K[X]) (z y : K) :
    unitPrimitive p (C a * W) z y = a * unitPrimitive p W z y := by
  simp only [unitPrimitive, coeff_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem originPrimitive_C_mul (p : ℕ) (a : K) (W : K[X]) (y : K) :
    originPrimitive p (C a * W) y = a * originPrimitive p W y := by
  simp only [originPrimitive, coeff_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem unitPrimitive_remove_origin (p : ℕ) (W : K[X]) (z y : K) :
    unitPrimitive p (W - C (W.coeff 0)) z y = unitPrimitive p W z y := by
  unfold unitPrimitive
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_sub, coeff_C, if_neg (by have := (Finset.mem_Ico.mp hi).1; omega), sub_zero]

private theorem originPrimitive_remove_origin (p : ℕ) (W : K[X]) (y : K) :
    originPrimitive p (W - C (W.coeff 0)) y = originPrimitive p W y := by
  unfold originPrimitive
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_sub, coeff_C, if_neg (by have := (Finset.mem_Ico.mp hi).1; omega), sub_zero]

/-- The whole product tail includes a primitive with its actual origin removed exactly once. -/
theorem fullStrictPositive_log_product_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (c : K) (hc : c ≠ 0) (z : K) :
    (fullStrictPositive p 1 (W * (LP p).comp (C c * X)).toLaurent).eval z =
      -(c ^ p) * (unitPrimitive p W z c⁻¹ - originPrimitive p W c⁻¹) := by
  let W0 : K[X] := W - C (W.coeff 0)
  let L : K[X] := (LP p).comp (C c * X)
  have hW0 : W0.natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hW (by
      have hp := (Fact.out : p.Prime).pos
      simpa using hp))
  have hW00 : W0.coeff 0 = 0 := by simp [W0]
  have hL : L.natDegree ≤ p - 1 := LP_scaled_degree (K := K) p c
  have hsmall : fullStrictPositive p 1 (C (W.coeff 0) * L).toLaurent = 0 :=
    fullStrictPositive_small p 1 _ ((natDegree_C_mul_le _ _).trans (hL.trans (by omega)))
  have hdeg : (W0 * L).natDegree < 2 * p :=
    natDegree_mul_le.trans_lt (by omega)
  have he : W * L = W0 * L + C (W.coeff 0) * L := by dsimp [W0]; ring
  change (fullStrictPositive p 1 (W * L).toLaurent).eval z = _
  rw [he, map_add, fullStrictPositive_add, hsmall, add_zero,
    fullStrictPositive_one_eq_strictTail p (Fact.out : p.Prime).pos _ hdeg]
  rw [full_product_tail_value p W0 hW0 hW00 c hc z]
  simp only [W0, unitPrimitive_remove_origin, originPrimitive_remove_origin]

/-- The literal SB102 primitive e=-3Dstar, with the same full finite coefficients. -/
noncomputable def branchH (p : ℕ) (z y : K) : K :=
  unitPrimitive p (-C (3 : K) * Dstar p) z y

theorem branchH_is_Dstar_primitive (p : ℕ) (z y : K) :
    branchH p z y = -3 * unitPrimitive p (Dstar p) z y := by
  rw [branchH, ← C_neg, unitPrimitive_C_mul]

theorem branchH_origin (p : ℕ) (y : K) :
    branchH p 0 y = -3 * originPrimitive p (Dstar p) y := by
  rw [branchH_is_Dstar_primitive, unitPrimitive_origin]

noncomputable def finiteMixedLog (p : ℕ) : K[X] :=
  C (2 / 5 : K) * (-C (1 / 4 : K) * (LP p).comp (C (4 : K) * X) +
    C (4 : K) * (LP p).comp (C (1 / 4 : K) * X))

theorem finiteMixedLog_degree (p : ℕ) : (finiteMixedLog p : K[X]).natDegree ≤ p - 1 := by
  unfold finiteMixedLog
  have hb : (-C (1 / 4 : K) * (LP p).comp (C (4 : K) * X)).natDegree ≤ p - 1 := by
    rw [← C_neg]
    exact (natDegree_C_mul_le _ _).trans (LP_scaled_degree p 4)
  exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le
    hb
    ((natDegree_C_mul_le _ _).trans (LP_scaled_degree p (1 / 4)))))

/-- The strict mixed tail retains all four ordered primitives and both origin terms. -/
theorem finiteMixedLog_Dstar_strict_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (fullStrictPositive p 1 ((finiteMixedLog p) * Dstar p).toLaurent).eval z =
      -(2 / 15 : K) * (branchH p z (1 / 4) - branchH p z 4) +
        (2 / 15 : K) * (branchH p 0 (1 / 4) - branchH p 0 4) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hD : (Dstar p : K[X]).natDegree < p := (Dstar_degree p hp).trans_lt (by omega)
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [one_div, inv_pow, h4p]
  have he : ((finiteMixedLog p : K[X]) * Dstar p) = C (2 / 5 : K) *
      (-C (1 / 4 : K) * (Dstar p * (LP p).comp (C (4 : K) * X)) +
        C (4 : K) * (Dstar p * (LP p).comp (C (1 / 4 : K) * X))) := by
    unfold finiteMixedLog
    ring
  rw [he]
  simp only [map_mul, map_add, map_neg, Polynomial.toLaurent_C]
  rw [fullStrictPositive_C_mul, fullStrictPositive_add,
    ← map_neg LaurentPolynomial.C, fullStrictPositive_C_mul, fullStrictPositive_C_mul]
  simp only [eval_mul, eval_C, eval_add]
  rw [← map_mul (Polynomial.toLaurent), ← map_mul (Polynomial.toLaurent),
    fullStrictPositive_log_product_value p _ hD 4 h4 z,
    fullStrictPositive_log_product_value p _ hD (1 / 4) (one_div_ne_zero h4) z,
    h4p, hap]
  simp only [one_div, inv_inv, branchH_is_Dstar_primitive, unitPrimitive_origin]
  field_simp [h3, h4, h5, h15]
  ring

theorem finiteMixedLog_Dstar_strict_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    fullStrictTail p 1 ((finiteMixedLog p) * Dstar p).toLaurent =
      -(2 / 15 : K) * (2 * branchH p 4 (1 / 4) + branchH p (1 / 4) (1 / 4) -
        2 * branchH p 4 4 - branchH p (1 / 4) 4) +
      (2 / 5 : K) * (branchH p 0 (1 / 4) - branchH p 0 4) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  rw [fullStrictTail, finiteMixedLog_Dstar_strict_value p hp,
    finiteMixedLog_Dstar_strict_value p hp]
  field_simp [h3, h5, h15]
  ring

private theorem H_succ_unit (j : ℕ) (hj : 1 ≤ j) :
    (WPFiniteJSource.H j : K) = WPFiniteJSource.H (j - 1) + (j : K)⁻¹ := by
  unfold WPFiniteJSource.H
  rw [Nat.sub_add_cancel hj, Finset.sum_Ico_succ_top hj]

theorem fullD_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteLoop.D (p - 1) z z = WPFiniteField.R p z - WPFiniteField.R p (1 - z) := by
  have he : WPFiniteLoop.D (p - 1) z z =
      (ActualFullA2.fullHarmonicPrimitive p : K[X]).eval z + WPFiniteField.R p z := by
    unfold WPFiniteLoop.D ActualFullA2.fullHarmonicPrimitive WPFiniteField.R
    rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjpos := (Finset.mem_Ico.mp hj).1
    have hu := WPFiniteField.denominator_ne_zero (K := K) p j hj
    have hinner : (∑ k ∈ Finset.Ico 1 (j + 1),
        z ^ k * z ^ (j - k) / ((k : K) * (j : K))) =
        z ^ j / (j : K) * WPFiniteJSource.H j := by
      unfold WPFiniteJSource.H
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ j)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hinner, H_succ_unit j hjpos]
    field_simp [hu]
  rw [ActualFullA2.actual_full_dilog_value p hp] at he
  linear_combination he

private theorem H2_zero_left (p : ℕ) (y : K) : WPFiniteDReciprocity.H2 p 0 y = 0 := by
  unfold WPFiniteDReciprocity.H2
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos := (Finset.mem_Ico.mp hj).1
  rw [zero_pow (by omega : j ≠ 0), zero_mul, zero_div]

private theorem H2_diagonal_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) : WPFiniteDReciprocity.H2 p z z = 0 := by
  have hR1 : WPFiniteField.R p (1 : K) = 0 := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.R_castHom, map_one, map_zero] using h
  have he : WPFiniteDReciprocity.H2 p z z = z ^ p * WPFiniteField.R p (1 : K) := by
    unfold WPFiniteDReciprocity.H2 WPFiniteField.R
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    rw [← pow_add, Nat.add_sub_of_le hj'.2.le, one_pow, mul_one_div]
  rw [he, hR1, mul_zero]

private theorem H2_symmetric (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) :
    WPFiniteDReciprocity.H2 p x y = WPFiniteDReciprocity.H2 p y x := by
  unfold WPFiniteDReciprocity.H2
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => x ^ j * y ^ (p - j) / (j : K) ^ 2)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [show p - (p - j) = j by omega,
    WPFiniteField.reflected_denominator p j hj, neg_sq, mul_comm]

private theorem H2_joint_neg (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (x y : K) :
    WPFiniteDReciprocity.H2 p (-x) (-y) = -WPFiniteDReciprocity.H2 p x y := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  unfold WPFiniteDReciprocity.H2
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hpow : (-x) ^ j * (-y) ^ (p - j) = -(x ^ j * y ^ (p - j)) := by
    rw [neg_pow, neg_pow]
    calc
      _ = (-1 : K) ^ (j + (p - j)) * (x ^ j * y ^ (p - j)) := by rw [pow_add]; ring
      _ = _ := by rw [show j + (p - j) = p by omega, hodd.neg_pow, one_pow]; ring
  rw [hpow, neg_div]

theorem fullD_first_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteLoop.D (p - 1) 1 z = 2 * (WPFiniteField.R p z - WPFiniteField.R p (1 - z)) := by
  have hdiag := WPFiniteHomogeneousD.full_D_three_H2 (K := K) p hp z z
  rw [sub_self, H2_zero_left, H2_zero_left, zero_sub, add_zero] at hdiag
  have hone := WPFiniteHomogeneousD.full_D_three_H2 (K := K) p hp 1 z
  rw [H2_diagonal_zero p hp, zero_sub] at hone
  have hlast : WPFiniteDReciprocity.H2 p (z - 1) z =
      -WPFiniteDReciprocity.H2 p (-z) (1 - z) := by
    rw [H2_symmetric]
    have h := H2_joint_neg (K := K) p hp (-z) (1 - z)
    simpa only [neg_neg, neg_sub] using h
  rw [hlast] at hone
  have he : WPFiniteLoop.D (p - 1) 1 z = 2 * WPFiniteLoop.D (p - 1) z z := by
    linear_combination hone - 2 * hdiag
  rw [he, fullD_diagonal p hp]

theorem fullD_second_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteLoop.D (p - 1) z 1 = WPFiniteField.R p (1 - z) :=
  WPFiniteDSource.D_at_one p hp z

theorem fullD_one_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : WPFiniteLoop.D (p - 1) (1 : K) 1 = 0 := by
  rw [fullD_second_one p hp, sub_self]
  unfold WPFiniteField.R
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos := (Finset.mem_Ico.mp hj).1
  rw [zero_pow (by omega : j ≠ 0), zero_div]

/-- The complete ordered four-term consumer collapses with both diagonal rows retained. -/
theorem fullD_square_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteLoop.D (p - 1) z z + WPFiniteLoop.D (p - 1) (1 : K) 1 -
      WPFiniteLoop.D (p - 1) z 1 - WPFiniteLoop.D (p - 1) 1 z = -WPFiniteField.R p z := by
  rw [fullD_one_one p hp, fullD_diagonal p hp, fullD_second_one p hp, fullD_first_one p hp]
  ring

theorem fullStrictPositive_sum (p k : ℕ) {ι : Type*} (s : Finset ι)
    (F : ι → K[T;T⁻¹]) :
    fullStrictPositive p k (∑ i ∈ s, F i) = ∑ i ∈ s, fullStrictPositive p k (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext j; simp only [Finset.sum_empty, fullStrictPositive_coeff, coeff_zero]; simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, fullStrictPositive_add, ih, Finset.sum_insert hi]

theorem fullStrictPositive_monomial (p n : ℕ) (a : K) :
    fullStrictPositive p 1 (C a * X ^ n).toLaurent =
      if p < n then C a * X ^ (n - p) else 0 := by
  by_cases hn : p < n
  · rw [if_pos hn]
    ext j
    rw [fullStrictPositive_polynomial_coeff, one_mul, coeff_C_mul_X_pow,
      coeff_C_mul_X_pow]
    by_cases hj : j = 0
    · subst j
      rw [if_pos rfl, if_neg (by omega : ¬ 0 = n - p)]
    · rw [if_neg hj]
      by_cases he : n = p + j
      · rw [if_pos he.symm, if_pos (by omega : j = n - p)]
      · rw [if_neg (by omega : ¬ p + j = n), if_neg (by omega : ¬ j = n - p)]
  · rw [if_neg hn]
    exact fullStrictPositive_small p 1 _
      ((natDegree_C_mul_le _ _).trans (by simp only [natDegree_X_pow, one_mul]; omega))

private theorem scaledLog_expansion (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (C c * X)) =
      ∑ i ∈ Finset.Ico 1 p, C (c ^ i / (i : K)) * X ^ i := by
  unfold LP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, mul_pow,
    ← C_pow, ← mul_assoc, ← C_mul]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  simp only [div_eq_mul_inv]
  ring

/-- The reversed full high rectangle is used with its middle diagonal removed exactly. -/
theorem fullStrict_log_product (p : ℕ) [Fact p.Prime] [CharP K p]
    (c d z : K) (hc : c ≠ 0) (hd : d ≠ 0) (hz : z ≠ 0) :
    (fullStrictPositive p 1
      (((LP p).comp (C c * X)) * ((LP p).comp (C d * X))).toLaurent).eval z =
      c ^ p * d ^ p * z ^ p * WPFiniteDReciprocity.T2 p (c⁻¹ * z⁻¹) (d⁻¹ * z⁻¹) := by
  classical
  have hpoly : ((LP p : K[X]).comp (C c * X)) * ((LP p).comp (C d * X)) =
      ∑ ij ∈ WPFiniteLogProduct.rect p,
        C (c ^ ij.1 * d ^ ij.2 / ((ij.1 : K) * (ij.2 : K))) * X ^ (ij.1 + ij.2) := by
    rw [scaledLog_expansion, scaledLog_expansion, Finset.sum_mul]
    unfold WPFiniteLogProduct.rect
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_mul_mul_comm, ← C_mul, ← pow_add]
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have he : (fullStrictPositive p 1
      (((LP p).comp (C c * X)) * ((LP p).comp (C d * X))).toLaurent).eval z =
      ∑ ij ∈ WPFiniteLogProduct.highRect p,
        c ^ ij.1 * d ^ ij.2 * z ^ (ij.1 + ij.2 - p) /
          ((ij.1 : K) * (ij.2 : K)) := by
    rw [hpoly, map_sum, fullStrictPositive_sum, eval_finsetSum]
    simp only [WPFiniteLogProduct.highRect, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ij _
    rw [fullStrictPositive_monomial]
    by_cases hij : p < ij.1 + ij.2
    · rw [if_pos hij, if_pos hij, eval_mul, eval_C, eval_pow, eval_X]
      simp only [div_eq_mul_inv]
      ring
    · rw [if_neg hij, if_neg hij, eval_zero]
  rw [he, ← WPFiniteLogProduct.high_reindex p
    (fun ij => c ^ ij.1 * d ^ ij.2 * z ^ (ij.1 + ij.2 - p) /
      ((ij.1 : K) * (ij.2 : K))), WPFiniteDReciprocity.T2_low_rows]
  simp only [WPFiniteLogProduct.lowTriangle, Finset.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hj' := Finset.mem_Ico.mp hj
  have hk' := Finset.mem_Ico.mp hk
  have hku : k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hju : j - k ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  rw [show p - k + (p - (j - k)) - p = p - j by omega,
    WPFiniteField.reflected_denominator p k hku,
    WPFiniteField.reflected_denominator p (j - k) hju, neg_mul_neg,
    pow_sub₀ c hc (by omega), pow_sub₀ d hd (by omega), pow_sub₀ z hz (by omega)]
  have hzinv : (z ^ k)⁻¹ * (z ^ (j - k))⁻¹ = (z ^ j)⁻¹ := by
    rw [← mul_inv_rev, ← pow_add, Nat.sub_add_cancel (by omega : k ≤ j)]
  simp only [mul_pow, inv_pow, div_eq_mul_inv, mul_inv_rev]
  linear_combination -(c ^ p * d ^ p * z ^ p * (c ^ k)⁻¹ * (d ^ (j - k))⁻¹ *
    (k : K)⁻¹ * ((j - k : ℕ) : K)⁻¹) * hzinv

theorem fullT2_square_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteDReciprocity.T2 p z z + WPFiniteDReciprocity.T2 p (1 : K) 1 -
      2 * WPFiniteDReciprocity.T2 p z 1 = -2 * WPFiniteField.R p z := by
  have h := fullD_square_consumer (K := K) p hp z
  unfold WPFiniteDReciprocity.T2
  linear_combination 2 * h

private theorem T2_comm (p : ℕ) [Fact p.Prime] [CharP K p] (x y : K) :
    WPFiniteDReciprocity.T2 p x y = WPFiniteDReciprocity.T2 p y x := by
  unfold WPFiniteDReciprocity.T2
  ring

theorem finiteMixedLog_square_strict_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) (hz : z ≠ 0) :
    (fullStrictPositive p 1 ((finiteMixedLog p : K[X]) ^ 2).toLaurent).eval z =
      (4 / 25 : K) * z ^ p *
        (WPFiniteDReciprocity.T2 p ((1 / 4) * z⁻¹) ((1 / 4) * z⁻¹) +
          WPFiniteDReciprocity.T2 p (4 * z⁻¹) (4 * z⁻¹) -
            2 * WPFiniteDReciprocity.T2 p ((1 / 4) * z⁻¹) (4 * z⁻¹)) := by
  let Lb : K[X] := (LP p).comp (C (4 : K) * X)
  let La : K[X] := (LP p).comp (C (1 / 4 : K) * X)
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [one_div, inv_pow, h4p]
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero _ h5
  have he : (finiteMixedLog p : K[X]) ^ 2 = C ((2 / 5 : K) ^ 2) *
      ((C ((1 / 4 : K) ^ 2) * (Lb * Lb) + C ((4 : K) ^ 2) * (La * La)) -
        C (2 * (1 / 4 : K) * 4) * (Lb * La)) := by
    dsimp only [La, Lb]
    simp only [finiteMixedLog, C_mul, C_pow, C_ofNat]
    ring
  rw [he]
  simp only [map_mul Polynomial.toLaurent, map_add Polynomial.toLaurent,
    map_sub Polynomial.toLaurent, Polynomial.toLaurent_C]
  rw [fullStrictPositive_C_mul, fullStrictPositive_sub, fullStrictPositive_add,
    fullStrictPositive_C_mul, fullStrictPositive_C_mul, fullStrictPositive_C_mul]
  simp only [eval_mul, eval_C, eval_sub, eval_add]
  rw [← map_mul (Polynomial.toLaurent), ← map_mul (Polynomial.toLaurent),
    ← map_mul (Polynomial.toLaurent)]
  dsimp only [La, Lb]
  rw [fullStrict_log_product p 4 4 z h4 h4 hz,
    fullStrict_log_product p (1 / 4) (1 / 4) z (one_div_ne_zero h4) (one_div_ne_zero h4) hz,
    fullStrict_log_product p 4 (1 / 4) z h4 (one_div_ne_zero h4) hz, h4p, hap]
  simp only [one_div, inv_inv]
  field_simp [h4, h5, h25]
  ring

/-- Positive weight-two inversion is the original sign, including both endpoint values. -/
theorem finiteMixedLog_square_strict_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (fullStrictPositive p 1 ((finiteMixedLog p : K[X]) ^ 2).toLaurent).eval 4 =
      -(32 / 25 : K) * WPFiniteField.R p (1 / 16) ∧
    (fullStrictPositive p 1 ((finiteMixedLog p : K[X]) ^ 2).toLaurent).eval (1 / 4) =
      -(2 / 25 : K) * WPFiniteField.R p 16 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [one_div, inv_pow, h4p]
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 ^ 2 by ring]
    exact pow_ne_zero _ h4
  have hsmall : (1 / 4 : K) * (4 : K)⁻¹ = 1 / 16 := by field_simp [h4, h16]; ring
  have hone : (4 : K) * (4 : K)⁻¹ = 1 := mul_inv_cancel₀ h4
  have hinvone : (1 / 4 : K) * (1 / 4 : K)⁻¹ = 1 :=
    mul_inv_cancel₀ (one_div_ne_zero h4)
  have hlarge : (4 : K) * (1 / 4 : K)⁻¹ = 16 := by rw [one_div, inv_inv]; ring
  constructor
  · rw [finiteMixedLog_square_strict_value p hp 4 h4, h4p, hsmall, hone,
      fullT2_square_consumer p hp]
    field_simp [h5]
    ring
  · rw [finiteMixedLog_square_strict_value p hp (1 / 4) (one_div_ne_zero h4), hap,
      hinvone, hlarge, T2_comm p 1 16]
    have h := fullT2_square_consumer (K := K) p hp (16 : K)
    have he : WPFiniteDReciprocity.T2 p (1 : K) 1 + WPFiniteDReciprocity.T2 p 16 16 -
        2 * WPFiniteDReciprocity.T2 p 16 1 = -2 * WPFiniteField.R p 16 := by
      linear_combination h
    rw [he]
    field_simp [h4, h5]

theorem finiteMixedLog_square_strict_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : fullStrictTail p 1 ((finiteMixedLog p : K[X]) ^ 2).toLaurent =
      -(6 / 25 : K) * WPFiniteField.R p 16 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : K) ≠ 0 := by rw [show (16 : K) = 4 ^ 2 by ring]; exact pow_ne_zero _ h4
  have h16p : (16 : K) ^ p = 16 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 16
  have hR := WPFiniteField.R_inversion p (16 : K) h16
  rw [h16p, ← one_div] at hR
  obtain ⟨hb, ha⟩ := finiteMixedLog_square_strict_endpoints (K := K) p hp
  rw [fullStrictTail, hb, ha, hR]
  field_simp [h16, h5]
  ring

end WPFieldAssembly.ActualBpairContraction
