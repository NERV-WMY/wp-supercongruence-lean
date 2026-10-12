import WPFieldAssembly.ActualBpairHAttachment
import WPFieldAssembly.ActualBpairMetric

open scoped Polynomial LaurentPolynomial
open Polynomial
open LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorMixedPrimitive

open ActualBpairContraction WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The same even source used in each original ordered H primitive. -/
noncomputable def originalEven (p : ℕ) : K[X] := -Polynomial.C (3 : K) * Dstar p

noncomputable def calLPositive (p : ℕ) : K[X] :=
  -Polynomial.C (2 / 15 : K) * (2 * branchHPolynomial p (1 / 4) + branchHPolynomial p 4) -
    Polynomial.C (4 * WPFiniteNC122.h p / 15) *
      (originalEven p - Polynomial.C ((originalEven p).eval 0))

noncomputable def calLNegative (p : ℕ) : K[T;T⁻¹] :=
  -LaurentPolynomial.C (2 / 15 : K) *
    (2 * invert (branchHPolynomial p 4).toLaurent +
      invert (branchHPolynomial p (1 / 4)).toLaurent -
        3 * invert (branchHPolynomial p 0).toLaurent)

noncomputable def calLUnnormalized (p : ℕ) : K[T;T⁻¹] :=
  (calLPositive p).toLaurent + calLNegative p

/-- The sole small-band invisible coefficient is fixed at the original branch point. -/
noncomputable def calL (p : ℕ) : K[T;T⁻¹] :=
  calLUnnormalized p - LaurentPolynomial.C
    (GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero) (calLUnnormalized p))

noncomputable def kappa (p : ℕ) : K :=
  -2 * (originalEven p).eval 4 - (originalEven p).eval (1 / 4) +
    3 * (originalEven p).eval 0

/-- Abar times the entire original simple-pole form, including its origin pole. -/
noncomputable def clearedLambda (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (-2 * kappa p / 15) * WPFiniteZSource.Abar.toLaurent * T (-1) +
    LaurentPolynomial.C (16 * WPFiniteNC122.h p / 15) * (T 1 - 4) -
      LaurentPolynomial.C (4 * WPFiniteNC122.h p / 15) * (T 1 - LaurentPolynomial.C (1 / 4 : K))

private theorem integratedGeometric_degree (i : ℕ) (z : K) :
    (WPFiniteProductTail.integratedGeometric i z).natDegree ≤ i := by
  unfold WPFiniteProductTail.integratedGeometric
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_le _ _).trans ((by simp : (X ^ k : K[X]).natDegree ≤ k).trans
    (by have := (Finset.mem_Ico.mp hk).2; omega))

private theorem integratedGeometric_last (i : ℕ) (hi : 0 < i) (z : K) :
    (WPFiniteProductTail.integratedGeometric i z).coeff i = (i : K)⁻¹ := by
  classical
  simp [WPFiniteProductTail.integratedGeometric, Nat.ne_of_gt hi]

theorem originalEven_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (originalEven p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  unfold originalEven
  rw [← Polynomial.C_neg]
  exact (natDegree_C_mul_le _ _).trans (Dstar_degree p hp)

theorem branchH_sharp_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (z : K) :
    (branchHPolynomial p z : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  let M := (p - 1) / 2 - 1
  let E := originalEven (K := K) p
  have hE : E.natDegree ≤ M := originalEven_degree p hp
  change (WPFiniteProductTail.unitPrimitiveP p E z).natDegree ≤ M
  unfold WPFiniteProductTail.unitPrimitiveP
  apply natDegree_sum_le_of_forall_le
  intro i hi
  by_cases hiM : i ≤ M
  · exact (natDegree_C_mul_le _ _).trans ((integratedGeometric_degree i z).trans hiM)
  · rw [coeff_eq_zero_of_natDegree_lt (hE.trans_lt (by omega)), Polynomial.C_0, zero_mul]
    simp

/-- The leading coefficient is independent of the fixed endpoint of the H row. -/
theorem branchH_last_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (branchHPolynomial p z : K[X]).coeff ((p - 1) / 2 - 1) =
      (originalEven p).coeff ((p - 1) / 2 - 1) *
        (((p - 1) / 2 - 1 : ℕ) : K)⁻¹ := by
  classical
  let M := (p - 1) / 2 - 1
  let E := originalEven (K := K) p
  have hM : 0 < M := by dsimp only [M]; omega
  have hMp : M < p := by dsimp only [M]; omega
  have hE : E.natDegree ≤ M := originalEven_degree p hp
  change (WPFiniteProductTail.unitPrimitiveP p E z).coeff M = E.coeff M * (M : K)⁻¹
  simp only [WPFiniteProductTail.unitPrimitiveP, finsetSum_coeff, coeff_C_mul]
  rw [Finset.sum_eq_single M]
  · rw [integratedGeometric_last M hM]
  · intro i hi hiM
    by_cases hiLt : i < M
    · rw [coeff_eq_zero_of_natDegree_lt ((integratedGeometric_degree i z).trans_lt hiLt), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt (hE.trans_lt (by omega)), zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_Ico.mpr ⟨hM, hMp⟩))

/-- The 2+1-3 cancellation removes exactly the deepest primitive coefficient. -/
theorem reciprocal_row_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (2 * branchHPolynomial p 4 + branchHPolynomial p (1 / 4) -
      3 * branchHPolynomial p 0 : K[X]).natDegree ≤ (p - 1) / 2 - 2 := by
  let M := (p - 1) / 2 - 1
  let Q : K[X] := 2 * branchHPolynomial p 4 + branchHPolynomial p (1 / 4) -
    3 * branchHPolynomial p 0
  have hQ : Q.natDegree ≤ M := by
    dsimp only [Q]
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_C_mul_le _ _).trans (branchH_sharp_degree p hp 4))
        (branchH_sharp_degree p hp (1 / 4))))
      ((natDegree_C_mul_le _ _).trans (branchH_sharp_degree p hp 0)))
  have hc : Q.coeff M = 0 := by
    dsimp only [Q, M]
    change (Polynomial.C (2 : K) * branchHPolynomial p 4 +
      branchHPolynomial p (1 / 4) - Polynomial.C (3 : K) *
        branchHPolynomial p 0).coeff ((p - 1) / 2 - 1) = 0
    simp only [coeff_sub, coeff_add, coeff_C_mul, branchH_last_coefficient p hp]
    ring
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_cases hiM : i = M
  · subst i
    exact hc
  · exact coeff_eq_zero_of_natDegree_lt (hQ.trans_lt (by dsimp only [M] at *; omega))

theorem calLPositive_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (calLPositive p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  unfold calLPositive
  rw [← Polynomial.C_neg]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (branchH_sharp_degree p hp (1 / 4)))
      (branchH_sharp_degree p hp 4))
  · apply (natDegree_C_mul_le _ _).trans
    exact (natDegree_sub_le _ _).trans (max_le (originalEven_degree p hp) (by simp))

theorem calL_branch_origin (p : ℕ) :
    GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero) (calL p : K[T;T⁻¹]) = 0 := by
  simp only [calL, map_sub, GreenLaurentOperators.ev, LaurentPolynomial.eval₂_C,
    RingHom.id_apply, sub_self]

theorem calL_derivative_normalization (p : ℕ) :
    D (calL p : K[T;T⁻¹]) = D (calLUnnormalized p) := by
  rw [calL, map_sub, D_C, sub_zero]

private theorem original_Abar_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent =
      -4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * (T 1 - 4) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc : (4 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 4 : K) = 1 := by
    change LaurentPolynomial.C (4 : K) * LaurentPolynomial.C (1 / 4 : K) = 1
    rw [← map_mul, mul_one_div_cancel h4, map_one]
  simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat, map_one, Polynomial.toLaurent_X]
  linear_combination -(T 1 - 4) * hc

private theorem quarter_H_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (branchHPolynomial p (1 / 4) : K[X]).toLaurent =
      -4 * (T 1 - 4) * ((originalEven p).toLaurent -
        LaurentPolynomial.C ((originalEven p).eval (1 / 4))) := by
  have hs : (T 1 - LaurentPolynomial.C (1 / 4 : K)) *
      D (branchHPolynomial p (1 / 4) : K[X]).toLaurent =
        (originalEven p).toLaurent -
          LaurentPolynomial.C ((originalEven p).eval (1 / 4)) := by
    have h := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
      (branchHPolynomial_source (K := K) p hp (1 / 4))
    simpa only [originalEven, map_mul, map_sub, Polynomial.toLaurent_X,
      Polynomial.toLaurent_C, ← D_toLaurent] using h
  rw [original_Abar_factor p hp]
  change _ = -4 * (T 1 - 4) * _
  linear_combination -4 * (T 1 - 4) * hs

private theorem four_H_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (branchHPolynomial p 4 : K[X]).toLaurent =
      -4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * ((originalEven p).toLaurent -
        LaurentPolynomial.C ((originalEven p).eval 4)) := by
  have hs : (T 1 - 4 : K[T;T⁻¹]) * D (branchHPolynomial p 4 : K[X]).toLaurent =
      (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval 4) := by
    have h := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
      (branchHPolynomial_source (K := K) p hp 4)
    simpa only [originalEven, map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X,
      Polynomial.toLaurent_C, ← D_toLaurent] using h
  rw [original_Abar_factor p hp]
  linear_combination -4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * hs

private theorem reciprocal_H_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (T 1 - LaurentPolynomial.C z * T 2) * D (invert (branchHPolynomial p z : K[X]).toLaurent) =
      -(invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval z)) := by
  have hs : (T (-1) - LaurentPolynomial.C z) *
      invert (D (branchHPolynomial p z : K[X]).toLaurent) =
        invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval z) := by
    have h := congrArg invert (congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
      (branchHPolynomial_source (K := K) p hp z))
    simpa only [originalEven, map_mul, map_sub, Polynomial.toLaurent_X,
      Polynomial.toLaurent_C, invert_T, invert_C, ← D_toLaurent] using h
  rw [D_invert]
  have ht1 : (T 1 * T (-2) : K[T;T⁻¹]) = T (-1) := by rw [← T_add]; norm_num
  have ht2 : (T 2 * T (-2) : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  linear_combination -hs - invert (D (branchHPolynomial p z).toLaurent) *
    (ht1 - LaurentPolynomial.C z * ht2)

private theorem reciprocal_quarter_H_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (invert (branchHPolynomial p (1 / 4) : K[X]).toLaurent) =
      -16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * T (-1) *
        (invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval (1 / 4))) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hq := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (mul_one_div_cancel h4)
  simp only [map_mul, map_ofNat, map_one] at hq
  have ht1 : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have ht2 : (T (-1) * T 2 : K[T;T⁻¹]) = T 1 := by rw [← T_add]; norm_num
  have hm : (WPFiniteZSource.Abar : K[X]).toLaurent =
      16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * T (-1) *
        (T 1 - LaurentPolynomial.C (1 / 4 : K) * T 2) := by
    rw [original_Abar_factor p hp]
    calc
      _ = 16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) *
          (1 - LaurentPolynomial.C (1 / 4 : K) * T 1) := by
        linear_combination 4 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * T 1 * hq
      _ = _ := by
        linear_combination -16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) *
          (ht1 - LaurentPolynomial.C (1 / 4 : K) * ht2)
  rw [hm]
  linear_combination 16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) * T (-1) *
    reciprocal_H_cleared (K := K) p hp (1 / 4)

private theorem reciprocal_four_H_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (invert (branchHPolynomial p 4 : K[X]).toLaurent) =
      -(T 1 - 4) * T (-1) *
        (invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval 4)) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hq := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (mul_one_div_cancel h4)
  simp only [map_mul, map_ofNat, map_one] at hq
  have ht1 : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have ht2 : (T (-1) * T 2 : K[T;T⁻¹]) = T 1 := by rw [← T_add]; norm_num
  have hm : (WPFiniteZSource.Abar : K[X]).toLaurent =
      (T 1 - 4) * T (-1) * (T 1 - 4 * T 2) := by
    rw [original_Abar_factor p hp]
    calc
      _ = ((T 1 - 4) * (1 - 4 * T 1) : K[T;T⁻¹]) := by
        linear_combination (T 1 - 4 : K[T;T⁻¹]) * hq
      _ = _ := by
        linear_combination -(T 1 - 4 : K[T;T⁻¹]) * (ht1 - 4 * ht2)
  rw [hm]
  have hs := reciprocal_H_cleared (K := K) p hp (4 : K)
  simp only [map_ofNat] at hs
  linear_combination (T 1 - 4) * T (-1) * hs

private theorem reciprocal_zero_H_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (invert (branchHPolynomial p 0 : K[X]).toLaurent) =
      -WPFiniteZSource.Abar.toLaurent * T (-1) *
        (invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval 0)) := by
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have hs := reciprocal_H_cleared (K := K) p hp (0 : K)
  simp only [map_zero, zero_mul, sub_zero] at hs
  linear_combination WPFiniteZSource.Abar.toLaurent * T (-1) * hs -
    WPFiniteZSource.Abar.toLaurent * D (invert (branchHPolynomial p 0).toLaurent) * ht

/-- The reciprocal primitive retains both endpoint poles and the original zero row. -/
theorem calLNegative_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (calLNegative p : K[T;T⁻¹]) =
      LaurentPolynomial.C (2 / 15 : K) * T (-1) *
        (2 * (T 1 - 4) * (invert (originalEven p).toLaurent -
            LaurentPolynomial.C ((originalEven p).eval 4)) +
          16 * (T 1 - LaurentPolynomial.C (1 / 4 : K)) *
            (invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval (1 / 4))) -
          3 * WPFiniteZSource.Abar.toLaurent *
            (invert (originalEven p).toLaurent - LaurentPolynomial.C ((originalEven p).eval 0))) := by
  have ha := reciprocal_quarter_H_source (K := K) p hp
  have hb := reciprocal_four_H_source (K := K) p hp
  have h0 := reciprocal_zero_H_source (K := K) p hp
  have hD2 : D (2 : K[T;T⁻¹]) = 0 := D_C (2 : K)
  have hD3 : D (3 : K[T;T⁻¹]) = 0 := D_C (3 : K)
  simp only [calLNegative, D_mul, map_neg, D_C, map_add, map_sub, hD2, hD3,
    neg_zero, zero_mul, zero_add]
  linear_combination -LaurentPolynomial.C (2 / 15 : K) * (2 * hb + ha - 3 * h0)

theorem calLPositive_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (calLPositive p : K[X]).toLaurent =
      LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * (Dstar p).toLaurent -
        LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) +
        LaurentPolynomial.C (2 * WPFiniteNC122.h p) -
        LaurentPolynomial.C (16 / 15 : K) * (T 1 - 4) *
          LaurentPolynomial.C ((originalEven p).eval (1 / 4)) -
        LaurentPolynomial.C (8 / 15 : K) * (T 1 - LaurentPolynomial.C (1 / 4 : K)) *
          LaurentPolynomial.C ((originalEven p).eval 4) := by
  have ha := quarter_H_source (K := K) p hp
  have hb := four_H_source (K := K) p hp
  have he := congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹])
    (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_one, map_pow, Polynomial.toLaurent_C, ← D_toLaurent] at he
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hcoef : (2 / 5 : K) = 3 * (2 / 15) := by
    field_simp [h5, h15]
    ring
  have hcoefA : (16 / 15 : K) = 8 * (2 / 15) := by ring
  have hcoefB : (8 / 15 : K) = 4 * (2 / 15) := by ring
  have hcoefH : (2 * WPFiniteNC122.h p : K) =
      3 * (4 * WPFiniteNC122.h p / 15) * (5 / 2) := by
    field_simp [h2, h15]
    ring
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hcoefC : (LaurentPolynomial.C (2 / 5 : K) : K[T;T⁻¹]) =
      3 * LaurentPolynomial.C (2 / 15 : K) := by
    simpa only [map_mul, map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hcoef
  have hcoefAC : (LaurentPolynomial.C (16 / 15 : K) : K[T;T⁻¹]) =
      8 * LaurentPolynomial.C (2 / 15 : K) := by
    simpa only [map_mul, map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hcoefA
  have hcoefBC : (LaurentPolynomial.C (8 / 15 : K) : K[T;T⁻¹]) =
      4 * LaurentPolynomial.C (2 / 15 : K) := by
    simpa only [map_mul, map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hcoefB
  have hcoefHC : (LaurentPolynomial.C (2 * WPFiniteNC122.h p) : K[T;T⁻¹]) =
      3 * LaurentPolynomial.C (4 * WPFiniteNC122.h p / 15) *
        LaurentPolynomial.C (5 / 2 : K) := by
    simpa only [map_mul, map_ofNat] using
      congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hcoefH
  have hquarter := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    (mul_one_div_cancel h4)
  simp only [map_mul, map_ofNat, map_one] at hquarter
  have hE : (originalEven p : K[X]).toLaurent = -3 * (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  have hD2 : D (2 : K[T;T⁻¹]) = 0 := D_C (2 : K)
  have hD3 : D (3 : K[T;T⁻¹]) = 0 := D_C (3 : K)
  have hder : D (calLPositive p : K[X]).toLaurent =
      -LaurentPolynomial.C (2 / 15 : K) *
        (2 * D (branchHPolynomial p (1 / 4) : K[X]).toLaurent +
          D (branchHPolynomial p 4 : K[X]).toLaurent) +
      3 * LaurentPolynomial.C (4 * WPFiniteNC122.h p / 15) *
        D (Dstar p : K[X]).toLaurent := by
    simp only [calLPositive, originalEven, map_sub, map_mul, map_neg, map_ofNat,
      Polynomial.toLaurent_C, D_mul, D_C, hD2, hD3, map_add, neg_zero,
      zero_mul, zero_add, sub_zero]
    ring
  rw [hE] at ha hb
  rw [hder]
  simp only [hcoefC, hcoefAC, hcoefBC, hcoefHC]
  linear_combination -LaurentPolynomial.C (2 / 15 : K) * (2 * ha + hb) +
    3 * LaurentPolynomial.C (4 * WPFiniteNC122.h p / 15) * he +
    3 * LaurentPolynomial.C (2 / 15 : K) * (Dstar p).toLaurent * hquarter

/-- The two actual even endpoints supply the sole remaining source cancellation. -/
theorem originalEven_endpoint_sum (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (originalEven p : K[X]).eval (1 / 4) + (originalEven p).eval 4 =
      WPFiniteNC122.h p / 2 := by
  obtain ⟨ha, hb⟩ := Dstar_endpoints (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  simp only [originalEven, eval_mul, eval_neg, eval_C, ha, hb]
  field_simp [h2, h3, h6]
  ring

/-- The full adjoint primitive has the original simple-pole form, including its origin pole. -/
theorem calL_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteZSource.Abar.toLaurent * D (calL p : K[T;T⁻¹]) =
      LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) *
        ((Dstar p).toLaurent + invert (Dstar p).toLaurent) -
      LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) -
      clearedLambda p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (2 / 5 : K) = 6 * (15 : K)⁻¹ := by field_simp [h5, h15]; ring
  have h25C := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) h25
  simp only [map_mul, map_ofNat] at h25C
  have he : (2 : K) * ((originalEven p).eval (1 / 4) + (originalEven p).eval 4) =
      WPFiniteNC122.h p := by
    rw [originalEven_endpoint_sum p hp]
    field_simp [h2]
  have heC := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) he
  have hquarter := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    (mul_inv_cancel₀ h4)
  have hfifteen := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    (mul_inv_cancel₀ h15)
  simp only [map_add, map_mul, map_ofNat, map_one] at heC hquarter hfifteen
  have ht : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  have hEv : invert (originalEven p : K[X]).toLaurent =
      -3 * invert (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  rw [calL_derivative_normalization, calLUnnormalized, map_add, mul_add,
    calLPositive_cleared_source p hp, calLNegative_cleared_source p hp]
  simp only [h25C]
  simp only [hEv, clearedLambda, kappa, WPFiniteZSource.Abar, div_eq_mul_inv, map_mul,
    map_add, map_sub, map_neg, map_ofNat, map_one, Polynomial.toLaurent_X,
    one_mul] at heC ⊢
  linear_combination
    (6 * LaurentPolynomial.C ((15 : K)⁻¹) * (33 - 12 * T 1) *
        invert (Dstar p).toLaurent +
      2 * LaurentPolynomial.C ((15 : K)⁻¹) *
        ((1 - 4 * T 1) * LaurentPolynomial.C ((originalEven p).eval ((4 : K)⁻¹)) -
          8 * (T 1 - 4) * LaurentPolynomial.C ((originalEven p).eval 4))) * ht +
    LaurentPolynomial.C ((15 : K)⁻¹) * (33 - 12 * T 1) * heC -
    2 * LaurentPolynomial.C (WPFiniteNC122.h p) * hfifteen +
    (2 * LaurentPolynomial.C ((15 : K)⁻¹) * LaurentPolynomial.C ((originalEven p).eval 4) +
      24 * LaurentPolynomial.C ((15 : K)⁻¹) * T (-1) * invert (Dstar p).toLaurent +
      8 * LaurentPolynomial.C ((15 : K)⁻¹) * T (-1) *
        LaurentPolynomial.C ((originalEven p).eval ((4 : K)⁻¹)) +
      LaurentPolynomial.C ((15 : K)⁻¹) * LaurentPolynomial.C (WPFiniteNC122.h p)) * hquarter

private theorem calLNegative_row (p : ℕ) :
    (calLNegative p : K[T;T⁻¹]) =
      LaurentPolynomial.C (-(2 / 15 : K)) *
        invert (2 * branchHPolynomial p 4 + branchHPolynomial p (1 / 4) -
          3 * branchHPolynomial p 0 : K[X]).toLaurent := by
  simp only [calLNegative, map_sub, map_add, map_mul, map_ofNat, map_neg]

private theorem constant_coeff_outside (c : K) (j : ℤ) (hj : j ≠ 0) :
    (LaurentPolynomial.C c : K[T;T⁻¹]).coeff j = 0 := by
  rw [← Polynomial.toLaurent_C]
  apply WPFiniteJCarrier.toLaurent_coeff_outside
  by_cases hn : j < 0
  · exact Or.inl hn
  · exact Or.inr (by have hc : (Polynomial.C c).natDegree = 0 := natDegree_C c; omega)

/-- The reciprocal leading-coefficient cancellation bounds the entire primitive. -/
theorem calL_coeff_outside (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (j : ℤ) (hj : j < -(((p - 1) / 2 - 2 : ℕ) : ℤ) ∨
      (((p - 1) / 2 - 1 : ℕ) : ℤ) < j) :
    (calL p : K[T;T⁻¹]).coeff j = 0 := by
  let Q : K[X] := 2 * branchHPolynomial p 4 + branchHPolynomial p (1 / 4) -
    3 * branchHPolynomial p 0
  have hQ : Q.natDegree ≤ (p - 1) / 2 - 2 := reciprocal_row_degree p hp
  have hP : (calLPositive p : K[X]).natDegree ≤ (p - 1) / 2 - 1 :=
    calLPositive_degree p hp
  have hpos : (calLPositive p : K[X]).toLaurent.coeff j = 0 := by
    apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hneg : Q.toLaurent.coeff (-j) = 0 := by
    apply WPFiniteJCarrier.toLaurent_coeff_outside
    rcases hj with hj | hj
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hj0 : j ≠ 0 := by rcases hj with hj | hj <;> omega
  rw [calL, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    constant_coeff_outside _ _ hj0, sub_zero]
  rw [calLUnnormalized, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    hpos, zero_add, calLNegative_row, GreenLaurentOperators.C_mul_coeff, invert_apply]
  change (-(2 / 15 : K)) * Q.toLaurent.coeff (-j) = 0
  rw [hneg, mul_zero]

theorem calL_support (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (calL p : K[T;T⁻¹]).coeff.support ⊆
      Finset.Icc (-(((p - 1) / 2 - 2 : ℕ) : ℤ)) (((p - 1) / 2 - 1 : ℕ) : ℤ) := by
  intro j hj
  apply Finset.mem_Icc.mpr
  have hc := Finsupp.mem_support_iff.mp hj
  constructor
  · by_contra hn
    exact hc (calL_coeff_outside p hp j (Or.inl (by omega)))
  · by_contra hn
    exact hc (calL_coeff_outside p hp j (Or.inr (by omega)))

private theorem small_signed_unit (p : ℕ) [Fact p.Prime] [CharP K p]
    (j : ℤ) (hj : -(p : ℤ) < j ∧ j < (p : ℤ)) (hj0 : j ≠ 0) : (j : K) ≠ 0 := by
  by_cases hpos : 0 < j
  · exact integer_unit_in_band p j ⟨hpos, hj.2⟩
  · have hn := integer_unit_in_band (K := K) p (-j) (by omega)
    simpa only [Int.cast_neg, neg_ne_zero] using hn

/-- In this band the derivative leaves exactly the constant, fixed by the value at -1. -/
theorem normalized_small_band_unique (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (F G : K[T;T⁻¹])
    (hF : ∀ j, j < -(((p - 1) / 2 - 2 : ℕ) : ℤ) ∨
      (((p - 1) / 2 - 1 : ℕ) : ℤ) < j → F.coeff j = 0)
    (hG : ∀ j, j < -(((p - 1) / 2 - 2 : ℕ) : ℤ) ∨
      (((p - 1) / 2 - 1 : ℕ) : ℤ) < j → G.coeff j = 0)
    (hD : D F = D G)
    (hbranch : GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero) F =
      GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero) G) : F = G := by
  have hcoeff (j : ℤ) (hj0 : j ≠ 0) : F.coeff j = G.coeff j := by
    by_cases hj : -(p : ℤ) < j ∧ j < (p : ℤ)
    · have hd := congrArg (fun L : K[T;T⁻¹] => L.coeff (j - 1)) hD
      rw [D_coeff, D_coeff, sub_add_cancel] at hd
      exact mul_left_cancel₀ (small_signed_unit p j hj hj0) hd
    · rw [hF j (by omega), hG j (by omega)]
  have hConst : F - G = LaurentPolynomial.C (F.coeff 0 - G.coeff 0) := by
    ext j
    by_cases hj0 : j = 0
    · subst j
      rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
      simpa only [Polynomial.toLaurent_C, Polynomial.coeff_C_zero, Nat.cast_zero] using
        (WPFiniteJCarrier.toLaurent_coeff_nat
          (Polynomial.C (F.coeff 0 - G.coeff 0)) 0).symm
    · rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hcoeff j hj0, sub_self,
        constant_coeff_outside _ _ hj0]
  have h0 : F.coeff 0 - G.coeff 0 = 0 := by
    have he := congrArg (GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero)) hConst
    rw [map_sub, hbranch, sub_self] at he
    simpa only [GreenLaurentOperators.ev, LaurentPolynomial.eval₂_C, RingHom.id_apply] using he.symm
  rw [h0, map_zero] at hConst
  exact sub_eq_zero.mp hConst

/-- The actual cleared source and original branch normalization identify the full small primitive. -/
theorem calL_unique (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (F : K[T;T⁻¹])
    (hF : ∀ j, j < -(((p - 1) / 2 - 2 : ℕ) : ℤ) ∨
      (((p - 1) / 2 - 1 : ℕ) : ℤ) < j → F.coeff j = 0)
    (hbranch : GreenLaurentOperators.ev (-1) (neg_ne_zero.mpr one_ne_zero) F = 0)
    (hsource : WPFiniteZSource.Abar.toLaurent * D F =
      LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) *
        ((Dstar p).toLaurent + invert (Dstar p).toLaurent) -
      LaurentPolynomial.C (2 * WPFiniteNC122.h p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) -
      clearedLambda p) : F = calL p := by
  apply normalized_small_band_unique p hp F (calL p) hF (calL_coeff_outside p hp)
  · exact mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := K) p hp)
      (hsource.trans (calL_cleared_source p hp).symm)
  · rw [hbranch, calL_branch_origin]

end WPFieldAssembly.NativeJointSuccessorMixedPrimitive
