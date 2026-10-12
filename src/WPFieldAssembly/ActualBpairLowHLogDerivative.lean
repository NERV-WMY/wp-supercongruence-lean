import WPFieldAssembly.ActualBpairLowHIntegralRelations
import WPFieldAssembly.ActualBpairLowHBranchTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteProductTail WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The whole original two-end density, including the dx/x origin subtraction. -/
noncomputable def lowHTwoEndDensity (H : K[X]) : K[X] :=
  2 * lowHqCubicDensity H - (lowHCubicY H).divX

noncomputable def lowHKernelRowZero (H : K[X]) : K[X] :=
  (Polynomial.C (20 : K) * X + Polynomial.C (15 / 2 : K)) * lowHBranchYQuotient H

noncomputable def lowHKernelRowOne (H : K[X]) : K[X] :=
  (Polynomial.C (113 / 2 : K) * X + 4) * lowHBranchYQuotient H

noncomputable def lowHKernelRowTwo (H : K[X]) : K[X] :=
  (Polynomial.C (1953 / 8 : K) * X - Polynomial.C (113 / 2 : K)) * lowHBranchYQuotient H

/-- Every original row, including the top negative phase, has its actual full polynomial bound. -/
theorem lowH_kernel_rows_degree (d : ℕ) (hd : 1 ≤ d) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHKernelRowZero H).natDegree ≤ 3 * d - 1 ∧
      (lowHKernelRowOne H).natDegree ≤ 3 * d - 1 ∧
      (lowHKernelRowTwo H).natDegree ≤ 3 * d - 1 := by
  have hR := lowHBranchYQuotient_degree d hd H hH
  have h0 : (Polynomial.C (20 : K) * (X : K[X]) + Polynomial.C (15 / 2 : K)).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have h1 : (Polynomial.C (113 / 2 : K) * (X : K[X]) + 4).natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have h2 : (Polynomial.C (1953 / 8 : K) * (X : K[X]) - Polynomial.C (113 / 2 : K)).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  unfold lowHKernelRowZero lowHKernelRowOne lowHKernelRowTwo
  refine ⟨natDegree_mul_le.trans (by omega),
    natDegree_mul_le.trans (by omega), natDegree_mul_le.trans (by omega)⟩

/-- The exact row combination keeps the original constant coefficient before division by X. -/
theorem lowH_kernel_rows_origin_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) (h0 : H.coeff 0 = 0) :
    X * lowHTwoEndDensity H = lowHKernelRowOne H - X * lowHKernelRowZero H -
      Polynomial.C ((lowHKernelRowOne H).coeff 0) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hrow : (113 / 2 : K) - 15 / 2 = 49 := by field_simp [h2]; ring
  have hc := congrArg (Polynomial.C : K →+* K[X]) hrow
  simp only [map_sub, map_ofNat] at hc
  have hdiv := X_mul_divX_add (lowHCubicY H)
  have hder : 2 * X * lowHqCubicDensity H - lowHCubicY H =
      lowHKernelRowOne H - X * lowHKernelRowZero H := by
    rw [lowHqCubicDensity, lowHCubicY_source H h0]
    simp only [WPFiniteNC122Residue.VP, derivative_mul, derivative_C, derivative_sub,
      derivative_X, derivative_pow, derivative_ofNat, derivative_one,
      zero_mul, zero_add, sub_zero, map_ofNat, one_div,
      lowHKernelRowOne, lowHKernelRowZero, lowHBranchYQuotient]
    simp only [Nat.cast_ofNat, map_ofNat]
    linear_combination -X * (Polynomial.C ((125 : K)⁻¹) * (4 * X - 1) *
      H.divX.comp (Polynomial.C ((125 : K)⁻¹) * (4 - X) * (4 * X - 1) ^ 2)) * hc
  have hconst : (lowHKernelRowOne H).coeff 0 = -(lowHCubicY H).coeff 0 := by
    have he := congrArg (fun Q : K[X] => Q.eval 0) hder
    simpa only [eval_sub, eval_mul, eval_X, eval_ofNat, zero_mul, mul_zero, zero_sub,
      sub_zero, ← coeff_zero_eq_eval_zero] using he.symm
  rw [lowHTwoEndDensity, mul_sub, hconst, map_neg]
  linear_combination hder - hdiv

theorem lowH_two_end_density_integral (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) (c : K) :
    (lowHIntegralP p (lowHTwoEndDensity H)).eval c =
      2 * ((lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval c) -
        (lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0)) -
        originPrimitive p (lowHCubicY H) c := by
  have hs : lowHIntegralP p (lowHTwoEndDensity H) =
      Polynomial.C (2 : K) * lowHIntegralP p (lowHqCubicDensity H) -
        lowHIntegralP p (lowHCubicY H).divX := by
    have hlin := lowHIntegralP_sub_C_mul p (1 : K) (2 * lowHqCubicDensity H)
      (lowHCubicY H).divX
    rw [map_one, one_mul] at hlin
    rw [lowHTwoEndDensity, hlin]
    have hadd := lowHIntegralP_add_C_mul p (1 : K) (lowHqCubicDensity H) (lowHqCubicDensity H)
    simp only [map_one, one_mul, ← two_mul] at hadd
    rw [hadd]
    simp only [map_ofNat, one_mul]
  rw [hs, eval_sub, eval_mul, eval_C, lowHqCubicDensity_integral p hp d hd hband H hH h0,
    lowH_auxiliary_origin_integral]

theorem lowH_two_end_density_both_end_integrals (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) :
    (lowHIntegralP p (lowHTwoEndDensity H)).eval (1 / 4) =
        -2 * (lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) -
          originPrimitive p (lowHCubicY H) (1 / 4) ∧
      (lowHIntegralP p (lowHTwoEndDensity H)).eval 4 =
        -2 * (lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) -
          originPrimitive p (lowHCubicY H) 4 := by
  have hz : (lowHqPrimitive p H).eval 0 = 0 := unitPrimitiveP_zero p H 0
  simp only [lowH_two_end_density_integral p hp d hd hband H hH h0,
    lowHCubicV_quarter p hp, lowHCubicV_four, hz, zero_sub, mul_neg, neg_mul, and_self]

/-- The two proper endpoints cancel the entire origin primitive without an assigned value. -/
theorem lowH_two_end_derivative_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) :
    (8 / 15 : K) * (lowHIntegralP p (lowHTwoEndDensity H)).eval (1 / 4) -
      (1 / 30 : K) * (lowHIntegralP p (lowHTwoEndDensity H)).eval 4 =
        -(lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) +
          (2 / 15 : K) * ((1 / 4) * originPrimitive p (lowHCubicY H) 4 -
            4 * originPrimitive p (lowHCubicY H) (1 / 4)) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h30 : (30 : K) ≠ 0 := by convert mul_ne_zero h2 h15 using 1; norm_num
  have h60 : (60 : K) ≠ 0 := by convert mul_ne_zero h2 h30 using 1; norm_num
  have he := lowH_two_end_density_both_end_integrals p hp d hd hband H hH h0
  rw [he.1, he.2]
  field_simp [h2, h3, h4, h5, h15, h30, h60]
  ring

/-- The full row identity is integrated with its constant coefficient still separated. -/
theorem lowH_kernel_rows_integral (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) (h0 : H.coeff 0 = 0) (c : K) :
    (lowHIntegralP p (lowHTwoEndDensity H)).eval c =
      originPrimitive p (lowHKernelRowOne H) c -
        (lowHIntegralP p (lowHKernelRowZero H)).eval c := by
  rw [lowHIntegralP_eval, lowHIntegralP_eval, lowH_kernel_rows_origin_source p hp H h0]
  unfold originPrimitive
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := Finset.mem_Ico.mp hn; omega
  rw [coeff_sub, coeff_sub, coeff_C, if_neg hn0, sub_zero]
  ring

private theorem lowH_shifted_log_row (p n : ℕ) (hn : 1 ≤ n) (c : K) (R : K[X]) :
    (T (-(n : ℤ)) * (lowHLog p c * R).toLaurent).coeff (-1) =
      (lowHLog p c * R).coeff (n - 1) := by
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-(n : ℤ)) (-1)
    (lowHLog p c * R).toLaurent
  simp only [map_one, one_mul] at he
  rw [he, show (-1 : ℤ) - -(n : ℤ) = ((n - 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]

private theorem lowH_log_row_origin (p : ℕ) (c : K) (R : K[X]) :
    (lowHLog p c * R).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero, lowHLog_zero, zero_mul]

/-- The full three-band cleared derivative is paired with the full logarithm before coefficient extraction. -/
theorem lowH_three_row_log_residue (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (c : K) (hc : c ≠ 0) (R0 R1 R2 : K[X])
    (hR0 : R0.natDegree < p - 1) (hR1 : R1.natDegree < p - 1)
    (hR2 : R2.natDegree < p - 1) :
    (T (-(p : ℤ)) * (lowHLog p c).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
      (R0.toLaurent + T (-(p : ℤ)) * R1.toLaurent +
        T (-2 * (p : ℤ)) * R2.toLaurent)).coeff (-1) =
      c⁻¹ ^ p * (originPrimitive p R1 c - (lowHIntegralP p R0).eval c) := by
  have h01 : (T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ) : K[T;T⁻¹]) = T (-1) := by
    rw [← T_add]; congr 1; omega
  have h02 : (T (-(p : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-((2 * p : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; push_cast; ring
  have h11 : (T (-1) * T (-(p : ℤ)) : K[T;T⁻¹]) =
      T (-((p + 1 : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; push_cast; ring
  have h20 : (T (-(p : ℤ)) * T (-2 * (p : ℤ)) : K[T;T⁻¹]) = T (-((3 * p : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; push_cast; ring
  have h21 : (T (-1) * T (-2 * (p : ℤ)) : K[T;T⁻¹]) =
      T (-((2 * p + 1 : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; push_cast; ring
  have he : T (-(p : ℤ)) * (lowHLog p c).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
      (R0.toLaurent + T (-(p : ℤ)) * R1.toLaurent + T (-2 * (p : ℤ)) * R2.toLaurent) =
      T (-(p : ℤ)) * (lowHLog p c * R0).toLaurent -
        T (-1) * (lowHLog p c * R0).toLaurent +
        T (-((2 * p : ℕ) : ℤ)) * (lowHLog p c * R1).toLaurent -
        T (-((p + 1 : ℕ) : ℤ)) * (lowHLog p c * R1).toLaurent +
        T (-((3 * p : ℕ) : ℤ)) * (lowHLog p c * R2).toLaurent -
        T (-((2 * p + 1 : ℕ) : ℤ)) * (lowHLog p c * R2).toLaurent := by
    calc
      _ = (lowHLog p c).toLaurent *
          ((T (-(p : ℤ)) - T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ)) * R0.toLaurent +
            (T (-(p : ℤ)) * T (-(p : ℤ)) -
              T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ) * T (-(p : ℤ))) * R1.toLaurent +
            (T (-(p : ℤ)) * T (-2 * (p : ℤ)) -
              T (-(p : ℤ)) * T ((p - 1 : ℕ) : ℤ) * T (-2 * (p : ℤ))) * R2.toLaurent) := by ring
      _ = _ := by rw [h01, h02, h11, h20, h21]; simp only [map_mul]; ring
  rw [he]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply]
  rw [lowH_shifted_log_row p p (by omega),
    show T (-1) = (T (-((1 : ℕ) : ℤ)) : K[T;T⁻¹]) by rfl,
    lowH_shifted_log_row p 1 (by omega),
    lowH_shifted_log_row p (2 * p) (by omega),
    lowH_shifted_log_row p (p + 1) (by omega),
    lowH_shifted_log_row p (3 * p) (by omega),
    lowH_shifted_log_row p (2 * p + 1) (by omega)]
  simp only [Nat.sub_self, Nat.add_sub_cancel, lowH_log_row_origin, sub_zero]
  rw [lowH_log_green_coefficient p hp R0 hR0 c hc,
    lowH_log_product_upper_zero p hp R1 hR1 c (2 * p - 1) le_rfl,
    lowHLog_diagonal p hp R1 (by omega) c hc,
    lowH_log_product_upper_zero p hp R2 hR2 c (3 * p - 1) (by omega),
    lowH_log_product_upper_zero p hp R2 hR2 c (2 * p) (by omega)]
  ring

/-- All original negative phases and both finite logs are kept until the common two-end contraction. -/
theorem lowH_original_three_rows_two_end_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p)
    (H : K[X]) (hH : H.natDegree ≤ d) (h0 : H.coeff 0 = 0) :
    (LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
      (1 - T ((p - 1 : ℕ) : ℤ)) *
      ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
        T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent)).coeff (-1) =
      -(lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) +
        (2 / 15 : K) * ((1 / 4) * originPrimitive p (lowHCubicY H) 4 -
          4 * originPrimitive p (lowHCubicY H) (1 / 4)) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h30 : (30 : K) ≠ 0 := by convert mul_ne_zero h2 h15 using 1; norm_num
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hr := lowH_kernel_rows_degree d hd H hH
  have hR0 : (lowHKernelRowZero H).natDegree < p - 1 := by omega
  have hR1 : (lowHKernelRowOne H).natDegree < p - 1 := by omega
  have hR2 : (lowHKernelRowTwo H).natDegree < p - 1 := by omega
  have hb := lowH_three_row_log_residue p hp (4 : K) h4
    (lowHKernelRowZero H) (lowHKernelRowOne H) (lowHKernelRowTwo H) hR0 hR1 hR2
  have ha := lowH_three_row_log_residue p hp (1 / 4 : K) (one_div_ne_zero h4)
    (lowHKernelRowZero H) (lowHKernelRowOne H) (lowHKernelRowTwo H) hR0 hR1 hR2
  rw [← lowH_kernel_rows_integral p hp H h0] at hb ha
  rw [inv_pow, h4p] at hb
  rw [inv_pow, hap, one_div, inv_inv] at ha
  calc
    _ = (-2 / 15 : K) *
        ((T (-(p : ℤ)) * (lowHLog p 4).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
          ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
            T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent)).coeff (-1) -
          (T (-(p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
          ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
            T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent)).coeff (-1)) := by
      rw [show LaurentPolynomial.C (-2 / 15 : K) * T (-(p : ℤ)) *
          ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
          (1 - T ((p - 1 : ℕ) : ℤ)) *
          ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
            T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent) =
          LaurentPolynomial.C (-2 / 15 : K) *
            (T (-(p : ℤ)) * (lowHLog p 4).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
              ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
                T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent) -
            T (-(p : ℤ)) * (lowHLog p (1 / 4)).toLaurent * (1 - T ((p - 1 : ℕ) : ℤ)) *
              ((lowHKernelRowZero H).toLaurent + T (-(p : ℤ)) * (lowHKernelRowOne H).toLaurent +
                T (-2 * (p : ℤ)) * (lowHKernelRowTwo H).toLaurent)) by ring]
      rw [C_mul_coeff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    _ = (8 / 15 : K) * (lowHIntegralP p (lowHTwoEndDensity H)).eval (1 / 4) -
        (1 / 30 : K) * (lowHIntegralP p (lowHTwoEndDensity H)).eval 4 := by
      simp only [one_div]
      rw [hb, ha]
      field_simp [h2, h3, h4, h5, h15, h30]
      ring
    _ = _ := lowH_two_end_derivative_contraction p hp d hd hband H hH h0

end WPFieldAssembly.ActualBpairContraction
