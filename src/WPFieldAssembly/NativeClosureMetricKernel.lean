import WPFieldAssembly.NativeClosureKernelValues

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPActualCanonicalFinitePart WPCartierPoleProjection
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2000000

/-- The complete first metric kernel phase, including its actual origin and -p coefficient. -/
noncomputable def metricKernelPrimitive (p : ℕ) [Fact p.Prime]
    (m : (ZMod p)[X]) : (ZMod p)[T;T⁻¹] :=
  m.toLaurent + T (-(p : ℤ)) * (Polynomial.C (-2 / 3 : ZMod p) * m).toLaurent

theorem metricKernelPrimitive_coeff (p : ℕ) [Fact p.Prime]
    (m : (ZMod p)[X]) (j : ℤ) :
    (metricKernelPrimitive p m).coeff j = m.toLaurent.coeff j +
      (Polynomial.C (-2 / 3 : ZMod p) * m).toLaurent.coeff (j + p) := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (-(p : ℤ)) j
    (Polynomial.C (-2 / 3 : ZMod p) * m).toLaurent
  simp only [map_one, one_mul] at hs
  rw [metricKernelPrimitive, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hs]
  congr 2
  omega

/-- The full finite polynomial bound, rather than a deleted source slot, excludes higher phases. -/
theorem metricKernelPrimitive_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) (j : ℤ)
    (hj : j ∈ (metricKernelPrimitive p m).coeff.support) :
    -(p : ℤ) ≤ j ∧ j ≤ (p - 2 : ℕ) := by
  have hscaled := (Polynomial.natDegree_C_mul_le (-2 / 3 : ZMod p) m).trans hm
  have hne := Finsupp.mem_support_iff.mp hj
  constructor
  · by_contra hlow
    have h0 := WPFiniteJCarrier.toLaurent_coeff_outside m j (Or.inl (by omega))
    have h1 := WPFiniteJCarrier.toLaurent_coeff_outside
      (Polynomial.C (-2 / 3 : ZMod p) * m) (j + p) (Or.inl (by omega))
    rw [metricKernelPrimitive_coeff, h0, h1, zero_add] at hne
    exact hne rfl
  · by_contra hhigh
    have h0 := WPFiniteJCarrier.toLaurent_coeff_outside m j (Or.inr (by omega))
    have h1 := WPFiniteJCarrier.toLaurent_coeff_outside
      (Polynomial.C (-2 / 3 : ZMod p) * m) (j + p) (Or.inr (by omega))
    rw [metricKernelPrimitive_coeff, h0, h1, zero_add] at hne
    exact hne rfl

theorem metricKernelPrimitive_slots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) :
    (metricKernelPrimitive p m).coeff 0 = m.coeff 0 ∧
      (metricKernelPrimitive p m).coeff (-(p : ℤ)) = (-2 / 3 : ZMod p) * m.coeff 0 ∧
      (metricKernelPrimitive p m).coeff (p : ℤ) = 0 := by
  have hscaled := (Polynomial.natDegree_C_mul_le (-2 / 3 : ZMod p) m).trans hm
  have hmp : m.toLaurent.coeff (p : ℤ) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hmn : m.toLaurent.coeff (-(p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hsp : (Polynomial.C (-2 / 3 : ZMod p) * m).toLaurent.coeff (p : ℤ) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hs2 : (Polynomial.C (-2 / 3 : ZMod p) * m).toLaurent.coeff (2 * (p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  refine ⟨?_, ?_, ?_⟩
  · rw [metricKernelPrimitive_coeff, zero_add, hsp, add_zero]
    exact WPFiniteJCarrier.toLaurent_coeff_nat m 0
  · rw [metricKernelPrimitive_coeff, neg_add_cancel, hmn, zero_add,
      ← show ((0 : ℕ) : ℤ) = 0 from rfl, WPFiniteJCarrier.toLaurent_coeff_nat,
      Polynomial.coeff_C_mul]
  · rw [metricKernelPrimitive_coeff, hmp, show (p : ℤ) + p = 2 * p by omega,
      hs2, zero_add]

/-- The two endpoint evaluations and the negative half keep the same complete polynomial. -/
theorem metricKernelPrimitive_values (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) :
    originalKernelValue p (metricKernelPrimitive p m) =
      (47 / 18 : ZMod p) * m.eval (1 / 4) - (103 / 36 : ZMod p) * m.eval 4 := by
  have hscaled := (Polynomial.natDegree_C_mul_le (-2 / 3 : ZMod p) m).trans hm
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have h6 : (6 : ZMod p) ≠ 0 := by
    rw [show (6 : ZMod p) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 h3
  have h18 : (18 : ZMod p) ≠ 0 := by
    rw [show (18 : ZMod p) = 2 * 3 ^ 2 by norm_num]
    exact mul_ne_zero h2 (pow_ne_zero 2 h3)
  have h36 : (36 : ZMod p) ≠ 0 := by
    rw [show (36 : ZMod p) = 4 * 3 ^ 2 by norm_num]
    exact mul_ne_zero h4 (pow_ne_zero 2 h3)
  have ha0 := kernel_valueAt_shifted_polynomial p m 0 (1 / 4) (one_div_ne_zero h4)
  have hb0 := kernel_valueAt_shifted_polynomial p m 0 4 h4
  have ha1 := kernel_valueAt_shifted_polynomial p (Polynomial.C (-2 / 3) * m)
    (-(p : ℤ)) (1 / 4) (one_div_ne_zero h4)
  have hb1 := kernel_valueAt_shifted_polynomial p (Polynomial.C (-2 / 3) * m)
    (-(p : ℤ)) 4 h4
  simp only [T_zero, one_mul, zpow_zero] at ha0 hb0
  have hap : (1 / 4 : ZMod p) ^ (-(p : ℤ)) = 4 := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow, ZMod.pow_card, inv_inv]
  have hbp : (4 : ZMod p) ^ (-(p : ℤ)) = 1 / 4 := by
    rw [zpow_neg, zpow_natCast, ZMod.pow_card, one_div]
  rw [hap] at ha1
  rw [hbp] at hb1
  have hna := kernel_negativeValue_negative_phase p (Polynomial.C (-2 / 3) * m)
    (by omega) (1 / 4)
  have hnb := kernel_negativeValue_negative_phase p (Polynomial.C (-2 / 3) * m)
    (by omega) 4
  unfold originalKernelValue metricKernelPrimitive
  rw [kernel_valueAt_add, kernel_valueAt_add, kernel_negativeValue_add,
    kernel_negativeValue_add, ha0, hb0, kernel_negativeValue_polynomial,
    kernel_negativeValue_polynomial, hna, hnb, ha1, hb1]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  field_simp [h3, h4, h6, h18, h36]
  ring

/-- The original first kernel slot contributes the two proper ends and m(0)/4. -/
theorem metric_original_kernel_slot (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) :
    (literalKB (K := ZMod p) p * D (metricKernelPrimitive p m)).coeff (-1) =
      (47 / 18 : ZMod p) * m.eval (1 / 4) - (103 / 36 : ZMod p) * m.eval 4 +
        m.coeff 0 / 4 := by
  have hs := original_kernel_derivative_with_slots p hp (metricKernelPrimitive p m)
    (fun j hj => Finset.mem_Icc.mpr (by
      have hb := metricKernelPrimitive_support p hp m hm j hj
      constructor <;> omega))
  obtain ⟨h0, hn, hp0⟩ := metricKernelPrimitive_slots p hp m hm
  rw [metricKernelPrimitive_values p hp m hm, h0, hn, hp0, mul_zero, add_zero] at hs
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : ZMod p) ≠ 0 := by
    rw [show (8 : ZMod p) = 2 * 4 by norm_num]
    exact mul_ne_zero
      (WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))) h4
  linear_combination (norm := (field_simp [h3, h4, h8]; ring)) hs

/-- Integration by parts keeps the complete metric phase, without an assigned origin value. -/
theorem metric_original_KB_pair (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) :
    (-m.toLaurent * (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ))) *
      D (literalKB (K := ZMod p) p)).coeff (-1) =
        (47 / 18 : ZMod p) * m.eval (1 / 4) - (103 / 36 : ZMod p) * m.eval 4 +
          m.coeff 0 / 4 := by
  let U := metricKernelPrimitive p m
  have he : -m.toLaurent * (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ))) *
      D (literalKB (K := ZMod p) p) = -U * D (literalKB p) := by
    simp only [U, metricKernelPrimitive, map_mul, Polynomial.toLaurent_C, map_neg, neg_div]
    ring
  have hz : (D (literalKB (K := ZMod p) p * U)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hz
  have hi : (-U * D (literalKB p)).coeff (-1) = (literalKB p * D U).coeff (-1) := by
    have hc : -U * D (literalKB p) = -(D (literalKB p) * U) := by ring
    rw [hc, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    linear_combination -hz
  rw [he, hi]
  exact metric_original_kernel_slot p hp m hm

end WPFieldAssembly.ActualBpairContraction
