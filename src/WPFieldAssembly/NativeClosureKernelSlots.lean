import WPFieldAssembly.ActualBpairFiniteKernel

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPActualCanonicalFinitePart WPCartierPoleProjection
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- The original end functional, before removing its three invisible slots. -/
noncomputable def originalKernelValue (p : ℕ) [Fact p.Prime]
    (U : (ZMod p)[T;T⁻¹]) : ZMod p :=
  (29 / 6 : ZMod p) * valueAt p U (1 / 4) -
    (23 / 6 : ZMod p) * valueAt p U 4 +
    2 * (-2 * negativeValue p U (1 / 4) - negativeValue p U 4)

theorem originalKernelValue_expansion (p : ℕ) [Fact p.Prime]
    (U : (ZMod p)[T;T⁻¹]) :
    originalKernelValue p U = ∑ j ∈ U.coeff.support, U.coeff j * bWeight p j := by
  classical
  simp only [originalKernelValue, valueAt_linear, negativeValue_linear,
    coefficientValue_expansion, if_true, bWeight, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- These are the actual weights of the omitted 0, -p and p coefficients. -/
theorem bWeight_invisible_slots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    bWeight p 0 = 1 ∧ bWeight p (-(p : ℤ)) = 15 / 8 ∧
      bWeight p (p : ℤ) = -113 / 8 := by
  have h2 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1; norm_num
  have h6 : (6 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h3 using 1; norm_num
  have h8 : (8 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1; norm_num
  simp only [bWeight, zpow_neg, zpow_natCast, ZMod.pow_card,
    zpow_zero, one_div, inv_inv, show ¬ (0 : ℤ) < 0 by omega,
    show -(p : ℤ) < 0 by omega, show ¬ (p : ℤ) < 0 by omega,
    if_true, if_false]
  constructor
  · field_simp [h6]
    ring
  constructor <;> field_simp [h4, h6, h8] <;> ring

private theorem window_cast_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : -(p : ℤ) ≤ j ∧ j ≤ 2 * (p : ℤ) - 1)
    (hz : (j : ZMod p) = 0) : j = 0 ∨ j = -(p : ℤ) ∨ j = (p : ℤ) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨k, hk⟩ := hz
  have hpos : (0 : ℤ) < p := by omega
  have hklo : -1 ≤ k := by
    by_contra hh
    have hkle : k ≤ -2 := by omega
    nlinarith [hj.1]
  have hkhi : k ≤ 1 := by
    by_contra hh
    have hkge : 2 ≤ k := by omega
    nlinarith [hj.2]
  have hc : k = 0 ∨ k = -1 ∨ k = 1 := by omega
  rcases hc with hc | hc | hc <;> simp_all

private theorem bKernel_D_window_monomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (c : ZMod p)
    (hj : j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1)) :
    (bKernel p * D (LaurentPolynomial.C c * T j)).coeff (-1) =
      c * bWeight p j - (if j = 0 then c else 0) -
        (if j = -(p : ℤ) then c * (15 / 8) else 0) +
          (if j = (p : ℤ) then c * (113 / 8) else 0) := by
  obtain ⟨h0, hm, hpw⟩ := bWeight_invisible_slots p hp
  by_cases hz : (j : ZMod p) = 0
  · have hc := window_cast_zero p hp j (Finset.mem_Icc.mp hj) hz
    rcases hc with hc | hc | hc <;> subst j
    · rw [D_monomial]
      simp [h0, show ¬ (0 : ℤ) = -(p : ℤ) by omega,
        show ¬ (0 : ℤ) = (p : ℤ) by omega]
    · rw [D_monomial]
      simp [hz, hm, show ¬ -(p : ℤ) = 0 by omega,
        show ¬ -(p : ℤ) = (p : ℤ) by omega]
    · rw [D_monomial]
      simp [hpw, show p ≠ 0 by omega,
        show ¬ (p : ℤ) = -(p : ℤ) by omega]
      ring
  · have h0j : j ≠ 0 := by intro he; subst j; simp at hz
    have hmj : j ≠ -(p : ℤ) := by
      intro he
      subst j
      simp only [Int.cast_neg, Int.cast_natCast, ZMod.natCast_self, neg_zero] at hz
      exact hz trivial
    have hpj : j ≠ (p : ℤ) := by
      intro he
      subst j
      simp only [Int.cast_natCast, ZMod.natCast_self] at hz
      exact hz trivial
    rw [bKernel_D_monomial p j c hj hz, if_neg h0j, if_neg hmj, if_neg hpj]
    ring

/-- The whole original window retains the invisible coefficients as explicit corrections.
No coefficient at 0 or ±p is assumed to vanish, and no high band is truncated. -/
theorem original_kernel_derivative_with_slots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (U : (ZMod p)[T;T⁻¹])
    (hU : ∀ j ∈ U.coeff.support,
      j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1)) :
    (literalKB (K := ZMod p) p * D U).coeff (-1) =
      originalKernelValue p U - U.coeff 0 -
        (15 / 8 : ZMod p) * U.coeff (-(p : ℤ)) +
          (113 / 8 : ZMod p) * U.coeff (p : ℤ) := by
  classical
  rw [literalKB_eq_bKernel p hp, originalKernelValue_expansion]
  conv_lhs => rw [laurent_sum_basis p U]
  simp only [map_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  have he : ∀ j ∈ U.coeff.support,
      (bKernel p * D (LaurentPolynomial.C (U.coeff j) * T j)).coeff (-1) =
        U.coeff j * bWeight p j - (if j = 0 then U.coeff j else 0) -
          (if j = -(p : ℤ) then U.coeff j * (15 / 8) else 0) +
            (if j = (p : ℤ) then U.coeff j * (113 / 8) else 0) := by
    intro j hj
    exact bKernel_D_window_monomial p hp j (U.coeff j) (hU j hj)
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hc (k : ℤ) :
      (∑ j ∈ U.coeff.support, if j = k then U.coeff j else 0) = U.coeff k := by
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hk).symm
  have hcs (k : ℤ) (a : ZMod p) :
      (∑ j ∈ U.coeff.support, if j = k then U.coeff j * a else 0) = U.coeff k * a := by
    rw [show (∑ j ∈ U.coeff.support, if j = k then U.coeff j * a else 0) =
        (∑ j ∈ U.coeff.support, if j = k then U.coeff j else 0) * a by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring, hc]
  rw [hc, hcs, hcs]
  ring

end WPFieldAssembly.ActualBpairContraction
