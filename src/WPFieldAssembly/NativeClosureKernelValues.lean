import WPFieldAssembly.NativeClosureKernelSlots

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPActualCanonicalFinitePart WPCartierPoleProjection
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

theorem kernel_valueAt_add (p : ℕ) [Fact p.Prime]
    (U V : (ZMod p)[T;T⁻¹]) (a : ZMod p) :
    valueAt p (U + V) a = valueAt p U a + valueAt p V a := by
  simp only [valueAt_linear, map_add]

theorem kernel_negativeValue_add (p : ℕ) [Fact p.Prime]
    (U V : (ZMod p)[T;T⁻¹]) (a : ZMod p) :
    negativeValue p (U + V) a = negativeValue p U a + negativeValue p V a := by
  simp only [negativeValue_linear, map_add]

theorem kernel_valueAt_ev (p : ℕ) [Fact p.Prime]
    (U : (ZMod p)[T;T⁻¹]) (a : ZMod p) (ha : a ≠ 0) :
    valueAt p U a = ev a ha U := by
  induction U using LaurentPolynomial.induction_on' with
  | add U V hU hV =>
    rw [valueAt_linear] at hU hV
    simp only [valueAt_linear, map_add]
    rw [hU, hV]
  | C_mul_T n c =>
    rw [valueAt_linear, coefficientValue_monomial, if_pos trivial]
    simp [ev, LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]

theorem kernel_valueAt_shifted_polynomial (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[X]) (s : ℤ) (a : ZMod p) (ha : a ≠ 0) :
    valueAt p (T s * P.toLaurent) a = a ^ s * P.eval a := by
  rw [kernel_valueAt_ev p _ a ha, map_mul]
  have ht : ev a ha (T s : (ZMod p)[T;T⁻¹]) = a ^ s := by
    simp [ev, Units.val_zpow_eq_zpow_val]
  rw [ht]
  simp [ev, LaurentPolynomial.eval₂_toLaurent]

theorem kernel_negativeValue_polynomial (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[X]) (a : ZMod p) : negativeValue p P.toLaurent a = 0 := by
  classical
  rw [negativeValue_linear, coefficientValue_expansion]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hn : j < 0
  · rw [if_pos hn, WPFiniteJCarrier.toLaurent_coeff_outside P j (Or.inl hn), zero_mul]
  · rw [if_neg hn]

theorem kernel_negativeValue_negative_phase (p : ℕ) [Fact p.Prime]
    (P : (ZMod p)[X]) (hP : P.natDegree < p) (a : ZMod p) :
    negativeValue p (T (-(p : ℤ)) * P.toLaurent) a =
      valueAt p (T (-(p : ℤ)) * P.toLaurent) a := by
  classical
  rw [negativeValue_linear, valueAt_linear, coefficientValue_expansion,
    coefficientValue_expansion]
  apply Finset.sum_congr rfl
  intro j hj
  have hjneg : j < 0 := by
    by_contra hn
    have hs := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (-(p : ℤ)) j P.toLaurent
    simp only [map_one, one_mul] at hs
    have hz := WPFiniteJCarrier.toLaurent_coeff_outside P (j - -(p : ℤ))
      (Or.inr (by omega))
    have hne := Finsupp.mem_support_iff.mp hj
    rw [hs, hz] at hne
    exact hne rfl
  rw [if_pos hjneg, if_pos trivial]

end WPFieldAssembly.ActualBpairContraction

