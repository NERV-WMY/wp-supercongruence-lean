import WPFieldAssembly.NativeScalarRows

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.GreenLaurentOperators WPFiniteLaurentDifferential
  WPActualNativeCanonicalPart WPActualCanonicalFinitePart WPCartierPoleProjection
namespace WPFieldAssembly.ActualBpairContraction

noncomputable def bWeight (p : ℕ) [Fact p.Prime] (j : ℤ) : ZMod p :=
  (29 / 6 : ZMod p) * (1 / 4 : ZMod p) ^ j -
  (23 / 6 : ZMod p) * (4 : ZMod p) ^ j +
  2 * (if j < 0 then -2 * (1 / 4 : ZMod p) ^ j - (4 : ZMod p) ^ j else 0)

noncomputable def bKernel (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  ∑ j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1),
    LaurentPolynomial.C (bWeight p j / (j : ZMod p)) * T (-j)

theorem bKernel_coeff_neg (p : ℕ) [Fact p.Prime] (j : ℤ) :
    (bKernel p).coeff (-j) =
      if j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1)
      then bWeight p j / (j : ZMod p) else 0 := by
  classical
  rw [bKernel, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases hj : j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1)
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [cm_coeff, if_pos rfl]
    · intro i hi hij
      rw [cm_coeff, if_neg (by omega : -i ≠ -j)]
    · intro hn
      exact False.elim (hn hj)
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := by intro he; subst i; exact hj hi
    rw [cm_coeff, if_neg (by omega : -i ≠ -j)]

theorem bKernel_zero (p : ℕ) [Fact p.Prime] : (bKernel p).coeff 0 = 0 := by
  have h := bKernel_coeff_neg p 0
  simpa only [neg_zero, Int.cast_zero, div_zero, ite_self] using h

theorem bKernel_D_monomial (p : ℕ) [Fact p.Prime] (j : ℤ) (c : ZMod p)
    (hj : j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1))
    (hunit : (j : ZMod p) ≠ 0) :
    (bKernel p * D (LaurentPolynomial.C c * T j)).coeff (-1) =
      c * bWeight p j := by
  rw [D_monomial]
  have hc : bKernel p * (LaurentPolynomial.C (c * (j : ZMod p)) * T (j - 1)) =
      LaurentPolynomial.C (c * (j : ZMod p)) * T (j - 1) * bKernel p := by ring
  rw [hc, shift_coeff, show (-1 : ℤ) - (j - 1) = -j by omega,
    bKernel_coeff_neg, if_pos hj]
  field_simp [hunit]

theorem laurent_sum_basis (p : ℕ) (U : (ZMod p)[T;T⁻¹]) :
    U = ∑ j ∈ U.coeff.support, LaurentPolynomial.C (U.coeff j) * T j := by
  classical
  ext k
  simp_rw [← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply', Finset.sum_eq_single k]
  · rw [single_eq_C_mul_T,cm_coeff,if_pos rfl]
  · intro j hj hjk
    change Finsupp.single j (U.coeff j) k=0
    exact Finsupp.single_eq_of_ne' hjk
  · intro hk
    rw [single_eq_C_mul_T,cm_coeff,if_pos rfl]
    exact Finsupp.notMem_support_iff.mp hk

theorem actual_bpair_expansion (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    NativeScalarRows.nativeBpair p hp =
      ∑ j ∈ (nativeRemainder p hp).coeff.support,
        (nativeRemainder p hp).coeff j * bWeight p j := by
  classical
  simp only [NativeScalarRows.nativeBpair, valueAt_linear, negativeValue_linear,
    coefficientValue_expansion, if_true, bWeight,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

theorem actual_bpair_IR53 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    NativeScalarRows.nativeBpair p hp =
      (bKernel p * D (nativeRemainder p hp)).coeff (-1) := by
  classical
  let U := nativeRemainder p hp
  rw [actual_bpair_expansion]
  change (∑ j ∈ U.coeff.support, U.coeff j * bWeight p j) =
    (bKernel p * D U).coeff (-1)
  calc
    _ = ∑ j ∈ U.coeff.support,
        (bKernel p * D (LaurentPolynomial.C (U.coeff j) * T j)).coeff (-1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hne : U.coeff j ≠ 0 := Finsupp.mem_support_iff.mp hj
      have hs := WPActualNativeRemainderSource.actual_native_remainder_support p hp j hne
      have hband : j ∈ Finset.Icc (-(p : ℤ)) (2 * (p : ℤ) - 1) :=
        Finset.mem_Icc.mpr (by omega)
      have hu : (j : ZMod p) ≠ 0 := by
        intro hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        obtain ⟨k, hk⟩ := hz
        have he : j = k * (p : ℤ) := by rw [hk]; ring
        rw [he] at hne
        exact hne (actual_native_remainder_resonant_zero p hp k)
      exact (bKernel_D_monomial p j (U.coeff j) hband hu).symm
    _ = (bKernel p * D (∑ j ∈ U.coeff.support,
        LaurentPolynomial.C (U.coeff j) * T j)).coeff (-1) := by
      simp only [map_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum,
        Finsupp.finsetSum_apply]
    _ = _ := by rw [← laurent_sum_basis p U]

end WPFieldAssembly.ActualBpairContraction
