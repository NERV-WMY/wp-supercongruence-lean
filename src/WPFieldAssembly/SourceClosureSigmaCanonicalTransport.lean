import WPFieldAssembly.SourceClosureSigmaProperJ
import WPActualEtaIntegrality

open scoped LaurentPolynomial
open LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPFieldAssembly.SourceClosureSigmaProperJ

namespace WPFieldAssembly.SourceClosureSigmaCanonicalTransport

set_option maxHeartbeats 1500000

/- The whole logarithmic source also has positive pivots above p.
Their genuine unit inverses are transported; the small unit-band helper
is intentionally not used outside its declared interval. -/

noncomputable def nonresonantInverseI (p : ℕ) [Fact p.Prime] (j : ℤ) :
    integralRationals p :=
  if h : (p : ℤ) ∣ j then 0 else
    ⟨(j : ℚ)⁻¹, by
      change 0 ≤ padicValRat p (j : ℚ)⁻¹
      rw [padicValRat.inv, WPPIntegralReduction.integer_denominator_unit p j h]
      simp⟩

noncomputable def nonresonantInverse {K : Type*} [Field K] (p : ℕ) (j : ℤ) : K :=
  if (p : ℤ) ∣ j then 0 else (j : K)⁻¹

theorem nonresonantInverseI_value (p : ℕ) [Fact p.Prime] (j : ℤ) :
    (integralRationals p).subtype (nonresonantInverseI p j) =
      nonresonantInverse (K := ℚ) p j := by
  unfold nonresonantInverseI nonresonantInverse
  split_ifs <;> rfl

theorem nonresonantInverseI_field (p : ℕ) [Fact p.Prime] (j : ℤ) :
    residueHom p (nonresonantInverseI p j) =
      nonresonantInverse (K := ZMod p) p j := by
  by_cases hj : (p : ℤ) ∣ j
  · simp only [nonresonantInverseI, nonresonantInverse, dif_pos hj, if_pos hj, _root_.map_zero]
  · have hj0 : j ≠ 0 := by intro hz; exact hj (hz ▸ dvd_zero _)
    have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
    have hi : (j : integralRationals p) * nonresonantInverseI p j = 1 := by
      apply Subtype.ext
      change (j : ℚ) * (integralRationals p).subtype (nonresonantInverseI p j) = 1
      rw [nonresonantInverseI_value, nonresonantInverse, if_neg hj, mul_inv_cancel₀ hjq]
    have hf := congrArg (residueHom p) hi
    simp only [_root_.map_mul, _root_.map_intCast, _root_.map_one] at hf
    rw [nonresonantInverse, if_neg hj]
    exact eq_inv_of_mul_eq_one_left
      ((mul_comm (residueHom p (nonresonantInverseI p j)) (j : ZMod p)).trans hf)

noncomputable def nonresonantPrimitiveI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] →ₗ[integralRationals p] (integralRationals p)[T;T⁻¹] :=
  primitiveWith (nonresonantInverseI p)

noncomputable def nonresonantPrimitiveField (p : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] (ZMod p)[T;T⁻¹] :=
  primitiveWith (nonresonantInverse (K := ZMod p) p)

/-- The existing rational canonical primitive is transported coefficientwise in full support. -/
theorem nonresonantPrimitiveI_value (p : ℕ) [Fact p.Prime]
    (F : (integralRationals p)[T;T⁻¹]) :
    coefficientMap (integralRationals p).subtype (nonresonantPrimitiveI p F) =
      WPActualEtaPrimitive.canonicalPrimitive p
        (coefficientMap (integralRationals p).subtype F) := by
  rw [nonresonantPrimitiveI, primitiveWith_map _ _ _ (nonresonantInverseI_value p)]
  ext j
  rw [primitiveWith_coeff, WPActualEtaPrimitive.canonicalPrimitive_coeff]
  by_cases hj : (p : ℤ) ∣ j
  · simp only [nonresonantInverse, if_pos hj, zero_mul]
  · simp only [nonresonantInverse, if_neg hj, div_eq_mul_inv]
    ring

/-- Every surviving signed pivot is reduced after genuine integral inversion. -/
theorem nonresonantPrimitiveI_field (p : ℕ) [Fact p.Prime]
    (F : (integralRationals p)[T;T⁻¹]) :
    coefficientMap (residueHom p) (nonresonantPrimitiveI p F) =
      nonresonantPrimitiveField p (coefficientMap (residueHom p) F) := by
  rw [nonresonantPrimitiveI, primitiveWith_map _ _ _ (nonresonantInverseI_field p)]
  rfl

end WPFieldAssembly.SourceClosureSigmaCanonicalTransport
