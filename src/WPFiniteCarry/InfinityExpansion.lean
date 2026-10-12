/- Owned continuation of the retained source-only WPRationalInfinityExpansion.lean.
   Canonical WPForcedSourceStokes names and statements are preserved;
   elaboration repairs are confined to this owned copy. -/
import WPRationalPolynomialPart
import Mathlib.RingTheory.LaurentSeries

open scoped LaurentSeries
open Polynomial HahnSeries

namespace WPForcedSourceStokes

noncomputable section

/-- Literal evaluation of x at z inverse in formal Laurent series. -/
noncomputable def infinityPolynomialHom : ℚ[X] →+* LaurentSeries ℚ :=
  (aeval (single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ)).toRingHom

theorem infinity_polynomial_monomial (n : ℕ) (a : ℚ) :
    infinityPolynomialHom (monomial n a) = single (-(n : ℤ)) a := by
  change aeval (single (-1 : ℤ) (1 : ℚ) : LaurentSeries ℚ) (monomial n a) = _
  rw [aeval_monomial, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    single_pow, single_mul_single]
  simp

theorem infinity_polynomial_coeff (P : ℚ[X]) (n : ℕ) :
    (infinityPolynomialHom P).coeff (-(n : ℤ)) = P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, HahnSeries.coeff_add, Polynomial.coeff_add, hP, hQ]
  | monomial k a =>
    rw [infinity_polynomial_monomial]
    simp [coeff_single, Polynomial.coeff_monomial, eq_comm]

theorem infinity_polynomial_positive_coeff (P : ℚ[X]) (j : ℤ) (hj : 0 < j) :
    (infinityPolynomialHom P).coeff j = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, HahnSeries.coeff_add, hP, hQ, add_zero]
  | monomial k a =>
    rw [infinity_polynomial_monomial]
    exact coeff_single_of_ne (by omega)

theorem infinity_polynomial_injective : Function.Injective infinityPolynomialHom := by
  intro P Q h
  ext n
  rw [← infinity_polynomial_coeff P n, ← infinity_polynomial_coeff Q n, h]

theorem infinity_polynomial_nonzero (P : ℚ[X]) (hP : P ≠ 0) :
    infinityPolynomialHom P ≠ 0 := by
  intro h
  apply hP
  apply infinity_polynomial_injective
  simpa using h

theorem infinity_polynomial_order (P : ℚ[X]) (hP : P ≠ 0) :
    (infinityPolynomialHom P).order = -(P.natDegree : ℤ) := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    rw [infinity_polynomial_coeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  · apply (le_order_iff_forall (infinity_polynomial_nonzero P hP)).mpr
    intro j hj
    let n : ℕ := (-j).toNat
    have hjn : j = -(n : ℤ) := by dsimp [n]; omega
    rw [hjn, infinity_polynomial_coeff]
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [n]
    omega

noncomputable def rationalInfinityHom : RatFunc ℚ →+* LaurentSeries ℚ :=
  RatFunc.liftRingHom infinityPolynomialHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ infinity_polynomial_injective)

theorem rational_infinity_polynomial (P : ℚ[X]) :
    rationalInfinityHom (algebraMap ℚ[X] (RatFunc ℚ) P) = infinityPolynomialHom P := by
  exact RatFunc.liftRingHom_algebraMap _ _ P

theorem rational_infinity_fraction (P Q : ℚ[X]) :
    rationalInfinityHom (algebraMap ℚ[X] (RatFunc ℚ) P /
      algebraMap ℚ[X] (RatFunc ℚ) Q) = infinityPolynomialHom P / infinityPolynomialHom Q := by
  exact RatFunc.liftRingHom_apply_div _ _ P Q

theorem laurent_inverse_order (G : LaurentSeries ℚ) (hG : G ≠ 0) :
    (G⁻¹).order = -G.order := by
  have h := order_mul_of_ne_zero (mul_ne_zero
    (HahnSeries.leadingCoeff_ne_zero.mpr hG)
    (HahnSeries.leadingCoeff_ne_zero.mpr (inv_ne_zero hG)))
  rw [mul_inv_cancel₀ hG, order_one] at h
  omega

theorem laurent_fraction_order (F G : LaurentSeries ℚ) (hF : F ≠ 0) (hG : G ≠ 0) :
    (F/G).order = F.order - G.order := by
  rw [div_eq_mul_inv, order_mul_of_ne_zero (mul_ne_zero
    (HahnSeries.leadingCoeff_ne_zero.mpr hF)
    (HahnSeries.leadingCoeff_ne_zero.mpr (inv_ne_zero hG))),
    laurent_inverse_order G hG, sub_eq_add_neg]

theorem rational_infinity_proper_coeff_zero (R Q : ℚ[X]) (hQ : Q ≠ 0)
    (hproper : R.degree < Q.degree) (k : ℕ) :
    (rationalInfinityHom (algebraMap ℚ[X] (RatFunc ℚ) R /
      algebraMap ℚ[X] (RatFunc ℚ) Q)).coeff (-(k : ℤ)) = 0 := by
  rw [rational_infinity_fraction]
  by_cases hR : R = 0
  · simp [hR]
  · apply coeff_eq_zero_of_lt_order
    rw [laurent_fraction_order _ _ (infinity_polynomial_nonzero R hR)
      (infinity_polynomial_nonzero Q hQ), infinity_polynomial_order R hR,
      infinity_polynomial_order Q hQ]
    rw [degree_eq_natDegree hR, degree_eq_natDegree hQ] at hproper
    have hn : R.natDegree < Q.natDegree := by exact_mod_cast hproper
    omega

/-- The honest infinity expansion recovers exactly the actual ordinary polynomial quotient. -/
theorem rational_infinity_polynomialPart_coeff (f : RatFunc ℚ) (k : ℕ) :
    (rationalInfinityHom f).coeff (-(k : ℤ)) = (rationalPolynomialPart f).coeff k := by
  have hf := rationalPolynomialPart_decomposition f
  have he := congrArg rationalInfinityHom hf.1
  rw [map_add, rational_infinity_polynomial] at he
  rw [he, HahnSeries.coeff_add, infinity_polynomial_coeff,
    rational_infinity_proper_coeff_zero _ _ (RatFunc.denom_ne_zero f) hf.2 k, add_zero]

end

end WPForcedSourceStokes
