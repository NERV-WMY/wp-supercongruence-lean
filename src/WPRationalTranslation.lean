import WPActualSourceCoefficients
import Mathlib.Algebra.Polynomial.Taylor

open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1000000

/-- Ordinary translation of the literal polynomial coefficient variable. -/
def rationalTranslationPolynomialHom (c : ℚ) : ℚ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.taylorAlgHom c).toRingHom

theorem rational_translation_polynomial_injective (c : ℚ) :
    Function.Injective (rationalTranslationPolynomialHom c) := by
  intro P Q h
  apply Polynomial.taylor_injective c
  apply RatFunc.algebraMap_injective
  exact h

/-- Translation is lifted from ordinary polynomial numerator and denominator quotients. -/
def rationalTranslationHom (c : ℚ) : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom (rationalTranslationPolynomialHom c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (rational_translation_polynomial_injective c))

theorem rational_translation_polynomial (c : ℚ) (P : ℚ[X]) :
    rationalTranslationHom c (algebraMap ℚ[X] (RatFunc ℚ) P) =
      algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.taylor c P) := by
  rw [rationalTranslationHom, RatFunc.liftRingHom_algebraMap]
  rfl

theorem rational_translation_fraction (c : ℚ) (P Q : ℚ[X]) :
    rationalTranslationHom c (algebraMap ℚ[X] (RatFunc ℚ) P/
        algebraMap ℚ[X] (RatFunc ℚ) Q) =
      algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.taylor c P)/
        algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.taylor c Q) := by
  rw [map_div₀, rational_translation_polynomial, rational_translation_polynomial]

theorem rational_translation_scalar (c q : ℚ) :
    rationalTranslationHom c (RatFunc.C q) = RatFunc.C q := by
  rw [← RatFunc.algebraMap_C, rational_translation_polynomial,
    Polynomial.taylor_C, RatFunc.algebraMap_C]

theorem rational_translation_symbol (c : ℚ) :
    rationalTranslationHom c symbol = symbol+RatFunc.C c := by
  rw [symbol, rational_translation_polynomial, Polynomial.taylor_X]
  simp only [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem derivative_taylor_polynomial (c : ℚ) (P : ℚ[X]) :
    derivative (Polynomial.taylor c P) = Polynomial.taylor c (derivative P) := by
  simp only [Polynomial.taylor_apply, derivative_comp, derivative_add,
    derivative_X, derivative_C, add_zero, one_mul]

/-- Literal reduced rational differentiation commutes with ordinary coordinate translation. -/
theorem rational_translation_derivative (c : ℚ) (f : RatFunc ℚ) :
    rationalTranslationHom c (rationalDerivative f) =
      rationalDerivative (rationalTranslationHom c f) := by
  refine RatFunc.induction_on (P := fun f =>
    rationalTranslationHom c (rationalDerivative f) =
      rationalDerivative (rationalTranslationHom c f)) f ?_
  intro P Q hQ
  have htQ : Polynomial.taylor c Q ≠ 0 := by
    intro hz
    apply hQ
    apply Polynomial.taylor_injective c
    simpa only [map_zero] using hz
  rw [rationalDerivative_fraction P Q hQ, rational_translation_fraction c P Q,
    rationalDerivative_fraction _ _ htQ]
  simp only [map_div₀, map_pow, rational_translation_polynomial,
    map_sub, map_mul,
    derivative_taylor_polynomial]

end

end WPForcedSourceStokes
