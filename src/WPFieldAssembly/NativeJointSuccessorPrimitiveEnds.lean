import WPFieldAssembly.NativeJointSuccessorMixedPrimitive

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorPrimitiveEnds

open ActualBpairContraction ActualSimplePoleResidue
open NativeJointSuccessorMixedPrimitive

variable {K : Type*} [Field K]
set_option maxHeartbeats 1600000

/-- The full reciprocal polynomial contributes its two actual proper endpoints. -/
theorem polynomial_inverse_origin (P : K[X]) :
    originPole (invert P.toLaurent) = (P.eval (1 / 4) - P.eval 4) / 15 := by
  rw [originPole_trunc_inverse, involutive_invert, trunc_toLaurent]

/-- The normalization coefficient cancels, and all six negative ordered H rows remain. -/
theorem actual_calL_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole (calL p : K[T;T⁻¹]) =
      -(2 / 225 : K) *
        (2 * branchH p 4 (1 / 4) + branchH p (1 / 4) (1 / 4) -
          3 * branchH p 0 (1 / 4) - 2 * branchH p 4 4 -
          branchH p (1 / 4) 4 + 3 * branchH p 0 4) := by
  have hC (c : K) : originPole (LaurentPolynomial.C c) = 0 := by
    simpa only [Polynomial.toLaurent_C] using originPole_polynomial (Polynomial.C c)
  rw [calL, originPole_sub, hC, sub_zero, calLUnnormalized,
    originPole_add, originPole_polynomial, zero_add, calLNegative,
    ← map_neg (LaurentPolynomial.C : K →+* K[T;T⁻¹]),
    originPole_C_mul, originPole_sub, originPole_add]
  have h2 (F : K[T;T⁻¹]) : originPole (2 * F) = 2 * originPole F := by
    simpa only [map_ofNat] using originPole_C_mul (2 : K) F
  have h3 (F : K[T;T⁻¹]) : originPole (3 * F) = 3 * originPole F := by
    simpa only [map_ofNat] using originPole_C_mul (3 : K) F
  rw [h2, h3, polynomial_inverse_origin, polynomial_inverse_origin,
    polynomial_inverse_origin, branchHPolynomial_eval, branchHPolynomial_eval,
    branchHPolynomial_eval, branchHPolynomial_eval, branchHPolynomial_eval,
    branchHPolynomial_eval]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  field_simp [h15, h225]
  ring

/-- The same reciprocal primitive keeps all four positive H rows and both even endpoints. -/
theorem actual_calL_inverse_origin (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole (invert (calL p : K[T;T⁻¹])) =
      -(2 / 225 : K) *
        (2 * branchH p (1 / 4) (1 / 4) + branchH p 4 (1 / 4) -
          2 * branchH p (1 / 4) 4 - branchH p 4 4) -
      (4 * WPFiniteNC122.h p / 225) *
        ((originalEven p : K[X]).eval (1 / 4) - (originalEven p).eval 4) := by
  have hC (c : K) : originPole (LaurentPolynomial.C c) = 0 := by
    simpa only [Polynomial.toLaurent_C] using originPole_polynomial (Polynomial.C c)
  have hnegative : originPole (invert (calLNegative p : K[T;T⁻¹])) = 0 := by
    have hn : invert (calLNegative p : K[T;T⁻¹]) =
        (-Polynomial.C (2 / 15 : K) *
          (2 * branchHPolynomial p 4 + branchHPolynomial p (1 / 4) -
            3 * branchHPolynomial p 0)).toLaurent := by
      simp only [calLNegative, map_mul, map_sub, map_add, map_neg, invert_C,
        map_ofNat, Polynomial.toLaurent_C]
      rw [involutive_invert, involutive_invert, involutive_invert]
    rw [hn, originPole_polynomial]
  rw [calL, map_sub, invert_C, originPole_sub, hC, sub_zero,
    calLUnnormalized, map_add, originPole_add, hnegative, add_zero,
    polynomial_inverse_origin]
  simp only [calLPositive, eval_sub, eval_mul, eval_add, eval_neg, eval_C, eval_ofNat,
    branchHPolynomial_eval]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  field_simp [h15, h225]
  ring

end WPFieldAssembly.NativeJointSuccessorPrimitiveEnds
