import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1000000

/-- The whole x=w^2 differential pullback, including its tame Jacobian 2w. -/
noncomputable def lowHQuadraticPullback : K[T;T⁻¹] →ₗ[K] K[T;T⁻¹] :=
  (Finsupp.linearCombination K (fun n : ℤ => LaurentPolynomial.C (2 : K) * T (2 * n + 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem lowHQuadraticPullback_monomial (a : K) (n : ℤ) :
    lowHQuadraticPullback (LaurentPolynomial.C a * T n) =
      LaurentPolynomial.C (2 * a) * T (2 * n + 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination K _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  congr 2
  ring

private theorem lowH_quadratic_monomial_coeff (a : K) (n j : ℤ) :
    (LaurentPolynomial.C a * T n).coeff j = if n = j then a else 0 := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_apply

/-- Every original integer exponent is retained; each ramified branch has factor two. -/
theorem lowHQuadraticPullback_residue (P : K[T;T⁻¹]) :
    (lowHQuadraticPullback P).coeff (-1) = 2 * P.coeff (-1) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
    ring
  | C_mul_T n a =>
    rw [lowHQuadraticPullback_monomial, lowH_quadratic_monomial_coeff, lowH_quadratic_monomial_coeff]
    by_cases hn : n = -1
    · rw [if_pos hn, if_pos (by omega : 2 * n + 1 = -1)]
    · rw [if_neg hn, if_neg (by omega : 2 * n + 1 ≠ -1), mul_zero]

theorem lowHQuadraticPullback_zero_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[T;T⁻¹]) :
    (lowHQuadraticPullback P).coeff (-1) = 0 ↔ P.coeff (-1) = 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  rw [lowHQuadraticPullback_residue]
  exact mul_eq_zero.trans (by simp only [h2, false_or])

theorem lowH_positive_square_jacobian : ((X : K[X]) ^ 2).derivative = Polynomial.C 2 * X := by
  exact derivative_X_sq

theorem lowH_negative_square_jacobian : ((-(X : K[X])) ^ 2).derivative = Polynomial.C 2 * X := by
  rw [neg_sq]
  exact derivative_X_sq

/-- Every signed Frobenius phase is excluded using the original full polynomial degree. -/
theorem lowH_subp_frobenius_phase_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (S : K[X]) (hS : S.natDegree < p - 1) (n : ℤ) :
    (T (n * (p : ℤ)) * S.toLaurent).coeff (-1) = 0 := by
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (n * (p : ℤ)) (-1) S.toLaurent
  simp only [map_one, one_mul] at he
  rw [he]
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hn : 0 ≤ n
  · apply WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl _)
    nlinarith
  · have hs : Above S.toLaurent ((p : ℤ) - 2) := by
      have he := Above_toLaurent S (p - 2) (by omega)
      simpa only [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat] using he
    exact hs _ (by nlinarith)

end WPFieldAssembly.ActualBpairContraction
