import WPFieldAssembly.ActualBpairLowHSeriesIBP
import WPFieldAssembly.ActualBpairLowHQuadratic
import WPFieldAssembly.ActualBpairBranchSquare

open scoped Polynomial LaurentPolynomial LaurentSeries
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The original x=w^2 substitution doubles every signed exponent. -/
def lowHSquareExponent : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by simp
  map_add' a b := by ring

noncomputable def lowHSquareSource : K[T;T⁻¹] →ₐ[K] K[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainAlgHom K K lowHSquareExponent

theorem lowHSquareSource_monomial (a : K) (n : ℤ) :
    lowHSquareSource (LaurentPolynomial.C a * T n) = LaurentPolynomial.C a * T (2 * n) := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T]
  change AddMonoidAlgebra.mapDomain lowHSquareExponent (AddMonoidAlgebra.single n a) =
    AddMonoidAlgebra.single (2 * n) a
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

theorem lowHSquareSource_T (n : ℤ) : lowHSquareSource (T n : K[T;T⁻¹]) = T (2 * n) := by
  simpa only [map_one, one_mul] using lowHSquareSource_monomial (1 : K) n

theorem lowHSquareSource_C (a : K) : lowHSquareSource (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  simpa only [mul_zero, T_zero, mul_one] using lowHSquareSource_monomial a 0

/-- The literal derivative source includes the full Jacobian 2w. -/
theorem lowHSquareSource_derivative (A : K[T;T⁻¹]) :
    D (lowHSquareSource A) = LaurentPolynomial.C (2 : K) * T 1 * lowHSquareSource (D A) := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB => simp only [map_add, hA, hB, mul_add]
  | C_mul_T n a =>
    rw [lowHSquareSource_monomial, D_monomial, D_monomial, lowHSquareSource_monomial]
    rw [show LaurentPolynomial.C (2 : K) * T 1 *
        (LaurentPolynomial.C (a * (n : K)) * T (2 * (n - 1))) =
        LaurentPolynomial.C (2 * (a * (n : K))) * T (1 + 2 * (n - 1)) by
      rw [T_add]
      simp only [map_mul]
      ring]
    simp only [Int.cast_mul, Int.cast_ofNat]
    rw [show (1 : ℤ) + 2 * (n - 1) = 2 * n - 1 by ring]
    congr 1
    congr 1
    ring

theorem lowHSquareSource_density (A : K[T;T⁻¹]) :
    LaurentPolynomial.C (2 : K) * T 1 * lowHSquareSource A = lowHQuadraticPullback A := by
  induction A using LaurentPolynomial.induction_on' with
  | add A B hA hB => simp only [map_add, mul_add, hA, hB]
  | C_mul_T n a =>
    rw [lowHSquareSource_monomial, lowHQuadraticPullback_monomial]
    rw [show LaurentPolynomial.C (2 : K) * T 1 * (LaurentPolynomial.C a * T (2 * n)) =
        LaurentPolynomial.C (2 * a) * T (1 + 2 * n) by rw [map_mul, T_add]; ring]
    congr 2
    ring

/-- The original cleared Dsym source retains both reciprocal phases and all proper-end factors. -/
theorem lowH_Dsym_square_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    lowHSquareSource ((WPFiniteZSource.Abar : K[X]).toLaurent) *
      D (lowHSquareSource (Dsym p)) =
        LaurentPolynomial.C (5 : K) * T 1 *
          lowHSquareSource WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (T (-2 * (((p - 1) / 2 : ℕ) : ℤ)) - 1) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (2 : K) * (5 / 2) = 5 := by field_simp [h2]
  have hc := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h5
  simp only [map_mul, map_ofNat] at hc
  have he := congrArg lowHSquareSource (Dsym_cleared_source (K := K) p hp)
  simp only [map_mul, map_pow, map_sub, map_one, lowHSquareSource_C, lowHSquareSource_T] at he
  rw [show 2 * -(((p - 1) / 2 : ℕ) : ℤ) = -2 * (((p - 1) / 2 : ℕ) : ℤ) by ring] at he
  rw [lowHSquareSource_derivative]
  simp only [map_ofNat]
  linear_combination (2 : K[T;T⁻¹]) * T 1 * he +
    T 1 * lowHSquareSource WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (T (-2 * (((p - 1) / 2 : ℕ) : ℤ)) - 1) * hc

/-- The tame residue factor is printed on the actual whole finite source. -/
theorem lowHSquareSource_residue (A : K[T;T⁻¹]) :
    (LaurentPolynomial.C (2 : K) * T 1 * lowHSquareSource A).coeff (-1) = 2 * A.coeff (-1) := by
  rw [lowHSquareSource_density, lowHQuadraticPullback_residue]

end WPFieldAssembly.ActualBpairContraction
