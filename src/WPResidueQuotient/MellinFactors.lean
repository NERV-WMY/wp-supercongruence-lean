import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# The actual all-integer Mellin factors

The factors are finite products in `RatFunc ℚ`. Negative indices use
reciprocals of finite products; no Gamma function or assumed functional
occurs. `integerProduct_succ` proves the recurrence across every integer,
including the transition from -1 to 0. The six-factor coefficient identities
below are the algebraic pole and exact-derivative cancellations, before any
canonicalization or truncation.
-/

noncomputable section

namespace WPResidueQuotient
namespace MellinFactors

open scoped BigOperators

abbrev RF := RatFunc ℚ

/-- The independent rational-function variable. -/
def rho : RF := RatFunc.X

/-- The linear factor `j + q rho`. -/
def linearFactor (q : ℚ) (j : ℤ) : RF :=
  (j : RF) + (q : RF) * rho

theorem linearFactor_image (q : ℚ) (j : ℤ) :
    linearFactor q j =
      algebraMap (Polynomial ℚ) RF
        (Polynomial.C (j : ℚ) + Polynomial.C q * Polynomial.X) := by
  simp only [linearFactor, rho, map_add, map_mul, RatFunc.algebraMap_C,
    RatFunc.algebraMap_X, eq_ratCast, Rat.cast_intCast]

/-- A nonconstant linear polynomial stays nonzero in its fraction field. -/
theorem linearFactor_ne_zero (q : ℚ) (hq : q ≠ 0) (j : ℤ) :
    linearFactor q j ≠ 0 := by
  rw [linearFactor_image]
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  have : q = 0 := by
    simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_zero, one_ne_zero, if_false, if_true,
      zero_add, mul_one] using hc
  exact hq this

/-- The positive product and reciprocal negative product centered at index 0.

For `l = -n-1`, the factors in the reciprocal are
`q rho, -1 + q rho, ..., -n + q rho`. This is the same product as the
increasing interval `l+1,...,0`, written in reverse order.
-/
def integerProduct (q : ℚ) : ℤ → RF
  | .ofNat n => ∏ j ∈ Finset.range n, linearFactor q ((j : ℤ) + 1)
  | .negSucc n => (∏ j ∈ Finset.range (n + 1), linearFactor q (-(j : ℤ)))⁻¹

@[simp] theorem integerProduct_zero (q : ℚ) : integerProduct q 0 = 1 := by
  simp [integerProduct]

theorem integerProduct_nat (q : ℚ) (n : ℕ) :
    integerProduct q (n : ℤ) =
      ∏ j ∈ Finset.range n, linearFactor q ((j : ℤ) + 1) := rfl

theorem integerProduct_negSucc (q : ℚ) (n : ℕ) :
    integerProduct q (Int.negSucc n) =
      (∏ j ∈ Finset.range (n + 1), linearFactor q (-(j : ℤ)))⁻¹ := rfl

/-- The finite-product recurrence holds at every integer, not only positive
indices. The negative constructor branch supplies the lower endpoint. -/
theorem integerProduct_succ (q : ℚ) (hq : q ≠ 0) (l : ℤ) :
    integerProduct q (l + 1) =
      linearFactor q (l + 1) * integerProduct q l := by
  cases l with
  | ofNat n =>
      change (∏ j ∈ Finset.range (n + 1), linearFactor q ((j : ℤ) + 1)) =
        linearFactor q ((n : ℤ) + 1) *
          (∏ j ∈ Finset.range n, linearFactor q ((j : ℤ) + 1))
      rw [Finset.prod_range_succ, mul_comm]
  | negSucc n =>
      cases n with
      | zero =>
          simpa [integerProduct] using
            (mul_inv_cancel₀ (linearFactor_ne_zero q hq 0)).symm
      | succ n =>
          have hindex : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
          rw [hindex]
          change (∏ j ∈ Finset.range (n + 1), linearFactor q (-(j : ℤ)))⁻¹ =
            linearFactor q (-((n + 1 : ℕ) : ℤ)) *
              (∏ j ∈ Finset.range (n + 2), linearFactor q (-(j : ℤ)))⁻¹
          rw [show n + 2 = (n + 1) + 1 by omega,
            Finset.prod_range_succ (fun j => linearFactor q (-(j : ℤ))) (n + 1),
            mul_inv_rev, mul_inv_cancel_left₀
              (linearFactor_ne_zero q hq (-((n + 1 : ℕ) : ℤ)))]

theorem integerProduct_ne_zero (q : ℚ) (hq : q ≠ 0) (l : ℤ) :
    integerProduct q l ≠ 0 := by
  cases l with
  | ofNat n =>
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => linearFactor_ne_zero q hq _)
  | negSucc n =>
      apply inv_ne_zero
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => linearFactor_ne_zero q hq _)

/-- The paper's `G_k`, with index shifted by one from the centered product. -/
def G (k : ℤ) : RF := integerProduct 6 (k - 1)

/-- The paper's `H_l`. -/
def H (l : ℤ) : RF := integerProduct 1 l

theorem G_recurrence (k : ℤ) : G (k + 1) = linearFactor 6 k * G k := by
  simpa [G] using integerProduct_succ 6 (by norm_num) (k - 1)

theorem H_recurrence (l : ℤ) : H l = linearFactor 1 l * H (l - 1) := by
  simpa [H] using integerProduct_succ 1 (by norm_num) (l - 1)

theorem G_ne_zero (k : ℤ) : G k ≠ 0 :=
  integerProduct_ne_zero 6 (by norm_num) (k - 1)

theorem H_ne_zero (l : ℤ) : H l ≠ 0 :=
  integerProduct_ne_zero 1 (by norm_num) l

theorem G_positive_product (n : ℕ) :
    G ((n : ℤ) + 1) =
      ∏ j ∈ Finset.range n, linearFactor 6 ((j : ℤ) + 1) := by
  simp [G, integerProduct]

theorem G_nonpositive_product (n : ℕ) :
    G (-(n : ℤ)) =
      (∏ j ∈ Finset.range (n + 1), linearFactor 6 (-(j : ℤ)))⁻¹ := by
  have hi : -(n : ℤ) - 1 = Int.negSucc n := by omega
  rw [G, hi]
  rfl

theorem H_positive_product (n : ℕ) :
    H (n : ℤ) = ∏ j ∈ Finset.range n, linearFactor 1 ((j : ℤ) + 1) := rfl

theorem H_negative_product (n : ℕ) :
    H (Int.negSucc n) =
      (∏ j ∈ Finset.range (n + 1), linearFactor 1 (-(j : ℤ)))⁻¹ := rfl

@[simp] theorem G_one : G 1 = 1 := by simp [G]

@[simp] theorem H_zero : H 0 = 1 := by simp [H]

theorem G_zero : G 0 = (6 * rho)⁻¹ := by
  simpa [linearFactor] using G_nonpositive_product 0

theorem H_neg_one : H (-1) = rho⁻¹ := by
  have hi : (-1 : ℤ) = Int.negSucc 0 := by decide
  rw [hi, H_negative_product]
  simp [linearFactor]

/-- The inverse-H factors, which are the factors used in the Mellin
coefficient's denominator. -/
def inverseH (l : ℤ) : RF := (H l)⁻¹

theorem inverseH_ne_zero (l : ℤ) : inverseH l ≠ 0 :=
  inv_ne_zero (H_ne_zero l)

/-- Lowering an H-index multiplies its reciprocal by `l + rho`. -/
theorem inverseH_lower (l : ℤ) :
    inverseH (l - 1) = linearFactor 1 l * inverseH l := by
  unfold inverseH
  rw [H_recurrence l, mul_inv_rev]
  rw [mul_left_comm (linearFactor 1 l), mul_inv_cancel₀
    (linearFactor_ne_zero 1 (by norm_num) l), mul_one]

abbrev SixIndices := Fin 6 → ℤ

/-- The rational-function coefficient at fixed summation index. -/
def coefficient (k : ℤ) (l : SixIndices) : RF :=
  G k * ∏ i, inverseH (l i)

theorem coefficient_ne_zero (k : ℤ) (l : SixIndices) :
    coefficient k l ≠ 0 := by
  apply mul_ne_zero (G_ne_zero k)
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => inverseH_ne_zero _)

/-- Shift exactly one reciprocal-H factor, leaving the other five fixed. -/
theorem prod_inverseH_lower (l : SixIndices) (i : Fin 6) :
    (∏ j, inverseH (Function.update l i (l i - 1) j)) =
      linearFactor 1 (l i) * ∏ j, inverseH (l j) := by
  classical
  have hfun :
      (fun j => inverseH (Function.update l i (l i - 1) j)) =
        Function.update (fun j => inverseH (l j)) i (inverseH (l i - 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i), inverseH_lower,
    mul_assoc, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_univ i) (fun j => inverseH (l j))]

theorem coefficient_lower (k : ℤ) (l : SixIndices) (i : Fin 6) :
    coefficient k (Function.update l i (l i - 1)) =
      linearFactor 1 (l i) * coefficient k l := by
  unfold coefficient
  rw [prod_inverseH_lower]
  ring

theorem coefficient_succ (k : ℤ) (l : SixIndices) :
    coefficient (k + 1) l = linearFactor 6 k * coefficient k l := by
  unfold coefficient
  rw [G_recurrence]
  ring

/-- The common-denominator identity for the pole relation, valid at every
G-index and every H-index. -/
theorem coefficient_pole_identity (k : ℤ) (l : SixIndices) :
    coefficient (k + 1) l -
        ∑ i, coefficient k (Function.update l i (l i - 1)) =
      (linearFactor 6 k - ∑ i, linearFactor 1 (l i)) * coefficient k l := by
  rw [coefficient_succ]
  simp_rw [coefficient_lower]
  rw [← Finset.sum_mul]
  ring

theorem sum_linearFactor_six (l : SixIndices) :
    (∑ i, linearFactor 1 (l i)) = ((∑ i, l i : ℤ) : RF) + 6 * rho := by
  simp [linearFactor, Finset.sum_add_distrib, nsmul_eq_mul]

/-- The six rho-terms cancel, leaving the integer pole multiplier. -/
theorem coefficient_pole_integer (k : ℤ) (l : SixIndices) :
    coefficient (k + 1) l -
        ∑ i, coefficient k (Function.update l i (l i - 1)) =
      ((k - ∑ i, l i : ℤ) : RF) * coefficient k l := by
  rw [coefficient_pole_identity, sum_linearFactor_six]
  simp only [linearFactor, Int.cast_sub]
  ring

/-- The two lowered denominator factors cancel the logarithmic derivative
multiplier. This is exact in the rational-function field before truncation. -/
theorem coefficient_derivative_identity
    (k : ℤ) (l : SixIndices) (i j : Fin 6) :
    (((l j - l i : ℤ) : RF) * coefficient k l) +
        coefficient k (Function.update l i (l i - 1)) -
        coefficient k (Function.update l j (l j - 1)) = 0 := by
  rw [coefficient_lower, coefficient_lower]
  simp only [linearFactor, Int.cast_sub]
  ring

/-- The six noncanonical exponents, with no nonnegativity assumption needed
for the purely algebraic coefficient identities. -/
abbrev ExponentVector := Fin 6 → ℤ

def increment (a : ExponentVector) (i : Fin 6) : ExponentVector :=
  Function.update a i (a i + 1)

def denominatorIndices (n : ℤ) (a : ExponentVector) : SixIndices :=
  fun i => n - a i

def poleIndex (m n : ℤ) (a : ExponentVector) : ℤ :=
  m + 6 * n - ∑ i, a i

/-- The coefficient appearing in formula (3), with the u-power omitted.
That u-power is common after the displayed pole/derivative prefactor. -/
def mellinTerm (m n : ℤ) (a : ExponentVector) : RF :=
  coefficient (poleIndex m n a) (denominatorIndices n a)

theorem sum_increment (a : ExponentVector) (i : Fin 6) :
    (∑ j, increment a i j) = (∑ j, a j) + 1 := by
  classical
  unfold increment
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsum := Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (Finset.mem_univ i) a
  rw [hsum]
  ring

theorem denominatorIndices_increment (n : ℤ) (a : ExponentVector) (i : Fin 6) :
    denominatorIndices n (increment a i) =
      Function.update (denominatorIndices n a) i (denominatorIndices n a i - 1) := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [denominatorIndices, increment]
    omega
  · simp [denominatorIndices, increment, Function.update, hji]

theorem poleIndex_increment (m n : ℤ) (a : ExponentVector) (i : Fin 6) :
    poleIndex (m + 1) n (increment a i) = poleIndex m n a := by
  unfold poleIndex
  rw [sum_increment]
  ring

theorem mellinTerm_increment (m n : ℤ) (a : ExponentVector) (i : Fin 6) :
    mellinTerm (m + 1) n (increment a i) =
      coefficient (poleIndex m n a)
        (Function.update (denominatorIndices n a) i (denominatorIndices n a i - 1)) := by
  unfold mellinTerm
  rw [poleIndex_increment, denominatorIndices_increment]

theorem mellinTerm_succ (m n : ℤ) (a : ExponentVector) :
    mellinTerm (m + 1) n a =
      coefficient (poleIndex m n a + 1) (denominatorIndices n a) := by
  unfold mellinTerm poleIndex
  congr 1
  ring

theorem sum_denominatorIndices (n : ℤ) (a : ExponentVector) :
    (∑ i, denominatorIndices n a i) = 6 * n - ∑ i, a i := by
  simp [denominatorIndices, Finset.sum_sub_distrib]

theorem poleIndex_sub_sum_denominatorIndices (m n : ℤ) (a : ExponentVector) :
    poleIndex m n a - ∑ i, denominatorIndices n a i = m := by
  rw [sum_denominatorIndices]
  unfold poleIndex
  ring

/-- Formula (4) for the actual Mellin factors. Every integer index is
allowed, so the negative and lower-endpoint cases are included. -/
theorem mellinTerm_pole_relation (m n : ℤ) (a : ExponentVector) :
    mellinTerm (m + 1) n a - ∑ i, mellinTerm (m + 1) n (increment a i) =
      (m : RF) * mellinTerm m n a := by
  rw [mellinTerm_succ]
  simp_rw [mellinTerm_increment]
  rw [coefficient_pole_integer, poleIndex_sub_sum_denominatorIndices]
  rfl

/-- Exact logarithmic derivative cancellation, with the actual exponent
multiplier `a_i-a_j`. No functional is postulated as a premise. -/
theorem mellinTerm_derivative_relation
    (m n : ℤ) (a : ExponentVector) (i j : Fin 6) :
    (((a i - a j : ℤ) : RF) * mellinTerm m n a) +
        mellinTerm (m + 1) n (increment a i) -
        mellinTerm (m + 1) n (increment a j) = 0 := by
  rw [mellinTerm_increment, mellinTerm_increment]
  unfold mellinTerm
  have hd := coefficient_derivative_identity (poleIndex m n a)
    (denominatorIndices n a) i j
  have hi : denominatorIndices n a j - denominatorIndices n a i = a i - a j := by
    unfold denominatorIndices
    ring
  rw [hi] at hd
  exact hd

/-- The polynomial whose image in the fraction field is a positive product. -/
def positivePolynomial (q : ℚ) (n : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.range n,
    (Polynomial.C (((j : ℤ) + 1 : ℤ) : ℚ) + Polynomial.C q * Polynomial.X)

theorem G_positive_polynomial (n : ℕ) :
    G ((n : ℤ) + 1) = algebraMap (Polynomial ℚ) RF (positivePolynomial 6 n) := by
  rw [G_positive_product]
  simp only [positivePolynomial, map_prod, ← linearFactor_image]

theorem positivePolynomial_six_zero : positivePolynomial 6 0 = 1 := by
  simp [positivePolynomial]

theorem polynomial_C_six : Polynomial.C (6 : ℚ) = (6 : Polynomial ℚ) :=
  map_natCast Polynomial.C 6

theorem positivePolynomial_six_one :
    positivePolynomial 6 1 = 1 + 6 * Polynomial.X := by
  norm_num [positivePolynomial, Finset.prod_range_succ, polynomial_C_six]

theorem positivePolynomial_six_two :
    positivePolynomial 6 2 =
      2 + 18 * Polynomial.X + 36 * Polynomial.X ^ 2 := by
  norm_num [positivePolynomial, Finset.prod_range_succ, polynomial_C_six]; ring

theorem positivePolynomial_six_three :
    positivePolynomial 6 3 =
      6 + 66 * Polynomial.X + 216 * Polynomial.X ^ 2 + 216 * Polynomial.X ^ 3 := by
  norm_num [positivePolynomial, Finset.prod_range_succ, polynomial_C_six]; ring

theorem positivePolynomial_six_four :
    positivePolynomial 6 4 =
      24 + 300 * Polynomial.X + 1260 * Polynomial.X ^ 2 +
        2160 * Polynomial.X ^ 3 + 1296 * Polynomial.X ^ 4 := by
  norm_num [positivePolynomial, Finset.prod_range_succ, polynomial_C_six]; ring

/-- Columns are the coefficients of the actual positive polynomials
underlying `G_1,...,G_5`; rows are rho-degrees 0,...,4. -/
def constantCoefficientMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i r => (positivePolynomial 6 r.val).coeff i.val

def printedConstantMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, 1, 2, 6, 24;
     0, 6, 18, 66, 300;
     0, 0, 36, 216, 1260;
     0, 0, 0, 216, 2160;
     0, 0, 0, 0, 1296]

attribute [local simp] Polynomial.coeff_one Polynomial.coeff_X

theorem constantCoefficientMatrix_eq :
    constantCoefficientMatrix = printedConstantMatrix := by
  have h0 := positivePolynomial_six_zero
  have h1 := positivePolynomial_six_one
  have h2 := positivePolynomial_six_two
  have h3 := positivePolynomial_six_three
  have h4 := positivePolynomial_six_four
  ext i r
  fin_cases i <;> fin_cases r <;>
    simp_all [constantCoefficientMatrix, printedConstantMatrix]

theorem printedConstantMatrix_upper : printedConstantMatrix.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [printedConstantMatrix] at *

/-- The fixed five-coefficient determinant, derived from the actual factors. -/
theorem constantCoefficientMatrix_det : constantCoefficientMatrix.det = 6 ^ 10 := by
  rw [constantCoefficientMatrix_eq,
    Matrix.det_of_isUpperTriangular printedConstantMatrix_upper]
  norm_num [printedConstantMatrix, Fin.prod_univ_succ]

theorem constantCoefficientMatrix_det_ne_zero : constantCoefficientMatrix.det ≠ 0 := by
  rw [constantCoefficientMatrix_det]
  norm_num

end MellinFactors
end WPResidueQuotient
