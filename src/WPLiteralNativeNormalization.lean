import WPReview.NativeTruncation
import WPReview.FiniteStokes
import WPReview.Literal

open scoped BigOperators
open Polynomial

namespace WPLiteralNativeNormalization

theorem literal_power_scaling (n : ℕ) :
    (4 : ℚ) ^ (3 * n) * (729 / 15625 : ℚ) ^ n /
      ((1728 : ℚ) ^ n) ^ 2 = 1 / (10 : ℚ) ^ (6 * n) := by
  have h1728 : ((1728 : ℚ) ^ n) ^ 2 = ((1728 : ℚ) ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  rw [show (4 : ℚ) ^ (3 * n) = ((4 : ℚ) ^ 3) ^ n by rw [pow_mul],
    h1728, ← mul_pow, ← div_pow]
  have hbase : (4 : ℚ) ^ 3 * (729 / 15625 : ℚ) / (1728 : ℚ) ^ 2 =
      1 / (10 : ℚ) ^ 6 := by norm_num
  rw [hbase, div_pow, one_pow, pow_mul]

/-- The literal weight normalization of the full native factorial coefficient. -/
theorem native_gamma_literal_term (n : ℕ) :
    WPReview.gamma (3 * n) * (2 * ((3 * n : ℕ) : ℚ) + 1) *
      WPReview.nativeCoefficient n ^ 2 * (729 / 15625 : ℚ) ^ n *
      (WPReview.weightNat n : ℚ) = WPReview.literalTerm n := by
  have hg := WPReview.gamma_factorial_identity (3 * n)
  have h3 : ((3 * n).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (3 * n))
  have h6 : ((6 * n).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (6 * n))
  have hn : (n.factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [mul_comm (WPReview.gamma (3 * n)), hg,
    show 2 * (3 * n) = 6 * n by omega]
  calc
    (4 : ℚ) ^ (3 * n) * ((3 * n).factorial : ℚ) ^ 2 /
        ((6 * n).factorial : ℚ) * WPReview.nativeCoefficient n ^ 2 *
        (729 / 15625 : ℚ) ^ n * (WPReview.weightNat n : ℚ) =
      ((6 * n).factorial : ℚ) / (n.factorial : ℚ) ^ 6 *
        ((4 : ℚ) ^ (3 * n) * (729 / 15625 : ℚ) ^ n /
          ((1728 : ℚ) ^ n) ^ 2) * (WPReview.weightNat n : ℚ) := by
      unfold WPReview.nativeCoefficient
      field_simp
    _ = WPReview.literalTerm n := by
      rw [literal_power_scaling]
      unfold WPReview.literalTerm
      ring

/-- The actual finite cubic pullback of P(theta_lambda)H(lambda). -/
noncomputable def outerPolynomial (p : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range p,
    monomial (3 * n) ((WPReview.weightNat n : ℚ) *
      WPReview.nativeCoefficient n ^ 2 * (729 / 15625 : ℚ) ^ n)

/-- The outer operator 2x d/dx+1, retaining its ordinary coefficient action. -/
noncomputable def outerOperator (P : ℚ[X]) : ℚ[X] := 2 * WPReview.nativeTheta P + P

theorem outerOperator_coeff (P : ℚ[X]) (k : ℕ) :
    (outerOperator P).coeff k = (2 * (k : ℚ) + 1) * P.coeff k := by
  simp [outerOperator, WPReview.nativeTheta_coeff]
  ring

theorem Gamma_monomial (L k : ℕ) (a : ℚ) (hk : k ≤ L) :
    WPReview.Gamma L (fun j => (monomial k a : ℚ[X]).coeff j) =
      WPReview.gamma k * a := by
  classical
  simp only [WPReview.Gamma, coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [hjk.symm]
  · intro hk'
    exact (hk' (Finset.mem_range.mpr (by omega))).elim

/-- The exact universal finite outer formula, before any source or congruence argument. -/
theorem Gamma_outer_literal (p L : ℕ) (hL : ∀ n < p, 3 * n ≤ L) :
    WPReview.Gamma L (fun k => (outerOperator (outerPolynomial p)).coeff k) =
      WPReview.literalSum p := by
  classical
  simp only [WPReview.Gamma, outerOperator_coeff, outerPolynomial, finsetSum_coeff,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold WPReview.literalSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n < p := Finset.mem_range.mp hn
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (3 * n)]
  · simp only [ite_true]
    have h := native_gamma_literal_term n
    convert h using 1
    ring
  · intro j hj hjn
    simp [hjn.symm]
  · intro hk'
    exact (hk' (Finset.mem_range.mpr (by have := hL n hn'; omega))).elim

theorem Gamma_outer_literal_extended (p : ℕ) :
    WPReview.Gamma (3 * p - 1)
      (fun k => (outerOperator (outerPolynomial p)).coeff k) =
        WPReview.literalSum p := by
  apply Gamma_outer_literal
  intro n hn
  omega

end WPLiteralNativeNormalization
