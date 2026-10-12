import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open scoped BigOperators
open Polynomial

namespace WPReview

def nativeCoefficient (n : ℕ) : ℚ :=
  ((6*n).factorial : ℚ) /
    (((3*n).factorial : ℚ) * (n.factorial : ℚ)^3 * (1728 : ℚ)^n)

noncomputable def nativePolynomial (p : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range p, monomial n (nativeCoefficient n)

noncomputable def nativeTheta (P : ℚ[X]) : ℚ[X] := X * derivative P

noncomputable def nativeShift (a : ℚ) (P : ℚ[X]) : ℚ[X] :=
  nativeTheta P + C a * P

noncomputable def nativeOperator (P : ℚ[X]) : ℚ[X] :=
  nativeTheta (nativeTheta (nativeTheta P)) -
    X * nativeShift (1/2) (nativeShift (1/6) (nativeShift (5/6) P))

def nativeEndpoint (p : ℕ) : ℚ :=
  ((p : ℚ)-1/2)*((p : ℚ)-5/6)*((p : ℚ)-1/6)*nativeCoefficient (p-1)

theorem nativeCoefficient_zero : nativeCoefficient 0 = 1 := by
  norm_num [nativeCoefficient]

private theorem factorial_six_block (n : ℕ) :
    ((6*(n+1)).factorial : ℚ) =
      ((6*n).factorial : ℚ) *
        (6*(n : ℚ)+1)*(6*(n : ℚ)+2)*(6*(n : ℚ)+3)*
        (6*(n : ℚ)+4)*(6*(n : ℚ)+5)*(6*(n : ℚ)+6) := by
  have h := Nat.factorial_mul_ascFactorial (6*n) 6
  have hq := congrArg (fun k : ℕ => (k : ℚ)) h
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero] at hq
  rw [show 6*(n+1)=6*n+6 by omega]
  linear_combination -hq

private theorem factorial_three_block (n : ℕ) :
    ((3*(n+1)).factorial : ℚ) =
      ((3*n).factorial : ℚ) *
        (3*(n : ℚ)+1)*(3*(n : ℚ)+2)*(3*(n : ℚ)+3) := by
  have h := Nat.factorial_mul_ascFactorial (3*n) 3
  have hq := congrArg (fun k : ℕ => (k : ℚ)) h
  norm_num [Nat.ascFactorial_succ, Nat.ascFactorial_zero] at hq
  rw [show 3*(n+1)=3*n+3 by omega]
  linear_combination -hq

theorem nativeCoefficient_recurrence (n : ℕ) :
    ((n : ℚ)+1)^3*nativeCoefficient (n+1) =
      ((n : ℚ)+1/2)*((n : ℚ)+1/6)*((n : ℚ)+5/6)*nativeCoefficient n := by
  unfold nativeCoefficient
  rw [factorial_six_block, factorial_three_block, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h3n : ((3*n).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (3*n))
  have hpos : 0 < (n : ℚ)+1 := by positivity
  field_simp
  ring

theorem nativePolynomial_coeff (p n : ℕ) :
    (nativePolynomial p).coeff n = if n < p then nativeCoefficient n else 0 := by
  classical
  simp only [nativePolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by
      have hb' := Finset.mem_range.mp hb
      omega
    simp [hbn]

theorem nativeTheta_coeff (P : ℚ[X]) (n : ℕ) :
    (nativeTheta P).coeff n = (n : ℚ)*P.coeff n := by
  cases n with
  | zero => simp [nativeTheta]
  | succ n =>
      rw [nativeTheta, coeff_X_mul, coeff_derivative]
      push_cast
      ring

private theorem nativeShift_coeff (a : ℚ) (P : ℚ[X]) (n : ℕ) :
    (nativeShift a P).coeff n = ((n : ℚ)+a)*P.coeff n := by
  simp only [nativeShift, coeff_add, nativeTheta_coeff, coeff_C_mul]
  ring

private theorem nativeOperator_coeff_zero (P : ℚ[X]) :
    (nativeOperator P).coeff 0 = 0 := by
  simp [nativeOperator, nativeTheta_coeff]

theorem nativeOperator_coeff_succ (P : ℚ[X]) (n : ℕ) :
    (nativeOperator P).coeff (n+1) =
      ((n : ℚ)+1)^3*P.coeff (n+1) -
        ((n : ℚ)+1/2)*((n : ℚ)+1/6)*((n : ℚ)+5/6)*P.coeff n := by
  simp only [nativeOperator, coeff_sub, nativeTheta_coeff, coeff_X_mul,
    nativeShift_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem nativeEndpoint_eq (p : ℕ) (hp : 0 < p) :
    nativeEndpoint p = (p : ℚ)^3*nativeCoefficient p := by
  have h := nativeCoefficient_recurrence (p-1)
  have heq : p-1+1=p := by omega
  have hq : ((p-1 : ℕ) : ℚ) = (p : ℚ)-1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [heq, hq] at h
  unfold nativeEndpoint
  linear_combination -h

theorem native_truncation_residual (p : ℕ) (hp : 0 < p) :
    nativeOperator (nativePolynomial p) = monomial p (-nativeEndpoint p) := by
  ext k
  cases k with
  | zero => simp [nativeOperator_coeff_zero, coeff_monomial, Nat.ne_of_gt hp]
  | succ n =>
      rw [nativeOperator_coeff_succ, nativePolynomial_coeff, nativePolynomial_coeff,
        coeff_monomial]
      by_cases hn : n+1 < p
      · have hn' : n < p := by omega
        have hpne : p ≠ n+1 := by omega
        rw [if_pos hn, if_pos hn', if_neg hpne]
        exact sub_eq_zero.mpr (nativeCoefficient_recurrence n)
      · by_cases heq : n+1=p
        · have hn' : n < p := by omega
          have hpred : p-1=n := by omega
          rw [if_neg hn, if_pos hn', if_pos heq.symm]
          simp only [nativeEndpoint, hpred]
          rw [← heq]
          push_cast
          ring
        · have hn' : ¬n < p := by omega
          rw [if_neg hn, if_neg hn', if_neg (Ne.symm heq)]
          ring

end WPReview
