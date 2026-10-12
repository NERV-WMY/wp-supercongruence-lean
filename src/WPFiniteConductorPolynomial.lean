import WPReview.NativeTruncation
import Mathlib.Tactic

open scoped BigOperators
open Polynomial

namespace WPFiniteConductorPolynomial

noncomputable def lam : ℚ[X] := C (729 / 15625) * X ^ 3
noncomputable def m : ℚ[X] := C (27 / 1000) * X * (80 - 99 * X + 27 * X ^ 2)
noncomputable def ell : ℚ[X] := C (27 / 1000) * X * (9 * X - 16)
noncomputable def collision : ℚ[X] := 25 - 9 * X
noncomputable def escape : ℚ[X] := 99 * X - 50

/-- The original retained s03 LP[2,0] witness. -/
noncomputable def LP20 : ℚ[X] :=
  C (1953125 / 209952) * (9 * X - 25) * (81 * X ^ 2 - 198 * X + 80) *
    (243 * X ^ 3 - 1053 * X ^ 2 + 1266 * X - 400)

/-- The original retained s03 RP[2,0] witness. -/
noncomputable def RP20 : ℚ[X] :=
  C (1953125 / 209952) * (59049 * X ^ 6 - 511758 * X ^ 5 +
    1724085 * X ^ 4 - 2860596 * X ^ 3 + 2441988 * X ^ 2 - 1011200 * X + 160000)

noncomputable def K : ℚ[X] :=
  (ell - 2 * (1 - X) * derivative ell) * collision + 9 * (1 - X) * ell

/-- Coefficients of x*g(s,x), keeping the literal original witness formula. -/
noncomputable def G0 : ℚ[X] :=
  2 * X * (1 - X) * LP20 * derivative lam +
    2 * X * RP20 * (-2 * (1 - X) * ell * collision * derivative m - m * K)

noncomputable def G1 : ℚ[X] :=
  12 * (1 - X) * (-LP20 * m + ell * collision * RP20) -
    4 * X * (1 - X) * LP20 * derivative m + 2 * X * RP20 * K

noncomputable def G2 : ℚ[X] := 12 * (1 - X) * LP20

noncomputable def kernelInput : ℕ → ℚ[X]
  | 0 => G0
  | 1 => G1 - G0
  | 2 => G2 - G1
  | 3 => -G2
  | _ + 4 => 0

/-- lambda^(k+1) times the original coefficient [s^k]((1-s)x*g/f). -/
noncomputable def scaledKernel : ℕ → ℚ[X]
  | 0 => kernelInput 0
  | 1 => 2 * m * kernelInput 0 + lam * kernelInput 1
  | k + 2 => 2 * m * scaledKernel (k + 1) - lam * scaledKernel k +
      lam ^ (k + 2) * kernelInput (k + 2)

/-- The full cusp, collision and double escape divisor, including x*g's extra x. -/
noncomputable def sourceDivisor : ℚ[X] := X ^ 5 * collision * escape ^ 2

noncomputable def Q2 : ℚ[X] :=
  C (-81 / 2000000) * (531441 * X ^ 8 - 6908733 * X ^ 7 +
    38244069 * X ^ 6 - 117490743 * X ^ 5 + 218546910 * X ^ 4 -
    251265024 * X ^ 3 + 173637632 * X ^ 2 - 65536000 * X + 10240000)

noncomputable def Q3 : ℚ[X] :=
  C (-2187 / 1000000000) * X * (14348907 * X ^ 10 - 239148450 * X ^ 9 +
    1759069710 * X ^ 8 - 7511426460 * X ^ 7 + 20594814975 * X ^ 6 -
    37830511674 * X ^ 5 + 47067955200 * X ^ 4 - 39081738240 * X ^ 3 +
    20666122240 * X ^ 2 - 6258688000 * X + 819200000)

/-- Quotient indexed by the original reciprocal coefficient k+2. -/
noncomputable def canceledKernel : ℕ → ℚ[X]
  | 0 => Q2
  | 1 => Q3
  | k + 2 => 2 * m * canceledKernel (k + 1) - lam * canceledKernel k

theorem original_coefficient_two : scaledKernel 2 = sourceDivisor * Q2 := by
  apply Polynomial.funext
  intro x
  norm_num [scaledKernel, kernelInput, G0, G1, G2, K, LP20, RP20,
    m, lam, ell, sourceDivisor, collision, escape, Q2,
    derivative_mul, derivative_pow_succ]
  ring

theorem original_coefficient_three : scaledKernel 3 = sourceDivisor * Q3 := by
  apply Polynomial.funext
  intro x
  norm_num [scaledKernel, kernelInput, G0, G1, G2, K, LP20, RP20,
    m, lam, ell, sourceDivisor, collision, escape, Q3,
    derivative_mul, derivative_pow_succ]
  ring

/-- All three original pole factors cancel, with escape multiplicity two retained. -/
theorem original_cusp_collision_escape_cancellation (k : ℕ) :
    scaledKernel (k + 2) = sourceDivisor * canceledKernel k := by
  induction k using Nat.twoStepInduction with
  | zero => exact original_coefficient_two
  | one => exact original_coefficient_three
  | more k hk hk1 =>
    rw [scaledKernel]
    rw [show k + 2 + 2 = k + 4 by omega]
    simp only [kernelInput, mul_zero, add_zero]
    rw [canceledKernel]
    rw [hk, hk1]
    ring

theorem canceledKernel_degree (k : ℕ) :
    (canceledKernel k).natDegree ≤ 3 * k + 8 := by
  have hm : m.natDegree ≤ 3 := by unfold m; compute_degree
  have hl : lam.natDegree ≤ 3 := by unfold lam; compute_degree
  induction k using Nat.twoStepInduction with
  | zero => unfold canceledKernel Q2; compute_degree
  | one => unfold canceledKernel Q3; compute_degree
  | more k hk hk1 =>
    rw [canceledKernel]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · have htwo : (2 * m).natDegree ≤ 3 := by
        exact (natDegree_mul_le_of_le (by simp) hm)
      exact (natDegree_mul_le_of_le htwo hk1).trans (by omega)
    · exact (natDegree_mul_le_of_le hl hk).trans (by omega)

/-- The original coefficient-defined conductor's explicitly canceled polynomial. -/
noncomputable def Be (p e : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range (e + 1),
    C (2 * WPReview.nativeCoefficient n) * lam ^ (n + 1) *
      canceledKernel (p - 4 - n)

theorem Be_degree (p e : ℕ) (he : e + 4 ≤ p) :
    (Be p e).natDegree ≤ 3 * p - 1 := by
  classical
  apply natDegree_le_iff_degree_le.mpr
  unfold Be
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro n hn
  have hnle : n ≤ e := by have := Finset.mem_range.mp hn; omega
  apply degree_le_of_natDegree_le
  have hl : lam.natDegree ≤ 3 := by unfold lam; compute_degree
  have hpow := natDegree_pow_le_of_le (n + 1) hl
  have hc : (C (2 * WPReview.nativeCoefficient n)).natDegree ≤ 0 :=
    (natDegree_C _).le
  have hmul := natDegree_mul_le_of_le
    (natDegree_mul_le_of_le hc hpow) (canceledKernel_degree (p - 4 - n))
  exact hmul.trans (by omega)

/-- The exact numerator produced by original coefficient extraction for Fe. -/
noncomputable def originalNumerator (p e : ℕ) : ℚ[X] :=
  ∑ n ∈ Finset.range (e + 1),
    C (2 * WPReview.nativeCoefficient n) * lam ^ (n + 1) * scaledKernel (p - 2 - n)

theorem Be_original_numerator (p e : ℕ) (he : e + 4 ≤ p) :
    sourceDivisor * Be p e = originalNumerator p e := by
  classical
  unfold Be originalNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ e := by have := Finset.mem_range.mp hn; omega
  have hindex : p - 2 - n = (p - 4 - n) + 2 := by omega
  rw [hindex, original_cusp_collision_escape_cancellation]
  ring

end WPFiniteConductorPolynomial
