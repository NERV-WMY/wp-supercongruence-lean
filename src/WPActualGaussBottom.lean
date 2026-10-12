import WPActualCubicHasse

open scoped BigOperators Polynomial
open Polynomial WPActualNativeHasse WPActualCMGauss

namespace WPActualGaussBottom

noncomputable def fieldHarmonic (p n : ℕ) : ZMod p :=
  ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ZMod p)⁻¹

theorem fieldHarmonic_zero (p : ℕ) : fieldHarmonic p 0 = 0 := by simp [fieldHarmonic]

theorem fieldHarmonic_succ (p n : ℕ) :
    fieldHarmonic p (n + 1) = fieldHarmonic p n + ((n + 1 : ℕ) : ZMod p)⁻¹ := by
  simp only [fieldHarmonic, Finset.sum_range_succ]

theorem actualGauss_cleared_recurrence (p n : ℕ) :
    (((n : ZMod p) + 1) ^ 2) * (actualGauss p).coeff (n + 1) =
      ((n : ZMod p) - ((p / 3 : ℕ) : ZMod p)) *
        ((n : ZMod p) + ((p / 3 : ℕ) : ZMod p) + 1) * (actualGauss p).coeff n := by
  have he := congrArg (fun z : ℤ => (z : ZMod p))
    (shiftedLegendre_cleared_recurrence (p / 3) n)
  simpa only [actualGauss, coeff_map, Int.cast_mul, Int.cast_pow, Int.cast_sub,
    Int.cast_add, Int.cast_one, Int.cast_natCast, Int.coe_castRingHom] using he

/-- The literal derivative in the Gauss bottom parameter, with all finite coefficients. -/
noncomputable def actualBottom (p : ℕ) : (ZMod p)[X] :=
  ∑ n ∈ Finset.range (p / 3 + 1), monomial n
    (-fieldHarmonic p n * (actualGauss p).coeff n)

theorem actualBottom_coeff (p n : ℕ) :
    (actualBottom p).coeff n = -fieldHarmonic p n * (actualGauss p).coeff n := by
  classical
  simp only [actualBottom, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p / 3 + 1
  · rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · have hy : (actualGauss p).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt ((actualGauss_degree p).trans_lt (by omega))
    rw [hy, mul_zero]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem actualBottom_origin (p : ℕ) : (actualBottom p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, actualBottom_coeff, fieldHarmonic_zero]
  ring

theorem actualBottom_degree (p : ℕ) : (actualBottom p).natDegree ≤ p / 3 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [actualBottom_coeff, coeff_eq_zero_of_natDegree_lt ((actualGauss_degree p).trans_lt hn)]
  ring

theorem actualBottom_cleared_recurrence (p n : ℕ) [Fact p.Prime] (_hp : 19 ≤ p) :
    ((n : ZMod p) + 1) ^ 2 * (actualBottom p).coeff (n + 1) -
      ((n : ZMod p) - ((p / 3 : ℕ) : ZMod p)) *
        ((n : ZMod p) + ((p / 3 : ℕ) : ZMod p) + 1) * (actualBottom p).coeff n =
        -((n : ZMod p) + 1) * (actualGauss p).coeff (n + 1) := by
  rw [actualBottom_coeff, actualBottom_coeff]
  have he := actualGauss_cleared_recurrence p n
  by_cases hn : n < p / 3
  · have hu : ((n : ZMod p) + 1) ≠ 0 := by
      rw [← Nat.cast_add_one]
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < n + 1) hd
      omega
    have hi := mul_inv_cancel₀ hu
    rw [fieldHarmonic_succ]
    simp only [Nat.cast_add, Nat.cast_one] at *
    linear_combination -fieldHarmonic p n * he -
      (((n : ZMod p) + 1) * (actualGauss p).coeff (n + 1)) * hi
  · have hy : (actualGauss p).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((actualGauss_degree p).trans_lt (by omega))
    rw [hy] at he ⊢
    linear_combination -fieldHarmonic p n * he

theorem actualBottom_euler_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreEuler (p / 3) (actualBottom p) = -theta (actualGauss p) := by
  ext n
  cases n with
  | zero => simp [legendreEuler_coeff_zero, theta_coeff]
  | succ n =>
    rw [legendreEuler_coeff_succ, coeff_neg, theta_coeff]
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul] using actualBottom_cleared_recurrence p n hp

theorem actualBottom_regular_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreRegular (p / 3) (actualBottom p) = -(actualGauss p).derivative := by
  have he := actualBottom_euler_source p hp
  rw [legendreEuler_eq_X_regular, theta] at he
  have hz : X * (legendreRegular (p / 3) (actualBottom p) + (actualGauss p).derivative) = 0 := by
    linear_combination he
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left X_ne_zero)

noncomputable def properGauss (p : ℕ) : (ZMod p)[X] :=
  actualBottom p + C (fieldHarmonic p (p / 3)) * actualGauss p

theorem properGauss_coeff (p n : ℕ) : (properGauss p).coeff n =
    (fieldHarmonic p (p / 3) - fieldHarmonic p n) * (actualGauss p).coeff n := by
  simp only [properGauss, coeff_add, coeff_C_mul, actualBottom_coeff]
  ring

theorem properGauss_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (properGauss p).natDegree ≤ p / 3 - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [properGauss_coeff]
  by_cases he : n = p / 3
  · rw [he, sub_self, zero_mul]
  · have hnk : p / 3 < n := by omega
    rw [coeff_eq_zero_of_natDegree_lt ((actualGauss_degree p).trans_lt hnk), mul_zero]

theorem properGauss_origin (p : ℕ) : (properGauss p).eval 0 = fieldHarmonic p (p / 3) := by
  simp [properGauss, actualBottom_origin, actualGauss_origin]

theorem legendreRegular_add_C_mul {K : Type*} [CommRing K] (k : ℕ) (P Q : K[X]) (c : K) :
    legendreRegular k (P + C c * Q) = legendreRegular k P + C c * legendreRegular k Q := by
  simp [legendreRegular, derivative_mul]
  ring

theorem actualGauss_legendre_regular (p : ℕ) : legendreRegular (p / 3) (actualGauss p) = 0 := by
  rw [actualGauss, ← legendreRegular_map, actual_integer_legendre_ODE, Polynomial.map_zero]

theorem properGauss_regular_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreRegular (p / 3) (properGauss p) = -(actualGauss p).derivative := by
  rw [properGauss, legendreRegular_add_C_mul, actualBottom_regular_source p hp,
    actualGauss_legendre_regular, mul_zero, add_zero]

end WPActualGaussBottom
