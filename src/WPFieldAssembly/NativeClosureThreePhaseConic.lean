import WPFieldAssembly.ActualSimplePoleResidue
import WPFiniteJWeightedResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.ActualSimplePoleResidue WPFiniteJWeightedResidue
  WPFiniteJHighCoefficient

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

/-- A complete finite polynomial below the shift retains both original endpoint values. -/
theorem originPole_negative_polynomial (P : K[X]) (n : ℕ) (hP : P.natDegree ≤ n)
    (h4 : (4 : K) ≠ 0) :
    originPole (T (-(n : ℤ)) * P.toLaurent) =
      ((1 / 4 : K) ^ n * P.eval 4 - (4 : K) ^ n * P.eval (1 / 4)) / 15 := by
  have hlow : lowBand (n + 1) P = P := by
    ext j
    rw [lowBand_coeff]
    by_cases hj : j < n + 1
    · rw [if_pos hj]
    · rw [if_neg hj, coeff_eq_zero_of_natDegree_lt (by omega)]
  rw [originPole_trunc_inverse]
  simp only [map_mul, invert_T, neg_neg]
  rw [trunc_shift_invert_eval P n (1 / 4 : K) (one_div_ne_zero h4),
    trunc_shift_invert_eval P n (4 : K) h4, hlow]
  simp only [one_div, inv_inv]

/-- The three shifts use c^(kp)=c^k, separately for every retained k. -/
theorem originPole_prime_multiple (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hP : P.natDegree ≤ p) (k : ℕ) (hk : 1 ≤ k) :
    originPole (T (-((k * p : ℕ) : ℤ)) * P.toLaurent) =
      ((1 / 4 : K) ^ k * P.eval 4 - (4 : K) ^ k * P.eval (1 / 4)) / 15 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by
    rw [div_pow, one_pow, h4p]
  have hpk : p ≤ k * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p hk
  rw [originPole_negative_polynomial P (k * p) (hP.trans hpk) h4,
    Nat.mul_comm k p, pow_mul, pow_mul, hap, h4p]

/-- The original conic numerator retains all three nonunit Frobenius slots. -/
noncomputable def threePhaseConicDensity (p : ℕ) (P : K[X]) : K[T;T⁻¹] :=
  LaurentPolynomial.C (3 / 10 : K) *
    ((4 - 33 * T (-(p : ℤ)) + 72 * T (-2 * (p : ℤ)) -
      16 * T (-3 * (p : ℤ))) * T 2 * P.toLaurent)

/-- All three original slots contract together; no slot has an independently assigned value. -/
theorem threePhaseConic_two_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hP : P.natDegree ≤ p - 2) :
    originPole (threePhaseConicDensity p P) =
      (2 / 25 : K) * ((1 / 4 : K) ^ 2 * P.eval (1 / 4) - 4 ^ 2 * P.eval 4) := by
  let M : K[X] := X ^ 2 * P
  have hM : M.natDegree ≤ p := by
    have h := natDegree_mul_le_of_le (show (X ^ 2 : K[X]).natDegree ≤ 2 by simp) hP
    exact h.trans (by omega)
  have h1 := originPole_prime_multiple p hp M hM 1 (by omega)
  have h2 := originPole_prime_multiple p hp M hM 2 (by omega)
  have h3 := originPole_prime_multiple p hp M hM 3 (by omega)
  norm_num only [one_mul, pow_one, Nat.cast_mul, Nat.cast_ofNat] at h1 h2 h3
  rw [show -(2 * (p : ℤ)) = -2 * (p : ℤ) by ring] at h2
  rw [show -(3 * (p : ℤ)) = -3 * (p : ℤ) by ring] at h3
  have hs :
      (4 - 33 * T (-(p : ℤ)) + 72 * T (-2 * (p : ℤ)) -
        16 * T (-3 * (p : ℤ))) * T 2 * P.toLaurent =
      LaurentPolynomial.C (4 : K) * M.toLaurent -
        LaurentPolynomial.C (33 : K) * (T (-(p : ℤ)) * M.toLaurent) +
        LaurentPolynomial.C (72 : K) * (T (-2 * (p : ℤ)) * M.toLaurent) -
        LaurentPolynomial.C (16 : K) * (T (-3 * (p : ℤ)) * M.toLaurent) := by
    simp only [M, map_mul, Polynomial.toLaurent_X_pow, map_ofNat]
    ring
  rw [threePhaseConicDensity, originPole_C_mul, hs, originPole_sub,
    originPole_add, originPole_sub, originPole_C_mul, originPole_C_mul,
    originPole_C_mul, originPole_C_mul, originPole_polynomial, h1, h2, h3]
  simp only [M, eval_mul, eval_pow, eval_X]
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hthree : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hten : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by norm_num]
    exact mul_ne_zero htwo hfive
  have hfifteen : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by norm_num]
    exact mul_ne_zero hthree hfive
  have htwentyfive : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by norm_num]
    exact pow_ne_zero 2 hfive
  field_simp [hfour, hten, hfifteen, htwentyfive]
  ring

/-- Substitution of the two actual proper endpoints gives the original metric end value. -/
theorem threePhaseConic_metric_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hP : P.natDegree ≤ p - 2) (m : K)
    (ha : P.eval (1 / 4) = -8 * m / 15) (hb : P.eval 4 = m / 60) :
    originPole (threePhaseConicDensity p P) = -3 * m / 125 := by
  rw [threePhaseConic_two_ends p hp P hP, ha, hb]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by norm_num]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by norm_num]
    exact pow_ne_zero 2 h5
  have h60 : (60 : K) ≠ 0 := by
    rw [show (60 : K) = 4 * 15 by norm_num]
    exact mul_ne_zero h4 h15
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by norm_num]
    exact pow_ne_zero 3 h5
  field_simp [h4, h15, h25, h60, h125]
  ring

end WPFieldAssembly.ActualBpairContraction
