import WPMomentPrecision.SecondLift.LogDegree
import Mathlib.Algebra.Polynomial.Expand

open scoped BigOperators Polynomial
open Polynomial WPMomentPrecision.NativeSecondLift WPMomentPrecision.LogReflection
  WPMomentPrecision.LogDegree

namespace WPMomentPrecision.LogQuadraticRepresentation

set_option maxHeartbeats 1600000

noncomputable def evenCoefficientFold {K : Type*} [Semiring K] (d : ℕ) (P : K[X]) : K[X] :=
  ∑ n ∈ Finset.range (d + 1), monomial n (P.coeff (2 * n))

theorem evenCoefficientFold_coeff {K : Type*} [Semiring K] (d : ℕ) (P : K[X]) (n : ℕ) :
    (evenCoefficientFold d P).coeff n = if n < d + 1 then P.coeff (2 * n) else 0 := by
  classical
  simp only [evenCoefficientFold, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < d + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem evenCoefficientFold_degree {K : Type*} [Semiring K] (d : ℕ) (P : K[X]) :
    (evenCoefficientFold d P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [evenCoefficientFold_coeff, if_neg (by omega)]

theorem reflection_odd_coefficient_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (P : (ZMod p)[X]) (hP : P.comp (-X) = P) (n : ℕ) (hn : Odd n) : P.coeff n = 0 := by
  have h := congrArg (fun Q : (ZMod p)[X] => Q.coeff n) hP
  rw [show (-X : (ZMod p)[X]) = C (-1) * X by simp,
    comp_C_mul_X_coeff, hn.neg_one_pow] at h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd (by norm_num : 0 < 2)
      ((ZMod.natCast_eq_zero_iff 2 p).mp hz)
    omega
  have hz : (2 : ZMod p) * P.coeff n = 0 := by linear_combination -h
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem evenCoefficientFold_source (p d : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree ≤ 2 * d) (hP : P.comp (-X) = P) :
    (evenCoefficientFold d P).comp (X ^ 2) = P := by
  ext n
  rw [← expand_eq_comp_X_pow, coeff_expand (by norm_num : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, evenCoefficientFold_coeff]
    have he : 2 * (n / 2) = n := by
      have h := Nat.div_mul_cancel hn
      omega
    by_cases hnd : n / 2 < d + 1
    · rw [if_pos hnd, he]
    · rw [if_neg hnd]
      exact (coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by omega))).symm
  · rw [if_neg hn]
    have hmod : n % 2 ≠ 0 := by
      intro hz
      exact hn (Nat.dvd_of_mod_eq_zero hz)
    have hodd : Odd n := Nat.odd_iff.mpr (by have := Nat.mod_lt n (by omega : 0 < 2); omega)
    exact (reflection_odd_coefficient_zero p hp P hP n hodd).symm

/-- Literal q-coordinate representative of the actual full logarithmic subtraction. -/
noncomputable def actualLogSecondQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (evenCoefficientFold (p / 6) (actualLogSecondNumeratorField p hp)).comp (1 - X)

theorem actual_logarithmic_second_q_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogSecondQ p hp).natDegree ≤ p / 6 := by
  have hq : (1 - X : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul (evenCoefficientFold_degree _ _) hq).trans
    (by omega))

/-- IR28 is attached to all of K(q)-4R² before any negative-residue extraction. -/
theorem actual_logarithmic_second_q_representation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogSecondQ p hp).comp (1 - X ^ 2) = actualLogSecondNumeratorField p hp := by
  rw [actualLogSecondQ, comp_assoc,
    show (1 - X : (ZMod p)[X]).comp (1 - X ^ 2) = X ^ 2 by
      simp only [sub_comp, one_comp, X_comp]; ring]
  exact evenCoefficientFold_source p (p / 6) (by omega) _
    (actual_logarithmic_second_degree p hp) (actual_logarithmic_numerator_even p hp)

end WPMomentPrecision.LogQuadraticRepresentation
