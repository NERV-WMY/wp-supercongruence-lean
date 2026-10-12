import WPFiniteConductorPolynomial
import WPNativeCutoff

open scoped BigOperators
open Polynomial

namespace WPFiniteConductorPolynomial

def integralSubring (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {a | 0 ≤ padicValRat p a}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    by_cases hab : a + b = 0
    · simp [hab]
    exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add hab)
  neg_mem' := by intro a ha; simpa using ha
  mul_mem' := by
    intro a b ha hb
    by_cases ha0 : a = 0
    · simp [ha0]
    by_cases hb0 : b = 0
    · simp [hb0]
    change 0 ≤ padicValRat p (a * b)
    rw [padicValRat.mul ha0 hb0]
    exact add_nonneg ha hb

/-- Polynomial membership retains every coefficient, including zero slots. -/
def coefficientSubring (R : Subring ℚ) : Subring ℚ[X] where
  carrier := {P | ∀ k, P.coeff k ∈ R}
  zero_mem' := by intro k; simp only [coeff_zero]; exact R.zero_mem
  one_mem' := by
    intro k
    rw [coeff_one]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  add_mem' := by
    intro P Q hP hQ k
    rw [coeff_add]
    exact R.add_mem (hP k) (hQ k)
  neg_mem' := by
    intro P hP k
    rw [coeff_neg]
    exact R.neg_mem (hP k)
  mul_mem' := by
    intro P Q hP hQ k
    rw [coeff_mul]
    exact R.sum_mem (fun ij _ => R.mul_mem (hP ij.1) (hQ ij.2))

theorem mem_coefficientSubring (R : Subring ℚ) (P : ℚ[X]) :
    P ∈ coefficientSubring R ↔ ∀ k, P.coeff k ∈ R := Iff.rfl

attribute [irreducible] coefficientSubring

theorem C_mem_coefficientSubring (R : Subring ℚ) (a : ℚ) (ha : a ∈ R) :
    C a ∈ coefficientSubring R := by
  rw [mem_coefficientSubring]
  intro k
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem

theorem X_mem_coefficientSubring (R : Subring ℚ) : X ∈ coefficientSubring R := by
  rw [mem_coefficientSubring]
  intro k
  rw [coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem integerPolynomial_mem (R : Subring ℚ) (Z : ℤ[X]) :
    Z.map (Int.castRingHom ℚ) ∈ coefficientSubring R := by
  rw [mem_coefficientSubring]
  intro k
  rw [coeff_map]
  exact intCast_mem R (Z.coeff k)

theorem small_inverse_integral (p d : ℕ) [Fact p.Prime]
    (hd : 0 < d) (hdp : d < p) : (1 / (d : ℚ)) ∈ integralSubring p := by
  have hnd : ¬p ∣ d := by
    intro h
    have := Nat.le_of_dvd hd h
    omega
  change 0 ≤ padicValRat p (1 / (d : ℚ))
  simp only [one_div, padicValRat.inv, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hnd, Int.natCast_zero, neg_zero, le_refl]

theorem canceledKernel_integral (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    canceledKernel k ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hx : X ∈ P := X_mem_coefficientSubring R
  have h2 : (1 / 2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hmC : (27 / 1000 : ℚ) ∈ R := by
    rw [show (27 / 1000 : ℚ) = 27 * (1 / 2) ^ 3 * (1 / 5) ^ 3 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 27) (R.pow_mem h2 3)) (R.pow_mem h5 3)
  have hlC : (729 / 15625 : ℚ) ∈ R := by
    rw [show (729 / 15625 : ℚ) = 729 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  have hQ2C : (-81 / 2000000 : ℚ) ∈ R := by
    rw [show (-81 / 2000000 : ℚ) = -81 * (1 / 2) ^ 7 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (R.mul_mem (R.neg_mem (natCast_mem R 81))
      (R.pow_mem h2 7)) (R.pow_mem h5 6)
  have hQ3C : (-2187 / 1000000000 : ℚ) ∈ R := by
    rw [show (-2187 / 1000000000 : ℚ) = -2187 * (1 / 2) ^ 9 * (1 / 5) ^ 9 by norm_num]
    exact R.mul_mem (R.mul_mem (R.neg_mem (natCast_mem R 2187))
      (R.pow_mem h2 9)) (R.pow_mem h5 9)
  have hm : m ∈ P := by
    unfold m
    have hpoly : (80 - 99 * X + 27 * X ^ 2 : ℚ[X]) ∈ P := by
      repeat' first | apply P.mul_mem | apply P.add_mem | apply P.sub_mem | apply P.neg_mem |
        apply P.pow_mem | exact hx | exact natCast_mem P _
    exact P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ hmC) hx) hpoly
  have hl : lam ∈ P := by
    unfold lam
    exact P.mul_mem (C_mem_coefficientSubring R _ hlC) (P.pow_mem hx 3)
  induction k using Nat.twoStepInduction with
  | zero =>
    unfold canceledKernel Q2
    apply P.mul_mem (C_mem_coefficientSubring R _ hQ2C)
    repeat' first | apply P.mul_mem | apply P.add_mem | apply P.sub_mem | apply P.neg_mem |
      apply P.pow_mem | exact hx | exact natCast_mem P _
  | one =>
    unfold canceledKernel Q3
    apply P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ hQ3C) hx)
    repeat' first | apply P.mul_mem | apply P.add_mem | apply P.sub_mem | apply P.neg_mem |
      apply P.pow_mem | exact hx | exact natCast_mem P _
  | more k hk hk1 =>
    rw [canceledKernel]
    exact P.sub_mem (P.mul_mem (P.mul_mem (natCast_mem P 2) hm) hk1) (P.mul_mem hl hk)

theorem Be_integral_coefficients (p e : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (he : e < p) (k : ℕ) : 0 ≤ padicValRat p ((Be p e).coeff k) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hx : X ∈ P := X_mem_coefficientSubring R
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hlC : (729 / 15625 : ℚ) ∈ R := by
    rw [show (729 / 15625 : ℚ) = 729 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  have hl : lam ∈ P := P.mul_mem (C_mem_coefficientSubring R _ hlC) (P.pow_mem hx 3)
  have hBe : Be p e ∈ P := by
    unfold Be
    apply P.sum_mem
    intro n hn
    have hnlt : n < p := by have := Finset.mem_range.mp hn; omega
    have hc : WPReview.nativeCoefficient n ∈ R := by
      change 0 ≤ padicValRat p (WPReview.nativeCoefficient n)
      rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp hnlt]
      have hdiv : 3 * n / p ≤ 6 * n / p := Nat.div_le_div_right (by omega)
      exact sub_nonneg.mpr (by exact_mod_cast hdiv)
    exact P.mul_mem
      (P.mul_mem (C_mem_coefficientSubring R _ (R.mul_mem (natCast_mem R 2) hc))
        (P.pow_mem hl (n + 1))) (canceledKernel_integral p _ hp)
  exact (mem_coefficientSubring R (Be p e)).mp hBe k

theorem native_cutoff_conductor_degree (p : ℕ) (hp : 19 ≤ p) :
    (Be p (p - 1 - p / 6)).natDegree ≤ 3 * p - 1 := by
  apply Be_degree
  have hdiv : 3 ≤ p / 6 := by omega
  omega

theorem native_cutoff_conductor_integral (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    0 ≤ padicValRat p ((Be p (p - 1 - p / 6)).coeff k) := by
  exact Be_integral_coefficients p _ (by omega) (by omega) k

end WPFiniteConductorPolynomial
