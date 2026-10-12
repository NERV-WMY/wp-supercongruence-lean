import WPReview.Literal
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Coprime.Lemmas

open scoped BigOperators
open Polynomial

namespace WPReview

/-- The five interpolation weights, indexed by the actual points 1 through 5. -/
def interpolationWeight (j : ℕ) : ℤ :=
  match j with
  | 1 => 5
  | 2 => -10
  | 3 => 10
  | 4 => -5
  | 5 => 1
  | _ => 0

def fiveInterpolation {R : Type*} [Ring R] (f : ℕ → R) : R :=
  5 * f 1 - 10 * f 2 + 10 * f 3 - 5 * f 4 + f 5

theorem fiveInterpolation_eq_sum (f : ℕ → ℚ) :
    fiveInterpolation f =
      ∑ i ∈ Finset.range 5, (interpolationWeight (i + 1) : ℚ) * f (i + 1) := by
  simp [Finset.sum_range_succ, interpolationWeight, fiveInterpolation]
  ring

theorem fiveInterpolation_sum {R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (f : ℕ → α → R) :
    fiveInterpolation (fun j => ∑ n ∈ s, f j n) =
      ∑ n ∈ s, fiveInterpolation (fun j => f j n) := by
  simp only [fiveInterpolation, Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

def integerFiveDifference (P : ℤ[X]) (p : ℕ) : ℤ :=
  fiveInterpolation (fun j => P.eval ((j : ℤ) * p)) - P.eval 0

/-- The five-point remainder is divisible by the fifth power at every integer step. -/
theorem integer_five_difference_dvd (P : ℤ[X]) (p : ℕ) :
    (p : ℤ) ^ 5 ∣ integerFiveDifference P p := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have h : integerFiveDifference (P + Q) p =
          integerFiveDifference P p + integerFiveDifference Q p := by
        simp only [integerFiveDifference, fiveInterpolation, Polynomial.eval_add]
        ring
      rw [h]
      exact dvd_add hP hQ
  | monomial k a =>
      simp only [integerFiveDifference, fiveInterpolation, Polynomial.eval_monomial]
      by_cases hk : k < 5
      · interval_cases k <;> exact ⟨0, by ring⟩
      · have hk5 : 5 ≤ k := Nat.le_of_not_gt hk
        have hk0 : k ≠ 0 := by omega
        have hpow : (p : ℤ) ^ 5 ∣ (p : ℤ) ^ k := pow_dvd_pow _ hk5
        have hm (j : ℤ) : (p : ℤ) ^ 5 ∣ a * (j * p) ^ k := by
          rw [mul_pow]
          simpa only [mul_assoc] using dvd_mul_of_dvd_right hpow (a * j ^ k)
        have h1 : (p : ℤ) ^ 5 ∣ a * (1 * (p : ℤ)) ^ k := hm 1
        have h2 := dvd_mul_of_dvd_right (hm 2) (10 : ℤ)
        have h3 := dvd_mul_of_dvd_right (hm 3) (10 : ℤ)
        have h4 := dvd_mul_of_dvd_right (hm 4) (5 : ℤ)
        have h5 := hm 5
        have h1' := dvd_mul_of_dvd_right h1 (5 : ℤ)
        have hz : (p : ℤ) ^ 5 ∣ a * 0 ^ k := by simp [hk0]
        exact dvd_sub (dvd_add (dvd_sub (dvd_add (dvd_sub h1' h2) h3) h4) h5) hz

/-- A finite rational coefficient with the upper endpoint encoded by `choose = 0`. -/
def finiteCoefficient (p N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range p,
    (Nat.choose N (6 * n) : ℚ) * (coefficientNat n : ℚ) / (10 : ℚ) ^ (6 * n)

def weightedBinomial (p n j : ℕ) : ℤ :=
  25 * (Nat.choose (j * p - 1) (6 * n) : ℤ) -
    210 * (Nat.choose (j * p - 2) (6 * n) : ℤ) +
    266 * (Nat.choose (j * p - 3) (6 * n) : ℤ)

def weightedFiniteCoefficient (p j : ℕ) : ℚ :=
  25 * finiteCoefficient p (j * p - 1) -
    210 * finiteCoefficient p (j * p - 2) +
    266 * finiteCoefficient p (j * p - 3)

def fifteenCoefficientCombination (p : ℕ) : ℚ :=
  fiveInterpolation (weightedFiniteCoefficient p)

theorem fifteenCoefficientCombination_eq_sum (p : ℕ) :
    fifteenCoefficientCombination p =
      ∑ i ∈ Finset.range 5, (interpolationWeight (i + 1) : ℚ) *
        (25 * finiteCoefficient p ((i + 1) * p - 1) -
          210 * finiteCoefficient p ((i + 1) * p - 2) +
          266 * finiteCoefficient p ((i + 1) * p - 3)) := by
  exact fiveInterpolation_eq_sum (weightedFiniteCoefficient p)

noncomputable def shiftedRisingPolynomial (r m : ℕ) : ℤ[X] :=
  (ascPochhammer ℤ m).comp (C (r : ℤ) - X)

noncomputable def weightedRisingPolynomial (n : ℕ) : ℤ[X] :=
  25 * shiftedRisingPolynomial 1 (6 * n) -
    210 * shiftedRisingPolynomial 2 (6 * n) +
    266 * shiftedRisingPolynomial 3 (6 * n)

theorem shiftedRising_eval (r m : ℕ) (x : ℤ) :
    (shiftedRisingPolynomial r m).eval x =
      (ascPochhammer ℤ m).eval ((r : ℤ) - x) := by
  simp [shiftedRisingPolynomial, Polynomial.eval_comp]

/-- Even negative rising factorials include the zero binomial tail exactly. -/
theorem shiftedRising_eval_nat_sub (r n t : ℕ) (hrt : r ≤ t) :
    (shiftedRisingPolynomial r (6 * n)).eval (t : ℤ) =
      ((6 * n).factorial : ℤ) * (Nat.choose (t - r) (6 * n) : ℤ) := by
  rw [shiftedRising_eval]
  have hneg : (r : ℤ) - t = -((t - r : ℕ) : ℤ) := by
    rw [Nat.cast_sub hrt]
    ring
  rw [hneg, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  have heven : (-1 : ℤ) ^ (6 * n) = 1 := by
    rw [show 6 * n = 2 * (3 * n) by omega, pow_mul]
    norm_num
  rw [heven, one_mul]

theorem weightedRising_eval_zero (n : ℕ) :
    (weightedRisingPolynomial n).eval 0 =
      9 * ((6 * n).factorial : ℤ) * (weightNat n : ℤ) := by
  have h1 : (ascPochhammer ℤ (6 * n)).eval 1 = ((6 * n).factorial : ℤ) :=
    ascPochhammer_eval_one ℤ (6 * n)
  have h2 : (ascPochhammer ℤ (6 * n)).eval 2 =
      ((6 * n).factorial : ℤ) * (6 * (n : ℤ) + 1) := by
    have h := factorial_mul_ascPochhammer ℤ 1 (6 * n)
    norm_num only [Nat.factorial_one, Nat.cast_one, one_mul] at h
    rw [show 1 + 6 * n = 6 * n + 1 by omega, Nat.factorial_succ] at h
    push_cast at h
    simpa [mul_comm] using h
  have h3 : 2 * (ascPochhammer ℤ (6 * n)).eval 3 =
      ((6 * n).factorial : ℤ) * (6 * (n : ℤ) + 1) * (6 * (n : ℤ) + 2) := by
    have h := factorial_mul_ascPochhammer ℤ 2 (6 * n)
    norm_num only [Nat.factorial_two, Nat.cast_ofNat] at h
    rw [show 2 + 6 * n = 6 * n + 2 by omega,
      Nat.factorial_succ, Nat.factorial_succ] at h
    push_cast at h
    simpa [add_assoc, mul_assoc, mul_comm, mul_left_comm] using h
  simp only [weightedRisingPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, shiftedRising_eval, sub_zero,
    Nat.cast_one, Nat.cast_ofNat]
  rw [h1, h2]
  calc
    25 * ((6 * n).factorial : ℤ) -
        210 * (((6 * n).factorial : ℤ) * (6 * (n : ℤ) + 1)) +
        266 * (ascPochhammer ℤ (6 * n)).eval 3 =
      ((6 * n).factorial : ℤ) *
        (25 - 210 * (6 * (n : ℤ) + 1) +
          133 * (6 * (n : ℤ) + 1) * (6 * (n : ℤ) + 2)) := by
            linear_combination 133 * h3
    _ = 9 * ((6 * n).factorial : ℤ) * (weightNat n : ℤ) := by
      simp only [weightNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

theorem weightedRising_eval_point (n p j : ℕ) (hp7 : 7 ≤ p) (hj : 1 ≤ j) :
    (weightedRisingPolynomial n).eval ((j : ℤ) * p) =
      (n.factorial : ℤ) ^ 6 * (coefficientNat n : ℤ) * weightedBinomial p n j := by
  have hpt : 3 ≤ j * p := by
    have := Nat.mul_le_mul_right p hj
    omega
  have h1 := shiftedRising_eval_nat_sub 1 n (j * p) (by omega)
  have h2 := shiftedRising_eval_nat_sub 2 n (j * p) (by omega)
  have h3 := shiftedRising_eval_nat_sub 3 n (j * p) hpt
  have hf : ((6 * n).factorial : ℤ) =
      (coefficientNat n : ℤ) * (n.factorial : ℤ) ^ 6 := by
    exact_mod_cast (coefficient_factorial_identity n).symm
  simp only [weightedRisingPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  rw [← Nat.cast_mul, h1, h2, h3, hf]
  simp only [weightedBinomial]
  ring

def interpolationIntegerDifference (p n : ℕ) : ℤ :=
  (coefficientNat n : ℤ) *
    (fiveInterpolation (weightedBinomial p n) - 9 * (weightNat n : ℤ))

theorem interpolation_integer_difference_dvd (p n : ℕ)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hn : n < p) :
    (p : ℤ) ^ 5 ∣ interpolationIntegerDifference p n := by
  have h0 := weightedRising_eval_zero n
  have h1 := weightedRising_eval_point n p 1 hp7 (by decide)
  have h2 := weightedRising_eval_point n p 2 hp7 (by decide)
  have h3 := weightedRising_eval_point n p 3 hp7 (by decide)
  have h4 := weightedRising_eval_point n p 4 hp7 (by decide)
  have h5 := weightedRising_eval_point n p 5 hp7 (by decide)
  have hf : ((6 * n).factorial : ℤ) =
      (coefficientNat n : ℤ) * (n.factorial : ℤ) ^ 6 := by
    exact_mod_cast (coefficient_factorial_identity n).symm
  have heq : integerFiveDifference (weightedRisingPolynomial n) p =
      (n.factorial : ℤ) ^ 6 * interpolationIntegerDifference p n := by
    simp only [integerFiveDifference, fiveInterpolation]
    rw [h1, h2, h3, h4, h5, h0, hf]
    simp only [interpolationIntegerDifference, fiveInterpolation]
    ring
  have hd := integer_five_difference_dvd (weightedRisingPolynomial n) p
  rw [heq] at hd
  have hcop : IsCoprime ((p : ℤ) ^ 5) ((n.factorial : ℤ) ^ 6) := by
    simpa only [Nat.cast_pow] using
      ((hp.coprime_factorial_of_lt hn).pow_left 5 |>.pow_right 6).cast (R := ℤ)
  exact hcop.dvd_of_dvd_mul_left hd

theorem weightedFiniteCoefficient_eq_sum (p j : ℕ) :
    weightedFiniteCoefficient p j =
      ∑ n ∈ Finset.range p,
        (coefficientNat n : ℚ) * (weightedBinomial p n j : ℚ) /
          (10 : ℚ) ^ (6 * n) := by
  simp only [weightedFiniteCoefficient, finiteCoefficient, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [weightedBinomial, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat]
  ring

theorem fifteen_difference_eq_sum (p : ℕ) :
    fifteenCoefficientCombination p - 9 * literalSum p =
      ∑ n ∈ Finset.range p,
        (interpolationIntegerDifference p n : ℚ) / (10 : ℚ) ^ (6 * n) := by
  change fiveInterpolation (fun j => weightedFiniteCoefficient p j) -
    9 * literalSum p = _
  simp_rw [weightedFiniteCoefficient_eq_sum]
  rw [fiveInterpolation_sum]
  simp only [literalSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [literal_term_eq_coefficient]
  simp only [interpolationIntegerDifference, fiveInterpolation, Int.cast_mul,
    Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  ring

def interpolationClearedDifference (p : ℕ) : ℤ :=
  ∑ n ∈ Finset.range p,
    interpolationIntegerDifference p n * (10 : ℤ) ^ (6 * (p - 1 - n))

theorem interpolation_cleared_difference_dvd (p : ℕ)
    (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ℤ) ^ 5 ∣ interpolationClearedDifference p := by
  unfold interpolationClearedDifference
  apply Finset.dvd_sum
  intro n hn
  exact dvd_mul_of_dvd_left
    (interpolation_integer_difference_dvd p n hp hp7 (Finset.mem_range.mp hn)) _

theorem fifteen_difference_eq_cleared (p : ℕ) (hp : 0 < p) :
    fifteenCoefficientCombination p - 9 * literalSum p =
      (interpolationClearedDifference p : ℚ) / (clearingDenominatorNat p : ℚ) := by
  rw [fifteen_difference_eq_sum]
  simp only [interpolationClearedDifference]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : n < p := Finset.mem_range.mp hn
  have hexp : 6 * (p - 1) = 6 * n + 6 * (p - 1 - n) := by omega
  have hpow : (clearingDenominatorNat p : ℚ) =
      (10 : ℚ) ^ (6 * n) * (10 : ℚ) ^ (6 * (p - 1 - n)) := by
    simp [clearingDenominatorNat, hexp, pow_add]
  rw [hpow]
  field_simp

/-- The complete finite interpolation endpoint; it does not evaluate the literal sum. -/
theorem finite_interpolation_congruence (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    RationalCongruent p 5 (fifteenCoefficientCombination p) (9 * literalSum p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdiff := fifteen_difference_eq_cleared p hp.pos
  have hdvd := interpolation_cleared_difference_dvd p hp hp7
  have hQ := clearing_denominator_ne_zero p
  have hvQ : padicValRat p (clearingDenominatorNat p : ℚ) = 0 := by
    simp only [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (clearing_denominator_unit p hp hp7), Nat.cast_zero]
  by_cases hD : interpolationClearedDifference p = 0
  · left
    apply sub_eq_zero.mp
    rw [hdiff, hD]
    simp
  · right
    have hDr : (interpolationClearedDifference p : ℚ) ≠ 0 := by exact_mod_cast hD
    rw [hdiff, padicValRat.div hDr hQ, hvQ, sub_zero, padicValRat.of_int]
    have hval : 5 ≤ padicValInt p (interpolationClearedDifference p) :=
      ((padicValInt_dvd_iff 5 (interpolationClearedDifference p)).mp hdvd).resolve_left hD
    exact_mod_cast hval

end WPReview
