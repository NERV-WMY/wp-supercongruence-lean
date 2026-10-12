import WPCartierFinite.Basic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

open scoped BigOperators
open Polynomial

namespace WPCartierFinite

abbrev SixExponent := Fin 6 → ℕ
abbrev LowVector := Fin 5 → ℚ

/-- Rational p-integrality uses the actual reduced denominator. -/
def pIntegral (p : ℕ) (q : ℚ) : Prop := ¬ p ∣ q.den

theorem pIntegral_of_fraction (p : ℕ) (n : ℤ) (d : ℕ) (hd : ¬ p ∣ d) :
    pIntegral p ((n : ℚ) / (d : ℚ)) := by
  intro h
  have hden : ((n : ℚ) / (d : ℚ)).den ∣ d := by
    have hz := Rat.den_dvd n (d : ℤ)
    rw [Rat.divInt_eq_div] at hz
    exact_mod_cast hz
  exact hd (h.trans hden)

theorem pIntegral_intCast (p : ℕ) (hp : p.Prime) (n : ℤ) :
    pIntegral p (n : ℚ) := by
  simp only [pIntegral, Rat.den_intCast]
  exact hp.not_dvd_one

theorem pIntegral_natCast (p : ℕ) (hp : p.Prime) (n : ℕ) :
    pIntegral p (n : ℚ) := by
  simpa using pIntegral_intCast p hp (n : ℤ)

theorem pIntegral_add (p : ℕ) (hp : p.Prime) {q r : ℚ}
    (hq : pIntegral p q) (hr : pIntegral p r) : pIntegral p (q + r) := by
  intro h
  exact (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd q r))).elim hq hr

theorem pIntegral_mul (p : ℕ) (hp : p.Prime) {q r : ℚ}
    (hq : pIntegral p q) (hr : pIntegral p r) : pIntegral p (q * r) := by
  intro h
  exact (hp.dvd_mul.mp (h.trans (Rat.mul_den_dvd q r))).elim hq hr

theorem pIntegral_pow (p : ℕ) (hp : p.Prime) {q : ℚ}
    (hq : pIntegral p q) (n : ℕ) : pIntegral p (q ^ n) := by
  induction n with
  | zero => simpa using pIntegral_natCast p hp 1
  | succ n ih => simpa [pow_succ] using pIntegral_mul p hp ih hq

theorem pIntegral_sum (p : ℕ) (hp : p.Prime) {α : Type*}
    (s : Finset α) (f : α → ℚ) (hf : ∀ a ∈ s, pIntegral p (f a)) :
    pIntegral p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pIntegral_natCast p hp 0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact pIntegral_add p hp (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

def exponentDegree (a : SixExponent) : ℕ := ∑ i, a i

noncomputable def lowPoleIntegerPolynomial (a : SixExponent) (k : ℕ) : ℤ[X] :=
  (∏ i, ∏ j ∈ Finset.range (a i), (X - C (6 * (j : ℤ)))) *
    ∏ t ∈ Finset.range (k - exponentDegree a), (X + C ((t : ℤ) + 1))

noncomputable def lowPolePolynomial (a : SixExponent) (k : ℕ) : ℚ[X] :=
  (lowPoleIntegerPolynomial a k).map (Int.castRingHom ℚ)

def gammaBInteger (d : ℕ) : Fin 5 → ℤ :=
  match d with
  | 0 => ![1, 0, 0, 0, 0]
  | 1 => ![-1, 1, 0, 0, 0]
  | 2 => ![1, -3, 1, 0, 0]
  | 3 => ![-1, 7, -6, 1, 0]
  | 4 => ![1, -15, 25, -10, 1]
  | _ => 0

def gammaB (d : ℕ) : LowVector := fun i => (gammaBInteger d i : ℚ)

def gammaLambda (v : LowVector) : ℚ := ∑ i, (i.val.factorial : ℚ) * v i
def gammaLambdaWeights : LowVector := ![1, 1, 2, 6, 24]
def scalarRow (v : LowVector) : ℚ := ∑ i, v i
def factorialDiagonal (v : LowVector) : LowVector :=
  fun i => (i.val.factorial : ℚ) * v i

noncomputable def lowPoleVector (a : SixExponent) (k : ℕ) : LowVector :=
  fun i => ((5 : ℚ) / 3) ^ exponentDegree a / (k.factorial : ℚ) *
    ∑ d ∈ Finset.range (k + 1), (lowPolePolynomial a k).coeff d * gammaB d i

theorem lowPolePolynomial_formula (a : SixExponent) (k : ℕ) :
    lowPolePolynomial a k =
      (∏ i, ∏ j ∈ Finset.range (a i), (X - C (6 * (j : ℚ)))) *
        ∏ t ∈ Finset.range (k - exponentDegree a), (X + C ((t : ℚ) + 1)) := by
  simp only [lowPolePolynomial, lowPoleIntegerPolynomial, Polynomial.map_mul,
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat, Int.cast_add, Int.cast_one]

theorem lowPolePolynomial_degree (a : SixExponent) (k : ℕ)
    (ha : exponentDegree a ≤ k) : (lowPolePolynomial a k).natDegree ≤ k := by
  rw [lowPolePolynomial_formula]
  have hinner (i : Fin 6) :
      (∏ j ∈ Finset.range (a i), (X - C (6 * (j : ℚ)))).natDegree ≤ a i := by
    calc
      _ ≤ ∑ j ∈ Finset.range (a i), (X - C (6 * (j : ℚ))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = a i := by simp only [Polynomial.natDegree_X_sub_C]; simp
  have hfirst :
      (∏ i : Fin 6, ∏ j ∈ Finset.range (a i),
        (X - C (6 * (j : ℚ)))).natDegree ≤ exponentDegree a := by
    exact (Polynomial.natDegree_prod_le Finset.univ _).trans
      (Finset.sum_le_sum (fun i _ => hinner i))
  have hlast :
      (∏ t ∈ Finset.range (k - exponentDegree a),
        (X + C ((t : ℚ) + 1))).natDegree ≤ k - exponentDegree a := by
    calc
      _ ≤ ∑ t ∈ Finset.range (k - exponentDegree a),
          (X + C ((t : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
      _ = k - exponentDegree a := by simp only [Polynomial.natDegree_X_add_C]; simp
  exact (Polynomial.natDegree_mul_le ..).trans
    ((Nat.add_le_add hfirst hlast).trans (by omega))

theorem exponentDegree_zero : exponentDegree 0 = 0 := by simp [exponentDegree]

theorem lowPoleIntegerPolynomial_eval_zero_nonzero (a : SixExponent) (k : ℕ)
    (ha : a ≠ 0) : (lowPoleIntegerPolynomial a k).eval 0 = 0 := by
  have hi : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨i, hi⟩ := hi
  have hin : 0 ∈ Finset.range (a i) := Finset.mem_range.mpr (Nat.pos_of_ne_zero hi)
  have hinner : (∏ j ∈ Finset.range (a i), (0 - 6 * (j : ℤ))) = 0 := by
    exact Finset.prod_eq_zero hin (by simp)
  have houter : (∏ i, ∏ j ∈ Finset.range (a i), (0 - 6 * (j : ℤ))) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ i) hinner
  simp only [lowPoleIntegerPolynomial, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [houter, zero_mul]

theorem lowPoleIntegerPolynomial_eval_zero_zero (k : ℕ) :
    (lowPoleIntegerPolynomial 0 k).eval 0 = (k.factorial : ℤ) := by
  simp only [lowPoleIntegerPolynomial, Pi.zero_apply, Finset.range_zero,
    Finset.prod_empty, Finset.prod_const_one, one_mul, exponentDegree_zero,
    Nat.sub_zero, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, zero_add]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring

theorem lowPolePolynomial_eval_zero_nonzero (a : SixExponent) (k : ℕ)
    (ha : a ≠ 0) : (lowPolePolynomial a k).eval 0 = 0 := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, lowPolePolynomial,
    Polynomial.coeff_map, Int.coe_castRingHom, Int.cast_zero] using
    congrArg (fun z : ℤ => (z : ℚ))
      (lowPoleIntegerPolynomial_eval_zero_nonzero a k ha)

theorem lowPolePolynomial_eval_zero_zero (k : ℕ) :
    (lowPolePolynomial 0 k).eval 0 = (k.factorial : ℚ) := by
  simpa only [← Polynomial.coeff_zero_eq_eval_zero, lowPolePolynomial,
    Polynomial.coeff_map, Int.coe_castRingHom, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ℚ)) (lowPoleIntegerPolynomial_eval_zero_zero k)

theorem gammaLambda_gammaB (d : ℕ) :
    gammaLambda (gammaB d) = if d = 0 then 1 else 0 := by
  rcases d with _ | _ | _ | _ | _ | d
  all_goals simp only [gammaLambda, gammaB, gammaBInteger]
  all_goals norm_num [Fin.sum_univ_succ]

theorem gammaLambda_add (u v : LowVector) :
    gammaLambda (u + v) = gammaLambda u + gammaLambda v := by
  simp [gammaLambda, mul_add, Finset.sum_add_distrib]

theorem gammaLambda_smul (c : ℚ) (v : LowVector) :
    gammaLambda (c • v) = c * gammaLambda v := by
  simp only [gammaLambda, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gammaLambda_sum {α : Type*} (s : Finset α) (v : α → LowVector) :
    gammaLambda (∑ a ∈ s, v a) = ∑ a ∈ s, gammaLambda (v a) := by
  simp only [gammaLambda, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem scalarRow_factorialDiagonal (v : LowVector) :
    scalarRow (factorialDiagonal v) = gammaLambda v := rfl

theorem gammaLambda_lowPoleVector (a : SixExponent) (k : ℕ) :
    gammaLambda (lowPoleVector a k) = if a = 0 then 1 else 0 := by
  have hv : lowPoleVector a k =
      (((5 : ℚ) / 3) ^ exponentDegree a / (k.factorial : ℚ)) •
        ∑ d ∈ Finset.range (k + 1), (lowPolePolynomial a k).coeff d • gammaB d := by
    ext i
    simp [lowPoleVector]
  rw [hv, gammaLambda_smul, gammaLambda_sum]
  simp only [gammaLambda_smul, gammaLambda_gammaB, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.zero_lt_succ, if_true,
    Polynomial.coeff_zero_eq_eval_zero]
  by_cases ha : a = 0
  · subst a
    simp [exponentDegree_zero, lowPolePolynomial_eval_zero_zero,
      Nat.factorial_ne_zero]
  · simp [ha, lowPolePolynomial_eval_zero_nonzero a k ha]

def markedVector : LowVector := ![25 / 9, -210 / 9, 266 / 9, 0, 0]

theorem scalarRow_markedVector : scalarRow markedVector = 9 := by
  norm_num [scalarRow, markedVector, Fin.sum_univ_succ]

theorem lowPolePolynomial_coeff_integer (a : SixExponent) (k d : ℕ) :
    (lowPolePolynomial a k).coeff d =
      ((lowPoleIntegerPolynomial a k).coeff d : ℚ) := by
  simp [lowPolePolynomial]

theorem lowPoleVector_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : SixExponent) (k : ℕ) (hk : k ≤ 4) (i : Fin 5) :
    pIntegral p (lowPoleVector a k i) := by
  have hthree : ¬ p ∣ 3 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  have hklt : k < p := by omega
  have hkfac : ¬ p ∣ k.factorial :=
    hp.coprime_iff_not_dvd.mp (hp.coprime_factorial_of_lt hklt)
  have hscale : pIntegral p (((5 : ℚ) / 3) ^ exponentDegree a /
      (k.factorial : ℚ)) := by
    rw [show ((5 : ℚ) / 3) ^ exponentDegree a / (k.factorial : ℚ) =
      ((5 : ℚ) / 3) ^ exponentDegree a * (1 / (k.factorial : ℚ)) by ring]
    exact pIntegral_mul p hp
      (pIntegral_pow p hp (pIntegral_of_fraction p 5 3 hthree) _)
      (pIntegral_of_fraction p 1 k.factorial hkfac)
  unfold lowPoleVector
  apply pIntegral_mul p hp hscale
  apply pIntegral_sum p hp
  intro d hd
  rw [lowPolePolynomial_coeff_integer]
  exact pIntegral_mul p hp (pIntegral_intCast p hp _)
    (pIntegral_intCast p hp _)

theorem factorialDiagonal_integral (p : ℕ) (hp : p.Prime)
    (v : LowVector) (hv : ∀ i, pIntegral p (v i)) (i : Fin 5) :
    pIntegral p (factorialDiagonal v i) := by
  exact pIntegral_mul p hp (pIntegral_natCast p hp _) (hv i)

noncomputable def lowPoleProjection (k : ℕ) : (SixExponent →₀ ℚ) →ₗ[ℚ] LowVector :=
  Finsupp.linearCombination ℚ (fun a => lowPoleVector a k)

theorem lowPoleProjection_support_formula (k : ℕ) (P : SixExponent →₀ ℚ)
    (i : Fin 5) :
    lowPoleProjection k P i =
      ∑ a ∈ P.support, P a * lowPoleVector a k i := by
  simp [lowPoleProjection, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Explicit finite array columns formed from polynomial coefficient supports. -/
noncomputable def finiteCoefficientArray (p : ℕ)
    (T : Fin 5 → Fin 5 → SixExponent →₀ ℚ) : Fin 5 → LowVector :=
  fun r => factorialDiagonal (fun i =>
    ∑ k : Fin 5, (p : ℚ) ^ k.val *
      ∑ a ∈ (T k r).support, (T k r) a * lowPoleVector a k.val i)

theorem scalarRow_finiteCoefficientArray (p : ℕ)
    (T : Fin 5 → Fin 5 → SixExponent →₀ ℚ) (r : Fin 5) :
    scalarRow (finiteCoefficientArray p T r) =
      ∑ k : Fin 5, (p : ℚ) ^ k.val * (T k r) 0 := by
  have hv : (fun i => ∑ k : Fin 5, (p : ℚ) ^ k.val *
      ∑ a ∈ (T k r).support, (T k r) a * lowPoleVector a k.val i) =
      ∑ k : Fin 5, (p : ℚ) ^ k.val •
        ∑ a ∈ (T k r).support, (T k r) a • lowPoleVector a k.val := by
    ext i
    simp
  rw [finiteCoefficientArray, scalarRow_factorialDiagonal, hv, gammaLambda_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gammaLambda_smul, gammaLambda_sum]
  simp only [gammaLambda_smul, gammaLambda_lowPoleVector, mul_ite, mul_one, mul_zero]
  congr 1
  rw [Finset.sum_ite_eq']
  by_cases h : (T k r) 0 = 0
  · simp [h]
  · simp [Finsupp.mem_support_iff, h]

theorem finiteCoefficientArray_integral (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (T : Fin 5 → Fin 5 → SixExponent →₀ ℚ)
    (hT : ∀ k r a, pIntegral p ((T k r) a)) (r i : Fin 5) :
    pIntegral p (finiteCoefficientArray p T r i) := by
  apply factorialDiagonal_integral p hp
  intro i
  apply pIntegral_sum p hp
  intro k hk
  apply pIntegral_mul p hp (pIntegral_pow p hp (pIntegral_natCast p hp p) _)
  apply pIntegral_sum p hp
  intro a ha
  exact pIntegral_mul p hp (hT k r a)
    (lowPoleVector_integral p hp hp7 a k.val (by omega) i)

theorem finiteCoefficientArray_projection_formula (p : ℕ)
    (T : Fin 5 → Fin 5 → SixExponent →₀ ℚ) (r : Fin 5) :
    finiteCoefficientArray p T r = factorialDiagonal
      (∑ k : Fin 5, (p : ℚ) ^ k.val • lowPoleProjection k.val (T k r)) := by
  ext i
  simp [finiteCoefficientArray, factorialDiagonal, lowPoleProjection_support_formula]

noncomputable def arrayMarkedScalar (C : Fin 5 → LowVector) : ℚ :=
  scalarRow (fun i => ∑ r, C r i * markedVector r)

def coefficientMatrix (C : Fin 5 → LowVector) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i r => C r i

def factorialMatrix : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal (fun i => (i.val.factorial : ℚ))

theorem allOnes_factorialMatrix :
    Matrix.vecMul (1 : LowVector) factorialMatrix =
      fun i => (i.val.factorial : ℚ) := by
  ext i
  simp [factorialMatrix, Matrix.vecMul_diagonal]

theorem factorialMatrix_integral (p : ℕ) (hp : p.Prime) (i j : Fin 5) :
    pIntegral p (factorialMatrix i j) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa [factorialMatrix] using pIntegral_natCast p hp i.val.factorial
  · simpa [factorialMatrix, Matrix.diagonal, hij] using pIntegral_natCast p hp 0

theorem arrayMarkedScalar_matrix (C : Fin 5 → LowVector) :
    arrayMarkedScalar C =
      dotProduct (1 : LowVector) ((coefficientMatrix C).mulVec markedVector) := by
  simp [arrayMarkedScalar, scalarRow, coefficientMatrix, Matrix.mulVec, dotProduct]

theorem arrayMarkedScalar_eq (C : Fin 5 → LowVector) :
    9 * arrayMarkedScalar C =
      25 * scalarRow (C 0) - 210 * scalarRow (C 1) + 266 * scalarRow (C 2) := by
  simp only [arrayMarkedScalar, scalarRow, Fin.sum_univ_succ, markedVector,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem finiteCoefficientArray_markedScalar (p : ℕ)
    (T : Fin 5 → Fin 5 → SixExponent →₀ ℚ) :
    9 * arrayMarkedScalar (finiteCoefficientArray p T) =
      25 * (∑ k : Fin 5, (p : ℚ) ^ k.val * (T k 0) 0) -
      210 * (∑ k : Fin 5, (p : ℚ) ^ k.val * (T k 1) 0) +
      266 * (∑ k : Fin 5, (p : ℚ) ^ k.val * (T k 2) 0) := by
  rw [arrayMarkedScalar_eq]
  simp only [scalarRow_finiteCoefficientArray]

theorem gammaLambda_explicit (v : LowVector) :
    gammaLambda v = v 0 + v 1 + 2 * v 2 + 6 * v 3 + 24 * v 4 := by
  norm_num [gammaLambda, Fin.sum_univ_succ]
  change v 0 + (v 1 + (2 * v 2 + (6 * v 3 + 24 * v 4))) = _
  ring

theorem factorial_weights_literal :
    (fun i : Fin 5 => (i.val.factorial : ℚ)) = gammaLambdaWeights := by
  ext i
  fin_cases i <;> norm_num [gammaLambdaWeights]

theorem allOnes_factorialMatrix_literal :
    Matrix.vecMul (1 : LowVector) factorialMatrix = gammaLambdaWeights := by
  rw [allOnes_factorialMatrix, factorial_weights_literal]

theorem gammaLambda_dotProduct (v : LowVector) :
    gammaLambda v = dotProduct gammaLambdaWeights v := by
  rw [← factorial_weights_literal]
  rfl

theorem prime_not_dvd_nine (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ∣ 9 := by
  intro h
  have h3 : p ∣ 3 := hp.dvd_of_dvd_pow (n := 2) (by simpa using h)
  have := Nat.le_of_dvd (by decide : 0 < 3) h3
  omega

theorem lowPole_denominator_unit (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (a : SixExponent) (k : ℕ) (hk : k ≤ 4) :
    ¬ p ∣ 3 ^ exponentDegree a * k.factorial := by
  intro h
  rcases hp.dvd_mul.mp h with h3 | hf
  · have hp3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have := Nat.le_of_dvd (by decide : 0 < 3) hp3
    omega
  · exact (hp.coprime_iff_not_dvd.mp
      (hp.coprime_factorial_of_lt (by omega : k < p))) hf

theorem nine_valuation_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    padicValRat p (9 : ℚ) = 0 := by
  change padicValRat p ((9 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (prime_not_dvd_nine p hp hp7)]
  rfl

/-- Division by 9 transfers the already checked interpolation congruence. -/
theorem literalCongruence_of_arrayIdentity (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (C : Fin 5 → LowVector)
    (hC : 9 * arrayMarkedScalar C = WPReview.fifteenCoefficientCombination p) :
    WPReview.RationalCongruent p 5 (arrayMarkedScalar C) (WPReview.literalSum p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hinter := WPReview.finite_interpolation_congruence p hp hp7
  by_cases heq : arrayMarkedScalar C = WPReview.literalSum p
  · exact Or.inl heq
  · right
    have hdiff : arrayMarkedScalar C - WPReview.literalSum p ≠ 0 := sub_ne_zero.mpr heq
    have hscaled : WPReview.fifteenCoefficientCombination p -
        9 * WPReview.literalSum p =
        9 * (arrayMarkedScalar C - WPReview.literalSum p) := by rw [← hC]; ring
    rcases hinter with hequal | hval
    · exfalso
      have hzero : WPReview.fifteenCoefficientCombination p -
          9 * WPReview.literalSum p = 0 := sub_eq_zero.mpr hequal
      rw [hscaled] at hzero
      exact hdiff ((mul_eq_zero.mp hzero).resolve_left (by norm_num))
    · rwa [hscaled, padicValRat.mul (by norm_num : (9 : ℚ) ≠ 0) hdiff,
        nine_valuation_zero p hp hp7, zero_add] at hval

end WPCartierFinite
