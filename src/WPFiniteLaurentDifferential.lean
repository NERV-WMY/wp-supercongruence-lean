import WPFiniteJCarrier
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

open scoped LaurentPolynomial Polynomial Pointwise

namespace WPFiniteLaurentDifferential

open LaurentPolynomial

variable {K : Type*} [Field K]

/-- Literal derivative of the full finite Laurent coefficient support. -/
noncomputable def D : K[T;T⁻¹] →ₗ[K] K[T;T⁻¹] :=
  (Finsupp.linearCombination K (fun n : ℤ => C (n : K) * T (n - 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem D_monomial (a : K) (n : ℤ) :
    D (C a * T n) = C (a * (n : K)) * T (n - 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination K _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul, ← mul_assoc, ← map_mul]

theorem D_coeff (P : K[T;T⁻¹]) (j : ℤ) :
    (D P).coeff j = ((j + 1 : ℤ) : K) * P.coeff (j + 1) := by
  have hc (c : K) (n k : ℤ) : (C c * T n).coeff k = if n = k then c else 0 := by
    rw [← single_eq_C_mul_T]
    exact Finsupp.single_apply
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
    ring
  | C_mul_T n c =>
    rw [D_monomial, hc, hc]
    by_cases hn : n = j + 1
    · subst n
      simp only [add_sub_cancel_right, if_true]
      ring
    · have hnj : n - 1 ≠ j := by omega
      simp only [if_neg hn, if_neg hnj, mul_zero]

theorem monomial_mul (a b : K) (n m : ℤ) :
    (C a * T n) * (C b * T m) = C (a * b) * T (n + m) := by
  rw [map_mul, T_add]
  ring

theorem D_mul (P Q : K[T;T⁻¹]) : D (P * Q) = D P * Q + P * D Q := by
  induction P using LaurentPolynomial.induction_on' with
  | add P1 P2 h1 h2 =>
    rw [add_mul, map_add, h1, h2, map_add]
    ring
  | C_mul_T n a =>
    induction Q using LaurentPolynomial.induction_on' with
    | add Q1 Q2 h1 h2 =>
      rw [mul_add, map_add, h1, h2, map_add]
      ring
    | C_mul_T m b =>
      rw [monomial_mul, D_monomial, D_monomial, D_monomial,
        monomial_mul, monomial_mul]
      rw [show n - 1 + m = n + m - 1 by omega,
        show n + (m - 1) = n + m - 1 by omega]
      rw [← add_mul, ← map_add]
      congr 2
      push_cast
      ring

theorem D_C (a : K) : D (C a) = 0 := by
  simpa using D_monomial a 0

theorem D_C_mul (a : K) (P : K[T;T⁻¹]) : D (C a * P) = C a * D P := by
  rw [D_mul, D_C, zero_mul, zero_add]

theorem D_half_square (P : K[T;T⁻¹]) (h2 : (2 : K) ≠ 0) :
    D (C (1 / 2 : K) * P ^ 2) = P * D P := by
  have hc : C (1 / 2 : K) * 2 = (1 : K[T;T⁻¹]) := by
    change C (1 / 2 : K) * C (2 : K) = 1
    rw [← map_mul, one_div_mul_cancel h2, map_one]
  rw [pow_two, D_C_mul, D_mul]
  linear_combination P * D P * hc

theorem D_toLaurent (P : K[X]) : D P.toLaurent = P.derivative.toLaurent := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [Polynomial.toLaurent_C_mul_T, D_monomial]
    cases n with
    | zero => simp
    | succ n =>
      rw [Polynomial.derivative_monomial, Polynomial.toLaurent_C_mul_T]
      apply congrArg₂ (fun a b => C a * T b)
      · push_cast
        ring
      · omega

theorem D_invert (P : K[T;T⁻¹]) :
    D (invert P) = -(T (-2) * invert (D P)) := by
  ext j
  rw [D_coeff, invert_apply]
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-2) j (invert (D P))
  simp only [map_one, one_mul, invert_apply] at he
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, he, D_coeff]
  rw [show -(j - -2) + 1 = -(j + 1) by omega]
  push_cast
  ring

theorem D_frobenius_shift (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : K[T;T⁻¹]) (n : ℤ) (hn : (p : ℤ) ∣ n) :
    D (T n * P) = T n * D P := by
  have hnp : (n : K) = 0 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk, Int.cast_mul]
    have hp : ((p : ℤ) : K) = 0 := by
      simpa only [Int.cast_natCast] using (CharP.cast_eq_zero K p)
    rw [hp, zero_mul]
  have he : D (T n : K[T;T⁻¹]) = 0 := by
    have hm := D_monomial (1 : K) n
    simpa only [map_one, one_mul, hnp, map_zero, zero_mul] using hm
  rw [D_mul, he, zero_mul, zero_add]

/-- A literal upper coefficient bound, including every integer exponent. -/
def Above (P : K[T;T⁻¹]) (b : ℤ) : Prop := ∀ j : ℤ, b < j → P.coeff j = 0

theorem Above_mono {P : K[T;T⁻¹]} {a b : ℤ} (hP : Above P a) (hab : a ≤ b) : Above P b := by
  intro j hj
  exact hP j (by omega)

theorem Above_add {P Q : K[T;T⁻¹]} {a b : ℤ} (hP : Above P a) (hQ : Above Q b) :
    Above (P + Q) (max a b) := by
  intro j hj
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP j (by omega), hQ j (by omega), add_zero]

theorem Above_sub {P Q : K[T;T⁻¹]} {a b : ℤ} (hP : Above P a) (hQ : Above Q b) :
    Above (P - Q) (max a b) := by
  intro j hj
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hP j (by omega), hQ j (by omega), sub_self]

theorem Above_mul {P Q : K[T;T⁻¹]} {a b : ℤ} (hP : Above P a) (hQ : Above Q b) :
    Above (P * Q) (a + b) := by
  classical
  intro j hj
  by_contra hz
  have hm : j ∈ (P * Q).coeff.support := Finsupp.mem_support_iff.mpr hz
  have hs : j ∈ P.coeff.support + Q.coeff.support :=
    AddMonoidAlgebra.support_coeff_mul_subset P Q hm
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.mem_add.mp hs
  have hia : i ≤ a := by
    by_contra hi'
    exact (Finsupp.mem_support_iff.mp hi) (hP i (by omega))
  have hkb : k ≤ b := by
    by_contra hk'
    exact (Finsupp.mem_support_iff.mp hk) (hQ k (by omega))
  omega

theorem Above_monomial (c : K) (n : ℤ) : Above (C c * T n) n := by
  intro j hj
  rw [← single_eq_C_mul_T]
  change Finsupp.single n c j = 0
  rw [Finsupp.single_apply, if_neg (by omega : n ≠ j)]

theorem Above_C (c : K) : Above (C c) 0 := by
  simpa only [T_zero, mul_one] using Above_monomial c 0

theorem Above_C_mul {P : K[T;T⁻¹]} {b : ℤ} (hP : Above P b) (c : K) :
    Above (C c * P) b := by
  simpa only [zero_add] using Above_mul (Above_C c) hP

theorem Above_neg {P : K[T;T⁻¹]} {b : ℤ} (hP : Above P b) : Above (-P) b := by
  intro j hj
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hP j hj, neg_zero]

theorem Above_pow {P : K[T;T⁻¹]} {b : ℤ} (hP : Above P b) (n : ℕ) :
    Above (P ^ n) ((n : ℤ) * b) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, map_one] using Above_C (1 : K)
  | succ n hn =>
    rw [pow_succ]
    have he := Above_mul hn hP
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using he

theorem Above_shift {P : K[T;T⁻¹]} {b : ℤ} (hP : Above P b) (n : ℤ) :
    Above (T n * P) (n + b) := by
  simpa only [map_one, one_mul] using Above_mul (Above_monomial (1 : K) n) hP

theorem Above_toLaurent (P : K[X]) (b : ℕ) (hP : P.natDegree ≤ b) : Above P.toLaurent (b : ℤ) := by
  intro j hj
  exact WPFiniteJCarrier.toLaurent_coeff_outside P j (Or.inr (by omega))

theorem Above_invert_toLaurent (P : K[X]) : Above (invert P.toLaurent) 0 := by
  intro j hj
  rw [invert_apply]
  exact WPFiniteJCarrier.toLaurent_coeff_outside P (-j) (Or.inl (by omega))

theorem Above_D {P : K[T;T⁻¹]} {b : ℤ} (hP : Above P b) : Above (D P) (b - 1) := by
  intro j hj
  rw [D_coeff, hP (j + 1) (by omega), mul_zero]

theorem integer_unit_in_band (p : ℕ) [Fact p.Prime] [CharP K p]
    (j : ℤ) (hj : 0 < j ∧ j < p) : (j : K) ≠ 0 := by
  have hjn : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
  have hnat : (j.toNat : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j.toNat
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (fun z : ℤ => (z : K)) hjn
  simp only [Int.cast_natCast] at hc
  rw [← hc]
  exact hnat

theorem integer_shift_unit (p : ℕ) [Fact p.Prime] [CharP K p]
    (j : ℤ) (k : ℕ) (hj : 0 < j - (k : ℤ) * p ∧ j - (k : ℤ) * p < p) :
    (j : K) ≠ 0 := by
  have hu := integer_unit_in_band (K := K) p (j - (k : ℤ) * p) hj
  have hc : ((j - (k : ℤ) * p : ℤ) : K) = (j : K) := by
    push_cast
    rw [CharP.cast_eq_zero K p]
    ring
  rw [hc] at hu
  exact hu

/-- Complete unit-band removal; the derivative-invisible 2p slot is deliberately retained. -/
theorem whole_high_band (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[T;T⁻¹]) (hP : Above P (3 * (p : ℤ) - 3))
    (hDP : Above (D P) (2 * (p : ℤ) - 4)) :
    Above P (2 * (p : ℤ)) ∧ P.coeff (2 * (p : ℤ) - 2) = 0 ∧
      P.coeff (2 * (p : ℤ) - 1) = 0 := by
  have hunit_zero (j : ℤ) (hju : (j : K) ≠ 0) (hj : 2 * (p : ℤ) - 4 < j - 1) :
      P.coeff j = 0 := by
    have he := hDP (j - 1) hj
    rw [D_coeff, show j - 1 + 1 = j by omega] at he
    exact (mul_eq_zero.mp he).resolve_left hju
  constructor
  · intro j hj
    by_cases htop : 3 * (p : ℤ) - 3 < j
    · exact hP j htop
    · exact hunit_zero j (integer_shift_unit p j 2 (by omega)) (by omega)
  · constructor
    · exact hunit_zero _ (integer_shift_unit p _ 1 (by omega)) (by omega)
    · exact hunit_zero _ (integer_shift_unit p _ 1 (by omega)) (by omega)

end WPFiniteLaurentDifferential
