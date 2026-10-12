import WPCartierFinite.Basic
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

namespace WPCartierFinite

/-- The inverse-trace product identity includes all admissible indices. -/
theorem binomial_product (r j k : ℕ) (hr : 1 ≤ r) (hkj : k ≤ j) :
    (r + k - 1).choose k * (r + j - 1).choose (j - k) =
      (r + j - 1).choose j * j.choose k := by
  have h₁ : r + j - 1 - (j - k) = r + k - 1 := by omega
  have h₂ : j - (j - k) = k := by omega
  have h := Nat.choose_mul (n := r + j - 1) (Nat.sub_le j k)
  rw [h₁, h₂, Nat.choose_symm hkj] at h
  exact (Nat.mul_comm _ _).trans h.symm

def alternatingKernel (N j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (min j (N - 1) + 1), (-1 : ℚ) ^ k * (j.choose k : ℚ)

theorem alternating_kernel_zero_index (N : ℕ) : alternatingKernel N 0 = 1 := by
  simp [alternatingKernel]

theorem alternating_kernel_before (N j : ℕ) (hj : 1 ≤ j) (hjN : j < N) :
    alternatingKernel N j = 0 := by
  have hmin : min j (N - 1) = j := min_eq_left (by omega)
  unfold alternatingKernel
  rw [hmin]
  exact_mod_cast (Int.alternating_sum_range_choose_of_ne (by omega : j ≠ 0))

theorem alternating_kernel_tail (N j : ℕ) (hN : 1 ≤ N) (hNj : N ≤ j) :
    alternatingKernel N j = (-1 : ℚ) ^ (N - 1) * ((j - 1).choose (N - 1) : ℚ) := by
  have hmin : min j (N - 1) = N - 1 := min_eq_right (by omega)
  have hj : j - 1 + 1 = j := by omega
  unfold alternatingKernel
  rw [hmin]
  exact_mod_cast (show (∑ k ∈ Finset.range (N - 1 + 1),
      (-1 : ℤ) ^ k * (j.choose k : ℤ)) =
      (-1 : ℤ) ^ (N - 1) * ((j - 1).choose (N - 1) : ℤ) by
    simpa only [hj] using (Int.alternating_sum_range_choose_eq_choose
      (n := j - 1) (m := N - 1)))

theorem alternating_kernel (N j : ℕ) (hN : 1 ≤ N) :
    alternatingKernel N j = if j = 0 then 1 else if j < N then 0 else
      (-1 : ℚ) ^ (N - 1) * ((j - 1).choose (N - 1) : ℚ) := by
  split_ifs with hj hjN
  · subst j; exact alternating_kernel_zero_index N
  · exact alternating_kernel_before N j (by omega) hjN
  · exact alternating_kernel_tail N j hN (by omega)

def factorialTailScalar (p k : ℕ) : ℚ := (p : ℚ) ^ k / (k.factorial : ℚ)

theorem factorial_tail_nonzero (p k : ℕ) (hp : p.Prime) :
    factorialTailScalar p k ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    (by exact_mod_cast Nat.factorial_ne_zero k)

theorem factorial_tail_valuation (p k : ℕ) (hp : p.Prime) :
    padicValRat p (factorialTailScalar p k) =
      (k : ℤ) - (WPTruncationArithmetic.factorialValuation p k : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [factorialTailScalar, padicValRat.div
    (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    (by exact_mod_cast Nat.factorial_ne_zero k), padicValRat.pow, padicValRat.self hp.one_lt]
  simp [WPTruncationArithmetic.factorialValuation]

theorem factorial_valuation_six_bound (p q : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hq : 1 ≤ q) :
    (WPTruncationArithmetic.factorialValuation p q : ℚ) ≤ ((q : ℚ) - 1) / 6 := by
  have h := WPTruncationArithmetic.factorial_valuation_growth p q hp hq
  have hpQ : (7 : ℚ) ≤ p := by exact_mod_cast hp7
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hcross := (le_div_iff₀ hpos).mp h
  have hv : (0 : ℚ) ≤ WPTruncationArithmetic.factorialValuation p q := by positivity
  nlinarith

theorem factorial_tail_lower_bound (p k : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hk : 1 ≤ k) :
    (5 * (k : ℚ) + 1) / 6 ≤ (padicValRat p (factorialTailScalar p k) : ℚ) := by
  rw [factorial_tail_valuation p k hp, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  have h := factorial_valuation_six_bound p k hp hp7 hk
  linarith

theorem factorial_tail_five (p k : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hk : 5 ≤ k) :
    5 ≤ padicValRat p (factorialTailScalar p k) := by
  have h := factorial_tail_lower_bound p k hp hp7 (by omega)
  have hkQ : (5 : ℚ) ≤ k := by exact_mod_cast hk
  have ht : (4 : ℚ) < (padicValRat p (factorialTailScalar p k) : ℚ) := by linarith
  have hi : (4 : ℤ) < padicValRat p (factorialTailScalar p k) := by exact_mod_cast ht
  omega

/-- The actual factorial-normalized inverse-trace tail coefficient. -/
def inverseTraceTailScalar (p r N j : ℕ) : ℚ :=
  (-1 : ℚ) ^ (N - 1) * (p : ℚ) ^ j * ((r + j - 1).choose j : ℚ) *
    ((j - 1).choose (N - 1) : ℚ) / ((r + j - 1).factorial : ℚ)

theorem inverse_trace_tail_nonzero (p r N j : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hNj : N ≤ j) :
    inverseTraceTailScalar p r N j ≠ 0 := by
  unfold inverseTraceTailScalar
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
          (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
      · exact_mod_cast Nat.choose_ne_zero (show j ≤ r + j - 1 by omega)
    · exact_mod_cast Nat.choose_ne_zero (show N - 1 ≤ j - 1 by omega)
  · exact_mod_cast Nat.factorial_ne_zero (r + j - 1)

theorem inverse_trace_tail_valuation (p r N j : ℕ) (hp : p.Prime)
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hNj : N ≤ j) :
    padicValRat p (inverseTraceTailScalar p r N j) =
      (j : ℤ) + (padicValNat p ((r + j - 1).choose j) : ℤ) +
        (padicValNat p ((j - 1).choose (N - 1)) : ℤ) -
        (WPTruncationArithmetic.factorialValuation p (r + j - 1) : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : (-1 : ℚ) ^ (N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpw : (p : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hc₁ : ((r + j - 1).choose j : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show j ≤ r + j - 1 by omega)
  have hc₂ : ((j - 1).choose (N - 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show N - 1 ≤ j - 1 by omega)
  rw [inverseTraceTailScalar, padicValRat.div
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hs hpw) hc₁) hc₂)
    (by exact_mod_cast Nat.factorial_ne_zero (r + j - 1)),
    padicValRat.mul (mul_ne_zero (mul_ne_zero hs hpw) hc₁) hc₂,
    padicValRat.mul (mul_ne_zero hs hpw) hc₁, padicValRat.mul hs hpw]
  simp [padicValRat.pow, padicValRat.self hp.one_lt,
    WPTruncationArithmetic.factorialValuation]

theorem inverse_trace_tail_lower_bound (p r N j : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hN : 1 ≤ N) (hNj : N ≤ j) :
    (5 * (j : ℚ) - (r : ℚ) + 2) / 6 ≤
      (padicValRat p (inverseTraceTailScalar p r N j) : ℚ) := by
  rw [inverse_trace_tail_valuation p r N j hp hr hN hNj]
  push_cast
  simp only [padicValRat.of_nat, Int.cast_natCast]
  have h := factorial_valuation_six_bound p (r + j - 1) hp hp7 (by omega)
  have heq : ((r + j - 1 : ℕ) : ℚ) = (r : ℚ) + j - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [heq] at h
  have hc₁ : (0 : ℚ) ≤ padicValNat p ((r + j - 1).choose j) := by positivity
  have hc₂ : (0 : ℚ) ≤ padicValNat p ((j - 1).choose (N - 1)) := by positivity
  linarith

theorem inverse_trace_tail_uniform_bound (p r N j : ℕ) (hp : p.Prime)
    (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hr5 : r ≤ 5) (hN : 1 ≤ N) (hNj : N ≤ j) :
    (5 * (j : ℚ) - 3) / 6 ≤
      (padicValRat p (inverseTraceTailScalar p r N j) : ℚ) := by
  have h := inverse_trace_tail_lower_bound p r N j hp hp7 hr hN hNj
  have hrQ : (r : ℚ) ≤ 5 := by exact_mod_cast hr5
  linarith

theorem factorial_tail_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      WPReview.RationalCongruent p precision (factorialTailScalar p k) 0 := by
  refine ⟨6 * precision + 1, ?_⟩
  intro k hk
  apply Or.inr
  rw [sub_zero]
  have h := factorial_tail_lower_bound p k hp hp7 (by omega)
  have hkQ : (6 * precision + 1 : ℚ) ≤ k := by exact_mod_cast hk
  have he : (precision : ℚ) ≤ (padicValRat p (factorialTailScalar p k) : ℚ) := by
    nlinarith
  exact_mod_cast he

theorem inverse_trace_tail_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ r N j : ℕ, 1 ≤ r → r ≤ 5 → 1 ≤ N → N ≤ j → cutoff ≤ j →
      WPReview.RationalCongruent p precision (inverseTraceTailScalar p r N j) 0 := by
  refine ⟨6 * precision + 1, ?_⟩
  intro r N j hr hr5 hN hNj hj
  apply Or.inr
  rw [sub_zero]
  have h := inverse_trace_tail_uniform_bound p r N j hp hp7 hr hr5 hN hNj
  have hjQ : (6 * precision + 1 : ℚ) ≤ j := by exact_mod_cast hj
  have he : (precision : ℚ) ≤ (padicValRat p (inverseTraceTailScalar p r N j) : ℚ) := by
    nlinarith
  exact_mod_cast he

/-- Multiplication by an actual integer includes its zero case explicitly. -/
theorem congruent_zero_mul_integer (p precision : ℕ) (hp : p.Prime)
    (a : ℚ) (z : ℤ) (ha : WPReview.RationalCongruent p precision a 0) :
    WPReview.RationalCongruent p precision (a * (z : ℚ)) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases ha with ha | ha
  · subst a; exact Or.inl (by simp)
  · by_cases haz : a = 0
    · simp [haz, WPReview.RationalCongruent]
    by_cases hz : z = 0
    · simp [hz, WPReview.RationalCongruent]
    apply Or.inr
    rw [sub_zero, padicValRat.mul haz (by exact_mod_cast hz), padicValRat.of_int]
    rw [sub_zero] at ha
    have hv : (0 : ℤ) ≤ padicValInt p z := by positivity
    omega

theorem factorial_tail_integer_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ k : ℕ, ∀ z : ℤ, cutoff ≤ k →
      WPReview.RationalCongruent p precision (factorialTailScalar p k * (z : ℚ)) 0 := by
  obtain ⟨cutoff, h⟩ := factorial_tail_eventual p precision hp hp7
  exact ⟨cutoff, fun k z hk => congruent_zero_mul_integer p precision hp _ z (h k hk)⟩

theorem inverse_trace_tail_integer_eventual (p precision : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∃ cutoff : ℕ, ∀ r N j : ℕ, ∀ z : ℤ, 1 ≤ r → r ≤ 5 → 1 ≤ N → N ≤ j → cutoff ≤ j →
      WPReview.RationalCongruent p precision (inverseTraceTailScalar p r N j * (z : ℚ)) 0 := by
  obtain ⟨cutoff, h⟩ := inverse_trace_tail_eventual p precision hp hp7
  exact ⟨cutoff, fun r N j z hr hr5 hN hNj hj =>
    congruent_zero_mul_integer p precision hp _ z (h r N j hr hr5 hN hNj hj)⟩

def traceKernelCoefficient (r j k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * ((r + k - 1).choose k : ℚ) * ((r + j - 1).choose (j - k) : ℚ)

theorem finite_kernel_coefficient_sum (r N j : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, if k ≤ j then traceKernelCoefficient r j k else 0) =
      ((r + j - 1).choose j : ℚ) * alternatingKernel N j := by
  have hm : min j (N - 1) + 1 ≤ N := by omega
  calc
    _ = ∑ k ∈ Finset.range (min j (N - 1) + 1),
        if k ≤ j then traceKernelCoefficient r j k else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hm)
      intro k hkN hkm
      have hk : ¬ k ≤ j := by
        simp only [Finset.mem_range] at hkN hkm
        omega
      simp only [hk, ↓reduceIte]
    _ = ((r + j - 1).choose j : ℚ) * alternatingKernel N j := by
      rw [alternatingKernel, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
      rw [if_pos hkj]
      have hprod : ((r + k - 1).choose k : ℚ) *
          ((r + j - 1).choose (j - k) : ℚ) =
          ((r + j - 1).choose j : ℚ) * (j.choose k : ℚ) := by
        exact_mod_cast binomial_product r j k hr hkj
      unfold traceKernelCoefficient
      calc
        _ = (-1 : ℚ) ^ k * (((r + k - 1).choose k : ℚ) *
            ((r + j - 1).choose (j - k) : ℚ)) := by ring
        _ = _ := by rw [hprod]; ring

/-- A finite direct sum indexed by pole order; no completion or operator is asserted. -/
abbrev FinitePoleCoefficients (V : Type*) [AddCommGroup V] := ℕ →₀ V

section FiniteRegrouping

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Regroup a finite triangle by its total numerator index, in the actual finite pole module. -/
theorem finite_pole_regrouping (p r N M : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N)
    (A : ℕ → V) :
    (∑ k ∈ Finset.range N, ∑ j ∈ Finset.range M,
      if k ≤ j then ((p : ℚ) ^ j * traceKernelCoefficient r j k) •
        (Finsupp.single (r + j) (A j) : FinitePoleCoefficients V) else 0) =
    ∑ j ∈ Finset.range M,
      if j = 0 then (Finsupp.single r (A 0) : FinitePoleCoefficients V)
      else if j < N then 0 else
        ((-1 : ℚ) ^ (N - 1) * (p : ℚ) ^ j * ((r + j - 1).choose j : ℚ) *
          ((j - 1).choose (N - 1) : ℚ)) • Finsupp.single (r + j) (A j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hsum : (∑ k ∈ Finset.range N,
      if k ≤ j then ((p : ℚ) ^ j * traceKernelCoefficient r j k) •
        (Finsupp.single (r + j) (A j) : FinitePoleCoefficients V) else 0) =
      ((p : ℚ) ^ j * ((r + j - 1).choose j : ℚ) * alternatingKernel N j) •
        Finsupp.single (r + j) (A j) := by
    calc
      _ = (∑ k ∈ Finset.range N,
          (p : ℚ) ^ j * (if k ≤ j then traceKernelCoefficient r j k else 0)) •
          Finsupp.single (r + j) (A j) := by
        rw [Finset.sum_smul]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs <;> simp
      _ = _ := by rw [← Finset.mul_sum, finite_kernel_coefficient_sum r N j hr hN,
        mul_assoc]
  rw [hsum, alternating_kernel N j hN]
  split_ifs with hj hjN
  · subst j
    simp
  · simp
  · congr 1
    ring

end FiniteRegrouping

/-- The finite image built from actual finite polynomial coefficients of selected powers. -/
noncomputable def finiteInverseTraceImage (κ : LaurentPolynomial →ₗ[ℚ] LaurentPolynomial)
    (G : LaurentPolynomial) (p r N M : ℕ) : FinitePoleCoefficients LaurentPolynomial :=
  ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range M,
    if k ≤ j then ((p : ℚ) ^ j * traceKernelCoefficient r j k) •
      Finsupp.single (r + j) (κ (G ^ j)) else 0

theorem finite_inverse_trace_image (κ : LaurentPolynomial →ₗ[ℚ] LaurentPolynomial)
    (G : LaurentPolynomial) (p r N M : ℕ) (hr : 1 ≤ r) (hN : 1 ≤ N) :
    finiteInverseTraceImage κ G p r N M =
      ∑ j ∈ Finset.range M,
        if j = 0 then Finsupp.single r (κ (1 : LaurentPolynomial))
        else if j < N then 0 else
          ((-1 : ℚ) ^ (N - 1) * (p : ℚ) ^ j * ((r + j - 1).choose j : ℚ) *
            ((j - 1).choose (N - 1) : ℚ)) • Finsupp.single (r + j) (κ (G ^ j)) := by
  simpa only [finiteInverseTraceImage, pow_zero] using
    finite_pole_regrouping p r N M hr hN (fun j => κ (G ^ j))

end WPCartierFinite
