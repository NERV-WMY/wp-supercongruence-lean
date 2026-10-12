import WPNativeCutoff
import WPFiniteConductorReflection
import Mathlib.Algebra.Polynomial.Degree.Operations

open scoped BigOperators
open Polynomial

namespace WPNativeMomentIntegrality

/-- The actual integer numerator in D1; its coefficient range is not fitted. -/
noncomputable def nativeNumerator (p n : ℕ) : ℤ[X] :=
  (4 * X - 1) ^ (2 * p + n - 1) *
    (4 - X) ^ (p + 2 * n - 1) * (11 - 4 * X)

noncomputable def actualMonomialMoment (p n : ℕ) : ℚ :=
  monomialMoment p n (nativeNumerator p n).coeff

theorem actual_monomial_moment_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    0 ≤ padicValRat p (actualMonomialMoment p n) :=
  monomial_moment_integral p n hp hn _

theorem native_numerator_degree_bound (p n : ℕ) (hp : 1 ≤ p) :
    (nativeNumerator p n).natDegree < 3 * (p + n) := by
  have hA : (4 * (X : ℤ[X]) - 1).natDegree ≤ 1 := by compute_degree
  have hB : (4 - (X : ℤ[X])).natDegree ≤ 1 := by compute_degree
  have hC : (11 - 4 * (X : ℤ[X])).natDegree ≤ 1 := by compute_degree
  have hApow := natDegree_pow_le_of_le (2 * p + n - 1) hA
  have hBpow := natDegree_pow_le_of_le (p + 2 * n - 1) hB
  have hAB :
      (((4 * (X : ℤ[X]) - 1) ^ (2 * p + n - 1)) *
        ((4 - (X : ℤ[X])) ^ (p + 2 * n - 1))).natDegree ≤
      ((4 * (X : ℤ[X]) - 1) ^ (2 * p + n - 1)).natDegree +
        ((4 - (X : ℤ[X])) ^ (p + 2 * n - 1)).natDegree := natDegree_mul_le
  have hABC :
      ((((4 * (X : ℤ[X]) - 1) ^ (2 * p + n - 1)) *
        ((4 - (X : ℤ[X])) ^ (p + 2 * n - 1))) *
          (11 - 4 * (X : ℤ[X]))).natDegree ≤
      (((4 * (X : ℤ[X]) - 1) ^ (2 * p + n - 1)) *
        ((4 - (X : ℤ[X])) ^ (p + 2 * n - 1))).natDegree +
          (11 - 4 * (X : ℤ[X])).natDegree := natDegree_mul_le
  dsimp only [nativeNumerator]
  omega

theorem native_numerator_full_evaluation (p n : ℕ) (hp : 1 ≤ p) (s : ℚ) :
    (nativeNumerator p n).eval₂ (Int.castRingHom ℚ) (s ^ 2) =
      ∑ a ∈ Finset.range (3 * (p + n)),
        ((nativeNumerator p n).coeff a : ℚ) * s ^ (2 * a) := by
  rw [eval₂_eq_sum_range' (Int.castRingHom ℚ) (native_numerator_degree_bound p n hp)]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [← pow_mul]
  rfl

/-- The original finite primitive retains the endpoints s=1/2 and s=2. -/
theorem actual_moment_endpoint_formula (p n : ℕ) :
    actualMonomialMoment p n =
      2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n)) *
        ∑ a ∈ Finset.range (3 * (p + n)),
          ((nativeNumerator p n).coeff a : ℚ) *
            WPFiniteConductorReflection.monomialEndpoint
              (primitiveDenominator n a) (1 / 2) 2 := by
  unfold actualMonomialMoment monomialMoment primitiveWeight
  simp only [WPFiniteConductorReflection.monomialEndpoint,
    WPFiniteConductorReflection.reciprocal_two_zpow]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem scaled_q1 (s : ℚ) (hs : s ≠ 0) :
    WPFiniteConductorReflection.q1 (s / 2) =
      (4 * s ^ 2 - 1) * (4 - s ^ 2) ^ 2 / (125 * s ^ 6) := by
  unfold WPFiniteConductorReflection.q1
  field_simp [hs]
  ring

theorem scaled_q2 (s : ℚ) :
    WPFiniteConductorReflection.q2 (s / 2) =
      (4 * s ^ 2 - 1) ^ 2 * (4 - s ^ 2) / 125 := by
  unfold WPFiniteConductorReflection.q2
  ring

theorem scaled_first_weight (s : ℚ)
    (hA : 4 * s ^ 2 - 1 ≠ 0) (hB : 4 - s ^ 2 ≠ 0) :
    WPFiniteConductorReflection.firstWeight (s / 2) =
      4 * (11 - 4 * s ^ 2) / (3 * (4 - s ^ 2) * (4 * s ^ 2 - 1)) := by
  have he1 : 1 - (s / 2) ^ 2 = (4 - s ^ 2) / 4 := by ring
  have he16 : 16 * (s / 2) ^ 2 - 1 = 4 * s ^ 2 - 1 := by ring
  have heNum : 16 * (s / 2) ^ 2 - 11 = -(11 - 4 * s ^ 2) := by ring
  unfold WPFiniteConductorReflection.firstWeight
  rw [he1, he16, heNum]
  generalize hdA : (4 * s ^ 2 - 1) = A
  generalize hdB : (4 - s ^ 2) = B
  have ha : A ≠ 0 := hdA ▸ hA
  have hb : B ≠ 0 := hdB ▸ hB
  field_simp [ha, hb]

private theorem finite_power_cancellation (A B c s Z : ℚ) (p n : ℕ)
    (hp : 1 ≤ p) (hA : A ≠ 0) (hB : B ≠ 0) (hc : c ≠ 0) (hs : s ≠ 0) :
    (4 * Z / (3 * B * A)) * ((A ^ 2 * B) / c) ^ p *
      ((A * B ^ 2) / (c * s ^ 6)) ^ n =
      4 * Z * A ^ (2 * p + n - 1) * B ^ (p + 2 * n - 1) /
        (3 * c ^ (p + n) * s ^ (6 * n)) := by
  have hApow : A ^ (p * 2) * A ^ n = A ^ (2 * p + n - 1) * A := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hBpow : B ^ p * B ^ (n * 2) = B ^ (p + 2 * n - 1) * B := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow,
    ← pow_mul, ← pow_mul, ← pow_mul, pow_add c p n]
  field_simp [hA, hB, hc, hs]
  linear_combination
    Z * B ^ p * B ^ (n * 2) * hApow +
      Z * A ^ (2 * p + n - 1) * A * hBpow

/-- The actual first conductor flux, with ds/2 from r=s/2, after cancellation. -/
theorem actual_native_density (p n : ℕ) (hp : 1 ≤ p) (s : ℚ) (hs : s ≠ 0)
    (hA : 4 * s ^ 2 - 1 ≠ 0) (hB : 4 - s ^ 2 ≠ 0) :
    (p : ℚ) / 2 * WPFiniteConductorReflection.firstFlux p n (s / 2) =
      2 * (p : ℚ) /
        (3 * (125 : ℚ) ^ (p + n) * s ^ (6 * n)) *
        (nativeNumerator p n).eval₂ (Int.castRingHom ℚ) (s ^ 2) := by
  have h := finite_power_cancellation (4 * s ^ 2 - 1) (4 - s ^ 2)
    125 s (11 - 4 * s ^ 2) p n hp hA hB (by norm_num) hs
  unfold WPFiniteConductorReflection.firstFlux
  rw [scaled_first_weight s hA hB, scaled_q2, scaled_q1 s hs]
  simp only [nativeNumerator, eval₂_mul, eval₂_pow, eval₂_sub, eval₂_one,
    eval₂_X, eval₂_ofNat]
  linear_combination (p : ℚ) / 2 * h

/-- Every term of the original canceled density, including the full Laurent range. -/
theorem actual_native_density_full_series (p n : ℕ) (hp : 1 ≤ p) (s : ℚ) (hs : s ≠ 0)
    (hA : 4 * s ^ 2 - 1 ≠ 0) (hB : 4 - s ^ 2 ≠ 0) :
    (p : ℚ) / 2 * WPFiniteConductorReflection.firstFlux p n (s / 2) =
      2 * (p : ℚ) / (3 * (125 : ℚ) ^ (p + n)) *
        ∑ a ∈ Finset.range (3 * (p + n)),
          ((nativeNumerator p n).coeff a : ℚ) *
            s ^ (primitiveDenominator n a - 1) := by
  rw [actual_native_density p n hp s hs hA hB,
    native_numerator_full_evaluation p n hp s, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  have hpow : s ^ (primitiveDenominator n a - 1) = s ^ (2 * a) / s ^ (6 * n) := by
    have he : primitiveDenominator n a - 1 = ((2 * a : ℕ) : ℤ) - ((6 * n : ℕ) : ℤ) := by
      unfold primitiveDenominator
      push_cast
      ring
    rw [he, zpow_sub₀ hs, zpow_natCast, zpow_natCast]
  rw [hpow]
  field_simp [hs]

/-- The actual conductor numerator, without an arbitrary coefficient premise. -/
theorem actual_full_literal_cutoff_moment_precision (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) :
    (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) =
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
        WPReview.nativeCoefficient n * actualMonomialMoment p n) ∨
    (3 : ℤ) ≤ padicValRat p
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n * actualMonomialMoment p n) -
        (∑ n ∈ Finset.range (p - 1 - p / 6 + 1),
          WPReview.nativeCoefficient n * actualMonomialMoment p n)) :=
  native_full_literal_cutoff_moment_precision p hp (fun n => (nativeNumerator p n).coeff)

end WPNativeMomentIntegrality
