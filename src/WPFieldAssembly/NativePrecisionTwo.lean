import WPFieldAssembly.NativePrecision

open scoped Polynomial
open Polynomial WPPIntegralReduction WPFieldAssembly.TerminatingSquare
  WPFieldAssembly.NativeDiscriminant WPFieldAssembly.NativePrecision

namespace WPFieldAssembly.NativePrecisionTwo

set_option maxHeartbeats 1000000

noncomputable def nativeFirstDerivativeSource (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  C (2 * (9 * (p : integralRationals p) ^ 2 - 4) *
    (p : integralRationals p) * nativeHalfDivPrime p hp) * X *
      (1 - X ^ 2) ^ ((p - 1) / 2) * integralNativeJacobi p hp

theorem nativeFirstDerivativeSource_field_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeFirstDerivativeSource p hp).map (residueHom p) = 0 := by
  simp [nativeFirstDerivativeSource, Polynomial.map_natCast]

/-- The original rational residual is divided before the integral source is reduced. -/
theorem first_divided_discriminant_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (Q : (integralRationals p)[X])
    (hQ : Q.map (integralRationals p).subtype =
      C (1 / (p : ℚ)) * weightedNativeDiscriminant p) :
    Q.derivative = nativeFirstDerivativeSource p hp := by
  apply Polynomial.map_injective (integralRationals p).subtype
    (Subring.subtype_injective (integralRationals p))
  rw [← derivative_map, hQ, derivative_C_mul, weightedNativeDiscriminant,
    actual_half_native_weighted_source p hp]
  simp only [nativeFirstDerivativeSource, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X,
    integralNativeJacobi_rational]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hc : (1 / (p : ℚ)) *
      (2 * (p : ℚ) * (9 * (p : ℚ) ^ 2 - 4) *
        WPReview.nativeCoefficient ((p - 1) / 2)) =
      2 * (9 * (p : ℚ) ^ 2 - 4) * (p : ℚ) *
        (nativeHalfDivPrime p hp).val := by
    change _ = 2 * (9 * (p : ℚ) ^ 2 - 4) * (p : ℚ) *
      (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ))
    field_simp
  have he := congrArg (C : ℚ → ℚ[X]) hc
  simp only [map_mul, map_sub, map_pow, map_ofNat, map_natCast] at he ⊢
  change _ = (2 * (9 * (p : ℚ[X]) ^ 2 - 4) * (p : ℚ[X]) *
      C (nativeHalfDivPrime p hp).val) * X *
        (1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p
  linear_combination
    (X * (1 - X ^ 2) ^ ((p - 1) / 2) * halfNativeJacobi p) * he

theorem first_divided_discriminant_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (Q : (integralRationals p)[X])
    (hQ : Q.map (integralRationals p).subtype =
      C (1 / (p : ℚ)) * weightedNativeDiscriminant p) :
    Q.coeff (2 * p) = (p : integralRationals p) *
      (9 * (p : integralRationals p) ^ 2 - 4) * nativeHalfDivPrime p hp ^ 2 := by
  apply Subtype.ext
  have hc := congrArg (fun P : ℚ[X] => P.coeff (2 * p)) hQ
  rw [coeff_map, coeff_C_mul, actual_native_discriminant_top p hp] at hc
  change (Q.coeff (2 * p)).val = (1 / (p : ℚ)) *
    ((9 * (p : ℚ) ^ 2 - 4) * WPReview.nativeCoefficient ((p - 1) / 2) ^ 2) at hc
  change (Q.coeff (2 * p)).val = (p : ℚ) *
    (9 * (p : ℚ) ^ 2 - 4) *
      (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ)) ^ 2
  rw [hc]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp

/-- The first division has zero residue only after the full top, parity and endpoint are fixed. -/
theorem first_divided_discriminant_field_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (Q : (integralRationals p)[X])
    (hQ : Q.map (integralRationals p).subtype =
      C (1 / (p : ℚ)) * weightedNativeDiscriminant p) :
    Q.map (residueHom p) = 0 := by
  apply even_derivative_zero_two_digits_eq_zero p hp
  · have hpq : (1 / (p : ℚ)) ≠ 0 := by positivity
    have hd : Q.natDegree = (weightedNativeDiscriminant p).natDegree := by
      rw [← natDegree_map_eq_of_injective
        (Subring.subtype_injective (integralRationals p)) Q, hQ, natDegree_C_mul hpq]
    exact natDegree_map_le.trans (hd.le.trans (weightedNativeDiscriminant_degree p hp))
  · rw [derivative_map, first_divided_discriminant_source p hp Q hQ,
      nativeFirstDerivativeSource_field_zero p hp]
  · have he : Q.comp (-X) = Q := by
      apply Polynomial.map_injective (integralRationals p).subtype
        (Subring.subtype_injective (integralRationals p))
      rw [Polynomial.map_comp, hQ]
      simp only [Polynomial.map_neg, Polynomial.map_X, mul_comp, C_comp,
        weightedNativeDiscriminant_even]
    have hf := congrArg (Polynomial.map (residueHom p)) he
    simpa only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using hf
  · rw [coeff_map, first_divided_discriminant_top p hp Q hQ]
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  · have he : Q.eval 1 = 0 := by
      apply (Subring.subtype_injective (integralRationals p))
      have hv := congrArg (fun P : ℚ[X] => P.eval 1) hQ
      simpa [eval_map, eval₂_at_one, weightedNativeDiscriminant] using hv
    simpa only [eval_map, eval₂_at_one, map_zero] using
      congrArg (residueHom p) he

/-- Actual native weighted discriminant has p² precision for every prime in both classes. -/
theorem actual_native_discriminant_divided_two_witness
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ∃ Q : (integralRationals p)[X],
      Q.map (integralRationals p).subtype =
        C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p := by
  obtain ⟨Q1, hQ1, _⟩ := exists_integral_polynomial_div_prime p
    (integralNativeDiscriminant p hp) (integralNativeDiscriminant_field_zero p hp)
  rw [integralNativeDiscriminant_rational p hp] at hQ1
  obtain ⟨Q2, hQ2, _⟩ := exists_integral_polynomial_div_prime p Q1
    (first_divided_discriminant_field_zero p hp Q1 hQ1)
  refine ⟨Q2, ?_⟩
  rw [hQ2, hQ1, ← mul_assoc, ← C_mul]
  congr 2
  ring

theorem actual_native_discriminant_divided_two_integral
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((C (1 / (p : ℚ) ^ 2) *
      weightedNativeDiscriminant p).coeff n) := by
  obtain ⟨Q, hQ⟩ := actual_native_discriminant_divided_two_witness p hp
  rw [← hQ, coeff_map]
  exact (Q.coeff n).property

theorem second_divided_discriminant_top (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (Q : (integralRationals p)[X])
    (hQ : Q.map (integralRationals p).subtype =
      C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p) :
    Q.coeff (2 * p) = (9 * (p : integralRationals p) ^ 2 - 4) *
      nativeHalfDivPrime p hp ^ 2 := by
  apply Subtype.ext
  have hc := congrArg (fun P : ℚ[X] => P.coeff (2 * p)) hQ
  rw [coeff_map, coeff_C_mul, actual_native_discriminant_top p hp] at hc
  change (Q.coeff (2 * p)).val = (1 / (p : ℚ) ^ 2) *
    ((9 * (p : ℚ) ^ 2 - 4) * WPReview.nativeCoefficient ((p - 1) / 2) ^ 2) at hc
  change (Q.coeff (2 * p)).val = (9 * (p : ℚ) ^ 2 - 4) *
    (WPReview.nativeCoefficient ((p - 1) / 2) / (p : ℚ)) ^ 2
  rw [hc]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp

/-- The invisible 2p coefficient survives the second division. -/
theorem actual_native_discriminant_divided_two_top_residue
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (((C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p).coeff (2 * p) : ℚ) : ZMod p) =
      -4 * (residueHom p (nativeHalfDivPrime p hp)) ^ 2 := by
  obtain ⟨Q, hQ⟩ := actual_native_discriminant_divided_two_witness p hp
  rw [← hQ, coeff_map]
  change residueHom p (Q.coeff (2 * p)) = _
  rw [second_divided_discriminant_top p hp Q hQ]
  simp only [map_mul, map_sub, map_pow, map_ofNat, map_natCast,
    ZMod.natCast_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_sub]

theorem actual_native_discriminant_divided_two_top_ne_zero
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (((C (1 / (p : ℚ) ^ 2) * weightedNativeDiscriminant p).coeff (2 * p) : ℚ) : ZMod p) ≠ 0 := by
  rw [actual_native_discriminant_divided_two_top_residue p hp]
  exact mul_ne_zero (neg_ne_zero.mpr
    (WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)))
      (pow_ne_zero 2 (actual_native_half_div_prime_residue_ne_zero p hp))

theorem actual_native_discriminant_precision_two
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℕ) :
    WPReview.RationalCongruent p 2 ((weightedNativeDiscriminant p).coeff n) 0 := by
  rw [WPReview.RationalCongruent, sub_zero]
  by_cases hn : (weightedNativeDiscriminant p).coeff n = 0
  · exact Or.inl hn
  · apply Or.inr
    have hi := actual_native_discriminant_divided_two_integral p hp n
    rw [coeff_C_mul, show (1 / (p : ℚ) ^ 2) * (weightedNativeDiscriminant p).coeff n =
        (weightedNativeDiscriminant p).coeff n / (p : ℚ) ^ 2 by ring,
      padicValRat.div hn (pow_ne_zero 2 (by positivity : (p : ℚ) ≠ 0)),
      padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt] at hi
    norm_num at hi ⊢
    omega

end WPFieldAssembly.NativePrecisionTwo
