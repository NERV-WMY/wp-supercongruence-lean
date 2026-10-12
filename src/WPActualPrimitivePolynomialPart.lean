import WPRationalPolynomialPart
import WPActualSquareForcing

open scoped BigOperators
open Polynomial
open WPFiniteConductorPolynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1000000

noncomputable def nativeStateTermWeight (n : ℕ) : Fin 6 → ℚ :=
  let a : ℚ := n
  let w : ℚ := a^3 + (3/2)*a^2 + (23/36)*a + 5/72
  ![-a^3, -a^4, -a^5, w, a*w, a^2*w]

theorem state_term_coefficient (p n : ℕ) (i : Fin 6) :
    (actualSixState p i).coeff n =
      if n < p then nativeStateTermWeight n i * WPReview.nativeCoefficient n^2 else 0 := by
  fin_cases i
  all_goals
    simp [actualSixState, nativeStateTermWeight, thirdNativeShift,
      thetaPower_coeff, WPReview.nativeTheta_coeff, squaredNativePolynomial_coeff]
  all_goals split_ifs <;> ring

theorem finite_monomial_sum_coefficient (p n : ℕ) (a : ℕ → ℚ) :
    (∑ j ∈ Finset.range p, monomial j (a j) : ℚ[X]).coeff n = if n < p then a n else 0 := by
  classical
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases hn : n < p
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by have := Finset.mem_range.mp hb; omega
    simp [hbn]

theorem actual_state_finite_expansion (p : ℕ) (i : Fin 6) :
    actualSixState p i = ∑ n ∈ Finset.range p,
      monomial n (nativeStateTermWeight n i * WPReview.nativeCoefficient n^2) := by
  ext n
  rw [state_term_coefficient, finite_monomial_sum_coefficient]

noncomputable def nativePrimitiveTerm (n : ℕ) (i : Fin 6) : RatFunc ℚ :=
  RatFunc.C (nativeStateTermWeight n i * WPReview.nativeCoefficient n^2) *
    lambda^n * primitiveEntry i

theorem actual_primitive_finite_expansion (p : ℕ) :
    nativePrimitive p = ∑ n ∈ Finset.range p, ∑ i : Fin 6, nativePrimitiveTerm n i := by
  unfold nativePrimitive nativeStateValue
  simp_rw [actual_state_finite_expansion, ← pullbackHom_apply, map_sum,
    pullbackHom_apply, pullbackValue_monomial, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [nativePrimitiveTerm]
  ring

theorem primitive_denominator_nonzero (i : Fin 6) : primitiveDenominator i ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval 1) h
  fin_cases i <;> norm_num [primitiveDenominator] at he

theorem primitive_infinity_degree (i : Fin 6) :
    (primitiveNumerator i).natDegree ≤ (primitiveDenominator i).natDegree + 8 := by
  have hd : (primitiveDenominator i).natDegree = (![3, 3, 6, 3, 3, 3] : Fin 6 → ℕ) i := by
    fin_cases i <;> dsimp [primitiveDenominator]
    all_goals compute_degree!
  rw [hd]
  fin_cases i
  all_goals norm_num [primitiveNumerator]
  all_goals compute_degree!

noncomputable def primitiveUnscaledTerm (n : ℕ) (i : Fin 6) : RatFunc ℚ :=
  lambda^n * primitiveEntry i

theorem primitive_unscaled_term_fraction (n : ℕ) (i : Fin 6) :
    primitiveUnscaledTerm n i =
      algebraMap ℚ[X] (RatFunc ℚ)
        (C ((729/15625:ℚ)^n) * X^(3*n) * primitiveNumerator i) /
      algebraMap ℚ[X] (RatFunc ℚ) (primitiveDenominator i) := by
  simp only [primitiveUnscaledTerm, lambda, primitiveEntry, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, symbol, pow_mul, mul_pow,
    map_div₀, map_ofNat]
  ring

theorem primitive_low_index_3p_coefficient (p n : ℕ) (hp : 0 < p)
    (hn : n + 3 ≤ p) (i : Fin 6) :
    (rationalPolynomialPart (primitiveUnscaledTerm n i)).coeff (3*p) = 0 := by
  rw [primitive_unscaled_term_fraction]
  apply rationalPolynomialPart_fraction_coeff_zero _ _ (primitive_denominator_nonzero i)
    (3*p) (by omega)
  have hnum : (C ((729/15625:ℚ)^n) * X^(3*n) * primitiveNumerator i).natDegree ≤
      3*n + (primitiveNumerator i).natDegree := by
    calc
      _ ≤ (C ((729/15625:ℚ)^n) * X^(3*n)).natDegree +
          (primitiveNumerator i).natDegree := natDegree_mul_le
      _ ≤ 3*n + (primitiveNumerator i).natDegree := by
        gcongr
        exact natDegree_C_mul_X_pow_le _ _
  have hdeg := primitive_infinity_degree i
  omega

theorem primitive_numerator_integral (p : ℕ) [Fact p.Prime] (i : Fin 6) :
    primitiveNumerator i ∈ coefficientSubring (integralSubring p) := by
  let P := coefficientSubring (integralSubring p)
  have hx : X ∈ P := X_mem_coefficientSubring (integralSubring p)
  fin_cases i <;> dsimp only [primitiveNumerator]
  all_goals
    repeat' first
      | exact hx
      | exact P.one_mem
      | exact P.zero_mem
      | exact natCast_mem P _
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem

noncomputable def primitiveDenominatorScalar : Fin 6 → ℚ :=
  ![4422292875000, 2211146437500, 4975079484375,
    61420734375000, 38387958984375, 38387958984375]

noncomputable def primitiveDenominatorOrder : Fin 6 → ℕ := ![1, 1, 4, 1, 1, 1]

theorem primitive_denominator_formula (i : Fin 6) :
    primitiveDenominator i = C (primitiveDenominatorScalar i) *
      X ^ primitiveDenominatorOrder i * (99 * X - 50)^2 := by
  fin_cases i <;> norm_num [primitiveDenominator, primitiveDenominatorScalar,
    primitiveDenominatorOrder, C_ofNat]

theorem primitive_denominator_integral (p : ℕ) [Fact p.Prime] (i : Fin 6) :
    primitiveDenominator i ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hx : X ∈ P := X_mem_coefficientSubring R
  have hs : primitiveDenominatorScalar i ∈ R := by
    fin_cases i <;> dsimp [primitiveDenominatorScalar] <;> exact natCast_mem R _
  rw [primitive_denominator_formula]
  exact P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ hs)
    (P.pow_mem hx _)) (P.pow_mem
      (P.sub_mem (P.mul_mem (natCast_mem P 99) hx) (natCast_mem P 50)) 2)

theorem primitive_denominator_leadingCoeff (i : Fin 6) :
    (primitiveDenominator i).leadingCoeff = primitiveDenominatorScalar i * 99^2 := by
  have hd : (99 * X - 50 : ℚ[X]).natDegree = 1 := by compute_degree!
  have he : (99 * X - 50 : ℚ[X]).leadingCoeff = 99 := by
    rw [leadingCoeff, hd]
    norm_num
  rw [primitive_denominator_formula, leadingCoeff_mul, leadingCoeff_mul,
    leadingCoeff_C, leadingCoeff_X_pow, leadingCoeff_pow, he, mul_one]

theorem primitive_denominator_leading_inverse_integral
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (i : Fin 6) :
    (primitiveDenominator i).leadingCoeff⁻¹ ∈ integralSubring p := by
  let R := integralSubring p
  have h2 : (1/2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h3 : (1/3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1/5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have h7 : (1/7 : ℚ) ∈ R := small_inverse_integral p 7 (by norm_num) (by omega)
  have h11 : (1/11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  have h13 : (1/13 : ℚ) ∈ R := small_inverse_integral p 13 (by norm_num) (by omega)
  have h17 : (1/17 : ℚ) ∈ R := small_inverse_integral p 17 (by norm_num) (by omega)
  have h2d : (1 / 4975079484375 : ℚ) ∈ R := by
    rw [show (1 / 4975079484375 : ℚ) =
      (1 / 3)^5 * (1 / 5)^6 * (1 / 7)^2 * (1 / 11)^2 * (1 / 13) * (1 / 17) by norm_num]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem
      (R.mul_mem (R.pow_mem h3 5) (R.pow_mem h5 6)) (R.pow_mem h7 2))
        (R.pow_mem h11 2)) h13) h17
  have h5d : (1 / 38387958984375 : ℚ) ∈ R := by
    rw [show (1 / 38387958984375 : ℚ) =
      (1 / 3) * (1 / 5)^10 * (1 / 7)^2 * (1 / 11)^2 * (1 / 13) * (1 / 17) by norm_num]
    exact R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem
      (R.mul_mem h3 (R.pow_mem h5 10)) (R.pow_mem h7 2))
        (R.pow_mem h11 2)) h13) h17
  have hd : (primitiveDenominatorScalar i)⁻¹ ∈ R := by
    fin_cases i <;> dsimp only [primitiveDenominatorScalar]
    · change (4422292875000 : ℚ)⁻¹ ∈ R
      rw [show (4422292875000 : ℚ)⁻¹ = 9 * (1/2)^3 * (1/4975079484375) by norm_num]
      exact R.mul_mem (R.mul_mem (natCast_mem R 9) (R.pow_mem h2 3)) h2d
    · change (2211146437500 : ℚ)⁻¹ ∈ R
      rw [show (2211146437500 : ℚ)⁻¹ = 18 * (1/2)^3 * (1/4975079484375) by norm_num]
      exact R.mul_mem (R.mul_mem (natCast_mem R 18) (R.pow_mem h2 3)) h2d
    · change (4975079484375 : ℚ)⁻¹ ∈ R
      simpa only [one_div] using h2d
    · change (61420734375000 : ℚ)⁻¹ ∈ R
      rw [show (61420734375000 : ℚ)⁻¹ = 5 * (1/2)^3 * (1/38387958984375) by norm_num]
      exact R.mul_mem (R.mul_mem (natCast_mem R 5) (R.pow_mem h2 3)) h5d
    · change (38387958984375 : ℚ)⁻¹ ∈ R
      simpa only [one_div] using h5d
    · change (38387958984375 : ℚ)⁻¹ ∈ R
      simpa only [one_div] using h5d
  have h99 : (1/99 : ℚ) ∈ R := by
    rw [show (1/99 : ℚ) = (1/3)^2 * (1/11) by norm_num]
    exact R.mul_mem (R.pow_mem h3 2) h11
  rw [primitive_denominator_leadingCoeff, mul_inv_rev, ← inv_pow]
  exact R.mul_mem (R.pow_mem (by simpa only [one_div] using h99) 2) hd

theorem primitive_unscaled_polynomialPart_integral
    (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (i : Fin 6) (k : ℕ) :
    (rationalPolynomialPart (primitiveUnscaledTerm n i)).coeff k ∈ integralSubring p := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hnum : C ((729/15625 : ℚ)^n) * X^(3*n) * primitiveNumerator i ∈ P := by
    have heq : C ((729/15625 : ℚ)^n) * X^(3*n) = lam^n := by
      simp only [lam, map_pow, mul_pow, pow_mul]
    rw [heq]
    exact P.mul_mem (P.pow_mem (literal_lambda_integral p (by omega)) n)
      (primitive_numerator_integral p i)
  rw [primitive_unscaled_term_fraction, rationalPolynomialPart_fraction _ _
    (primitive_denominator_nonzero i)]
  exact ordinary_quotient_coeff_mem R _ _ (primitive_denominator_nonzero i)
    ((mem_coefficientSubring R _).mp hnum)
    ((mem_coefficientSubring R _).mp (primitive_denominator_integral p i))
    (primitive_denominator_leading_inverse_integral p hp i) k

theorem native_state_weight_integral (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (i : Fin 6) : nativeStateTermWeight n i ∈ integralSubring p := by
  let R := integralSubring p
  have hn : (n : ℚ) ∈ R := natCast_mem R n
  have h2 : (1/2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h3 : (1/3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have ha : (3/2 : ℚ) ∈ R := by
    rw [show (3/2 : ℚ) = 3 * (1/2) by norm_num]
    exact R.mul_mem (natCast_mem R 3) h2
  have hb : (23/36 : ℚ) ∈ R := by
    rw [show (23/36 : ℚ) = 23 * (1/2)^2 * (1/3)^2 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 23) (R.pow_mem h2 2)) (R.pow_mem h3 2)
  have hc : (5/72 : ℚ) ∈ R := by
    rw [show (5/72 : ℚ) = 5 * (1/2)^3 * (1/3)^2 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 5) (R.pow_mem h2 3)) (R.pow_mem h3 2)
  have hw : ((n : ℚ)^3 + (3/2)*(n : ℚ)^2 + (23/36)*(n : ℚ) + 5/72) ∈ R :=
    R.add_mem (R.add_mem (R.add_mem (R.pow_mem hn 3)
      (R.mul_mem ha (R.pow_mem hn 2))) (R.mul_mem hb hn)) hc
  fin_cases i <;> dsimp only [nativeStateTermWeight]
  · exact R.neg_mem (R.pow_mem hn 3)
  · exact R.neg_mem (R.pow_mem hn 4)
  · exact R.neg_mem (R.pow_mem hn 5)
  · exact hw
  · exact R.mul_mem hn hw
  · exact R.mul_mem (R.pow_mem hn 2) hw

/-- The extended endpoint uses only the last two native squares; each has precision six. -/
theorem actual_primitive_polynomialPart_3p_precision
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    precisionZero p 6 ((rationalPolynomialPart (nativePrimitive p)).coeff (3*p)) := by
  classical
  rw [actual_primitive_finite_expansion, rationalPolynomialPart_sum]
  simp only [finsetSum_coeff]
  apply precisionZero_sum p 6 _ _
  intro n hn
  rw [rationalPolynomialPart_sum]
  simp only [finsetSum_coeff]
  apply precisionZero_sum p 6 _ _
  intro i hi
  have heq : nativePrimitiveTerm n i =
      RatFunc.C (nativeStateTermWeight n i * WPReview.nativeCoefficient n^2) *
        primitiveUnscaledTerm n i := by
    dsimp [nativePrimitiveTerm, primitiveUnscaledTerm]
    ring
  rw [heq, rationalPolynomialPart_scalar, coeff_C_mul]
  by_cases hlow : n + 3 ≤ p
  · rw [primitive_low_index_3p_coefficient p n (by omega) hlow i, mul_zero]
    exact Or.inl rfl
  · have hval := native_top_three_square_valuation p n hp
      (Finset.mem_range.mp hn) (by omega)
    have hsq : precisionZero p 6 (WPReview.nativeCoefficient n^2) := Or.inr (by omega)
    have hint : 0 ≤ padicValRat p (nativeStateTermWeight n i *
        (rationalPolynomialPart (primitiveUnscaledTerm n i)).coeff (3*p)) :=
      (integralSubring p).mul_mem (native_state_weight_integral p n hp i)
        (primitive_unscaled_polynomialPart_integral p n hp i (3*p))
    convert precisionZero_mul_integral p 6 _ _ hsq hint using 1
    ring

end

end WPForcedSourceStokes
