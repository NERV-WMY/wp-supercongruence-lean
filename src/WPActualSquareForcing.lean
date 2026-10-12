import WPActualNativeConnection
import WPActualConductorEscape

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

set_option maxHeartbeats 1000000

open WPFiniteConductorPolynomial

theorem integral_series_inverse (R : Subring ℚ) (F : PowerSeries ℚ)
    (hF : ∀ k, PowerSeries.coeff k F ∈ R)
    (h0 : (PowerSeries.constantCoeff F)⁻¹ ∈ R) :
    ∀ k, PowerSeries.coeff k F⁻¹ ∈ R := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hk
    · exact h0
    · apply R.mul_mem (R.neg_mem h0)
      apply R.sum_mem
      intro a _ha
      split_ifs with ha
      · exact R.mul_mem (hF a.1) (ih a.2 ha)
      · exact R.zero_mem

noncomputable def squareRegularDenominator : ℚ[X] := (1 - lam) * escape ^ 2

noncomputable def squareFixedNumerator : ℚ[X] :=
  20250 * (1 - X) *
    (C (-1 / 4975079484375) * primitiveNumerator 2 +
      C (1 / 38387958984375) * X ^ 3 * primitiveNumerator 5)

noncomputable def squareUnscaledPolynomial (p : ℕ) : ℚ[X] :=
  C ((729 / 15625 : ℚ) ^ p) * X ^ (3 * p - 5) * squareFixedNumerator

/-- The actual regular Taylor series of the retained square forcing. -/
noncomputable def actualSquareForcingSeries (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (WPReview.nativeEndpoint p ^ 2) *
    (squareUnscaledPolynomial p : PowerSeries ℚ) *
      (squareRegularDenominator : PowerSeries ℚ)⁻¹

theorem square_regular_denominator_constant : squareRegularDenominator.coeff 0 = 2500 := by
  norm_num [squareRegularDenominator, lam, escape, pow_two, coeff_mul]

theorem square_regular_denominator_nonzero : squareRegularDenominator ≠ 0 := by
  intro h
  have hc := congrArg (fun P : ℚ[X] => P.coeff 0) h
  rw [square_regular_denominator_constant] at hc
  norm_num at hc

/-- The regular numerator/denominator is the printed actual rational J. -/
theorem actual_square_forcing_rational (p : ℕ) (hp : 2 ≤ p) :
    nativeSquareForcing p = RatFunc.C (WPReview.nativeEndpoint p ^ 2) *
      algebraMap ℚ[X] (RatFunc ℚ) (squareUnscaledPolynomial p) /
        algebraMap ℚ[X] (RatFunc ℚ) squareRegularDenominator := by
  have hx : symbol ≠ 0 := RatFunc.algebraMap_ne_zero X_ne_zero
  have hX : algebraMap ℚ[X] (RatFunc ℚ) X = symbol := rfl
  have hL : algebraMap ℚ[X] (RatFunc ℚ) lam = lambda := by
    norm_num [lam, lambda, symbol, RatFunc.algebraMap_C, map_ratCast]
  have hE : algebraMap ℚ[X] (RatFunc ℚ) escape = 99 * symbol - 50 := by
    norm_num [escape, symbol, map_ratCast, _root_.map_ofNat]
  have hD : algebraMap ℚ[X] (RatFunc ℚ) squareRegularDenominator =
      (1 - lambda) * (99 * symbol - 50) ^ 2 := by
    simp only [squareRegularDenominator, map_mul, map_sub, map_one, map_pow, hL, hE]
  have hDn : (1 - lambda) * (99 * symbol - 50) ^ 2 ≠ 0 := by
    rw [← hD]
    exact RatFunc.algebraMap_ne_zero square_regular_denominator_nonzero
  have hl := (mul_ne_zero_iff.mp hDn).1
  have he : 99 * symbol - 50 ≠ 0 := by
    intro he
    apply hDn
    simp [he]
  have hsum : (∑ i : Fin 6, primitiveEntry i * RatFunc.C (nativeForcingVector i)) =
      primitiveEntry 5 - primitiveEntry 2 := by
    norm_num [Fin.sum_univ_succ, nativeForcingVector]
    change -primitiveEntry 2 + primitiveEntry 5 = primitiveEntry 5 - primitiveEntry 2
    ring
  have hd2 : primitiveDenominator 2 = 4975079484375 * X ^ 4 * escape ^ 2 := rfl
  have hd5 : primitiveDenominator 5 = 38387958984375 * X * escape ^ 2 := rfl
  have hpw : symbol ^ (3 * p) = symbol ^ (3 * p - 5) * symbol ^ 5 := by
    rw [← pow_add, show 3 * p - 5 + 5 = 3 * p by omega]
  rw [nativeSquareForcing, hsum, primitiveEntry, primitiveEntry, hd2, hd5, hD]
  simp only [squareUnscaledPolynomial, squareFixedNumerator,
    map_mul, map_add, map_sub, map_pow, map_one, hX, hE, RatFunc.algebraMap_C,
    _root_.map_ofNat]
  simp only [map_div₀, map_neg, map_one, _root_.map_ofNat]
  field_simp [hx, hl, he]
  simp only [lambda, mul_pow, ← pow_mul]
  rw [hpw]
  ring

theorem actual_square_series_equation (p : ℕ) :
    (squareRegularDenominator : PowerSeries ℚ) * actualSquareForcingSeries p =
      PowerSeries.C (WPReview.nativeEndpoint p ^ 2) *
        (squareUnscaledPolynomial p : PowerSeries ℚ) := by
  have h0 : PowerSeries.constantCoeff (squareRegularDenominator : PowerSeries ℚ) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, square_regular_denominator_constant] using
      (by norm_num : (2500 : ℚ) ≠ 0)
  unfold actualSquareForcingSeries
  calc
    _ = PowerSeries.C (WPReview.nativeEndpoint p ^ 2) *
        (squareUnscaledPolynomial p : PowerSeries ℚ) *
          ((squareRegularDenominator : PowerSeries ℚ) *
            (squareRegularDenominator : PowerSeries ℚ)⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ h0, mul_one]

theorem square_fixed_numerator_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    squareFixedNumerator ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hx : X ∈ P := X_mem_coefficientSubring R
  have h3 : (1 / 3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have h7 : (1 / 7 : ℚ) ∈ R := small_inverse_integral p 7 (by norm_num) (by omega)
  have h11 : (1 / 11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  have h13 : (1 / 13 : ℚ) ∈ R := small_inverse_integral p 13 (by norm_num) (by omega)
  have h17 : (1 / 17 : ℚ) ∈ R := small_inverse_integral p 17 (by norm_num) (by omega)
  have h2d : (-1 / 4975079484375 : ℚ) ∈ R := by
    rw [show (-1 / 4975079484375 : ℚ) =
      -((1 / 3) ^ 5 * (1 / 5) ^ 6 * (1 / 7) ^ 2 * (1 / 11) ^ 2 *
        (1 / 13) * (1 / 17)) by norm_num]
    exact R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem
      (R.mul_mem (R.mul_mem (R.pow_mem h3 5) (R.pow_mem h5 6)) (R.pow_mem h7 2))
        (R.pow_mem h11 2)) h13) h17)
  have h5d : (1 / 38387958984375 : ℚ) ∈ R := by
    rw [show (1 / 38387958984375 : ℚ) =
      (1 / 3) * (1 / 5) ^ 10 * (1 / 7) ^ 2 * (1 / 11) ^ 2 *
        (1 / 13) * (1 / 17) by norm_num]
    exact R.mul_mem (R.mul_mem (R.mul_mem
      (R.mul_mem (R.mul_mem h3 (R.pow_mem h5 10)) (R.pow_mem h7 2))
        (R.pow_mem h11 2)) h13) h17
  have hN (i : Fin 6) : primitiveNumerator i ∈ P := by
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
  unfold squareFixedNumerator
  exact P.mul_mem (P.mul_mem (natCast_mem P 20250)
    (P.sub_mem P.one_mem hx))
    (P.add_mem (P.mul_mem (C_mem_coefficientSubring R _ h2d) (hN 2))
      (P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ h5d) (P.pow_mem hx 3)) (hN 5)))

theorem square_regular_denominator_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    squareRegularDenominator ∈ coefficientSubring (integralSubring p) := by
  let P := coefficientSubring (integralSubring p)
  have hx : X ∈ P := X_mem_coefficientSubring (integralSubring p)
  have he : escape ∈ P := P.sub_mem (P.mul_mem (natCast_mem P 99) hx) (natCast_mem P 50)
  exact P.mul_mem (P.sub_mem P.one_mem (literal_lambda_integral p hp)) (P.pow_mem he 2)

theorem square_unscaled_polynomial_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    squareUnscaledPolynomial p ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hc : (729 / 15625 : ℚ) ∈ R := by
    rw [show (729 / 15625 : ℚ) = 729 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  exact P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ (R.pow_mem hc p))
    (P.pow_mem (X_mem_coefficientSubring R) (3 * p - 5)))
    (square_fixed_numerator_integral p hp)

theorem actual_square_forcing_coefficient_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 6 (PowerSeries.coeff k (actualSquareForcingSeries p)) := by
  let R := integralSubring p
  have h2 : (1 / 2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hD := (mem_coefficientSubring R _).mp (square_regular_denominator_integral p (by omega))
  have hN := (mem_coefficientSubring R _).mp (square_unscaled_polynomial_integral p hp)
  have hinv : (PowerSeries.constantCoeff (squareRegularDenominator : PowerSeries ℚ))⁻¹ ∈ R := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      square_regular_denominator_constant]
    rw [show (2500 : ℚ)⁻¹ = (1 / 2) ^ 2 * (1 / 5) ^ 4 by norm_num]
    exact R.mul_mem (R.pow_mem h2 2) (R.pow_mem h5 4)
  have hDi := integral_series_inverse R (squareRegularDenominator : PowerSeries ℚ)
    (fun i => by simpa only [Polynomial.coeff_coe] using hD i) hinv
  unfold actualSquareForcingSeries
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  apply precisionZero_mul_integral p 6
  · apply Or.inr
    rw [actual_native_square_endpoint_valuation p (by omega)]
    norm_num
  · apply R.sum_mem
    intro a _ha
    exact R.mul_mem (by simpa only [Polynomial.coeff_coe] using hN a.1) (hDi a.2)

theorem actual_square_forcing_lower_order (p k : ℕ) (hk : k < 3 * p - 5) :
    PowerSeries.coeff k (actualSquareForcingSeries p) = 0 := by
  have hform : actualSquareForcingSeries p = PowerSeries.X ^ (3 * p - 5) *
      (PowerSeries.C (WPReview.nativeEndpoint p ^ 2 * (729 / 15625 : ℚ) ^ p) *
        (squareFixedNumerator : PowerSeries ℚ) *
          (squareRegularDenominator : PowerSeries ℚ)⁻¹) := by
    simp only [actualSquareForcingSeries, squareUnscaledPolynomial,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      map_mul]
    ring
  rw [hform, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem integral_taylor_polynomial (R : Subring ℚ) (F : ℚ[X]) (r : ℚ)
    (hF : F ∈ coefficientSubring R) (hr : r ∈ R) :
    taylor r F ∈ coefficientSubring R := by
  let P := coefficientSubring R
  have hcoeff := (mem_coefficientSubring R F).mp hF
  have hrep : taylor r F = ∑ n ∈ Finset.range (F.natDegree + 1),
      C (F.coeff n) * (X + C r) ^ n := by
    rw [taylor_apply]
    conv_lhs => rw [F.as_sum_range_C_mul_X_pow]
    simp only [sum_comp, C_mul_comp, X_pow_comp]
  rw [hrep]
  apply P.sum_mem
  intro n _hn
  exact P.mul_mem (C_mem_coefficientSubring R _ (hcoeff n))
    (P.pow_mem (P.add_mem (X_mem_coefficientSubring R) (C_mem_coefficientSubring R _ hr)) n)

/-- The regular factor multiplying e^-2 in the actual square forcing at escape. -/
noncomputable def actualSquareEscapeSeries (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (WPReview.nativeEndpoint p ^ 2) *
    (taylor escapePoint (squareUnscaledPolynomial p) : PowerSeries ℚ) *
      (taylor escapePoint (1 - lam) : PowerSeries ℚ)⁻¹

theorem actual_square_escape_coefficient_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 6 (PowerSeries.coeff k (actualSquareEscapeSeries p)) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have h3 : (1 / 3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h7 : (1 / 7 : ℚ) ∈ R := small_inverse_integral p 7 (by norm_num) (by omega)
  have h11 : (1 / 11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  have hr : escapePoint ∈ R := by
    rw [escapePoint, show (50 / 99 : ℚ) = 50 * (1 / 3) ^ 2 * (1 / 11) by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 50) (R.pow_mem h3 2)) h11
  have hN := (mem_coefficientSubring R _).mp (integral_taylor_polynomial R
    (squareUnscaledPolynomial p) escapePoint (square_unscaled_polynomial_integral p hp) hr)
  have hD := (mem_coefficientSubring R _).mp (integral_taylor_polynomial R
    (1 - lam) escapePoint (P.sub_mem P.one_mem (literal_lambda_integral p (by omega))) hr)
  have hinv : (PowerSeries.constantCoeff (taylor escapePoint (1 - lam) : PowerSeries ℚ))⁻¹ ∈ R := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      taylor_coeff_zero]
    norm_num [escapePoint, lam]
    rw [show (1331 / 1323 : ℚ) = 1331 * (1 / 3) ^ 3 * (1 / 7) ^ 2 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 1331) (R.pow_mem h3 3)) (R.pow_mem h7 2)
  have hDi := integral_series_inverse R (taylor escapePoint (1 - lam) : PowerSeries ℚ)
    (fun i => by simpa only [Polynomial.coeff_coe] using hD i) hinv
  unfold actualSquareEscapeSeries
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul]
  apply precisionZero_mul_integral p 6
  · apply Or.inr
    rw [actual_native_square_endpoint_valuation p (by omega)]
    norm_num
  · apply R.sum_mem
    intro a _ha
    exact R.mul_mem (by simpa only [Polynomial.coeff_coe] using hN a.1) (hDi a.2)

end WPForcedSourceStokes
