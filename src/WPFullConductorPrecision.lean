import WPActualSquareForcing
import WPReview.GammaPrecision

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

open WPFiniteConductorPolynomial

set_option maxHeartbeats 1000000

theorem coefficient_derivative_integral (R : Subring ℚ) (F : ℚ[X])
    (hF : F ∈ coefficientSubring R) : derivative F ∈ coefficientSubring R := by
  rw [mem_coefficientSubring]
  intro k
  rw [coeff_derivative]
  simpa only [Nat.cast_add, Nat.cast_one] using
    R.mul_mem ((mem_coefficientSubring R _).mp hF (k + 1)) (natCast_mem R (k + 1))

theorem literal_scaled_kernel_integral (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    scaledKernel k ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have hx : X ∈ P := X_mem_coefficientSubring R
  have h2 : (1 / 2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h3 : (1 / 3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hc : (27 / 1000 : ℚ) ∈ R := by
    rw [show (27 / 1000 : ℚ) = 27 * (1 / 2) ^ 3 * (1 / 5) ^ 3 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 27) (R.pow_mem h2 3)) (R.pow_mem h5 3)
  have hLRc : (1953125 / 209952 : ℚ) ∈ R := by
    rw [show (1953125 / 209952 : ℚ) = 1953125 * (1 / 2) ^ 5 * (1 / 3) ^ 8 by norm_num]
    exact R.mul_mem (R.mul_mem (natCast_mem R 1953125) (R.pow_mem h2 5)) (R.pow_mem h3 8)
  have hL : LP20 ∈ P := by
    unfold LP20
    repeat' first
      | exact hx
      | exact natCast_mem P _
      | exact C_mem_coefficientSubring R _ hLRc
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have hR : RP20 ∈ P := by
    unfold RP20
    repeat' first
      | exact hx
      | exact natCast_mem P _
      | exact C_mem_coefficientSubring R _ hLRc
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have hm : m ∈ P := by
    unfold m
    repeat' first
      | exact hx
      | exact natCast_mem P _
      | exact C_mem_coefficientSubring R _ hc
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have he : ell ∈ P := P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ hc) hx)
    (P.sub_mem (P.mul_mem (natCast_mem P 9) hx) (natCast_mem P 16))
  have hM : collision ∈ P := P.sub_mem (natCast_mem P 25) (P.mul_mem (natCast_mem P 9) hx)
  have hl : lam ∈ P := literal_lambda_integral p hp
  have hmd : derivative m ∈ P := coefficient_derivative_integral R _ hm
  have hed : derivative ell ∈ P := coefficient_derivative_integral R _ he
  have hld : derivative lam ∈ P := coefficient_derivative_integral R _ hl
  have hK : K ∈ P := by
    unfold K
    repeat' first
      | exact hx
      | exact P.one_mem
      | exact natCast_mem P _
      | exact he
      | exact hed
      | exact hM
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have hG0 : G0 ∈ P := by
    unfold G0
    repeat' first
      | exact hx
      | exact P.one_mem
      | exact natCast_mem P _
      | exact hL
      | exact hR
      | exact he
      | exact hM
      | exact hmd
      | exact hld
      | exact hm
      | exact hK
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have hG1 : G1 ∈ P := by
    unfold G1
    repeat' first
      | exact hx
      | exact P.one_mem
      | exact natCast_mem P _
      | exact hL
      | exact hR
      | exact he
      | exact hM
      | exact hmd
      | exact hm
      | exact hK
      | apply P.mul_mem
      | apply P.add_mem
      | apply P.sub_mem
      | apply P.neg_mem
  have hG2 : G2 ∈ P := P.mul_mem (P.mul_mem (natCast_mem P 12)
    (P.sub_mem P.one_mem hx)) hL
  have hInput (n : ℕ) : kernelInput n ∈ P := by
    rcases n with (_ | (_ | (_ | (_ | n))))
    · exact hG0
    · exact P.sub_mem hG1 hG0
    · exact P.sub_mem hG2 hG1
    · exact P.neg_mem hG2
    · exact P.zero_mem
  induction k using Nat.twoStepInduction with
  | zero => exact hInput 0
  | one =>
    exact P.add_mem (P.mul_mem (P.mul_mem (natCast_mem P 2) hm) (hInput 0))
      (P.mul_mem hl (hInput 1))
  | more k hk hk1 =>
    rw [scaledKernel]
    exact P.add_mem (P.sub_mem (P.mul_mem (P.mul_mem (natCast_mem P 2) hm) hk1)
      (P.mul_mem hl hk)) (P.mul_mem (P.pow_mem hl (k + 2)) (hInput (k + 2)))

noncomputable def conductorRegularDenominator : ℚ[X] := collision * escape ^ 2

/-- An uncanceled top term after removing its actual factor x^5. -/
noncomputable def retainedTopPolynomial (n k : ℕ) : ℚ[X] :=
  C (2 * WPReview.nativeCoefficient n) * C ((729 / 15625 : ℚ) ^ (n + 1)) *
    X ^ (3 * (n + 1) - 5) * scaledKernel k

theorem retained_top_cusp_attachment (n k : ℕ) (hn : 5 ≤ 3 * (n + 1)) :
    X ^ 5 * retainedTopPolynomial n k =
      C (2 * WPReview.nativeCoefficient n) * lam ^ (n + 1) * scaledKernel k := by
  unfold retainedTopPolynomial lam
  simp only [mul_pow, ← pow_mul, ← map_pow]
  rw [show X ^ (3 * (n + 1)) = X ^ 5 * X ^ (3 * (n + 1) - 5) by
    rw [← pow_add, show 5 + (3 * (n + 1) - 5) = 3 * (n + 1) by omega]]
  ring

theorem original_full_numerator_regularized (p : ℕ) (hp : 4 ≤ p) :
    originalNumerator p (p - 2) = X ^ 5 *
      (conductorRegularDenominator * Be p (p - 4) +
        retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0) := by
  rw [original_full_numerator_split p hp]
  have ht1 : C (2 * WPReview.nativeCoefficient (p - 3)) * lam ^ (p - 2) * scaledKernel 1 =
      X ^ 5 * retainedTopPolynomial (p - 3) 1 := by
    rw [retained_top_cusp_attachment _ _ (by omega), show p - 3 + 1 = p - 2 by omega]
  have ht0 : C (2 * WPReview.nativeCoefficient (p - 2)) * lam ^ (p - 1) * scaledKernel 0 =
      X ^ 5 * retainedTopPolynomial (p - 2) 0 := by
    rw [retained_top_cusp_attachment _ _ (by omega), show p - 2 + 1 = p - 1 by omega]
  rw [ht1, ht0]
  simp only [sourceDivisor, conductorRegularDenominator]
  ring

/-- The actual full conductor's Taylor series, with both top terms retained. -/
noncomputable def fullConductorSeries (p : ℕ) : PowerSeries ℚ :=
  (Be p (p - 4) : PowerSeries ℚ) +
    ((retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0 : ℚ[X]) : PowerSeries ℚ) *
      (conductorRegularDenominator : PowerSeries ℚ)⁻¹

theorem original_full_conductor_regular_formula (p : ℕ) (hp : 4 ≤ p) (x : ℚ)
    (hx : x ≠ 0) (hM : collision.eval x ≠ 0) (hE : escape.eval x ≠ 0) :
    originalBe p (p - 1) x = (Be p (p - 4)).eval x +
      ((retainedTopPolynomial (p - 3) 1).eval x +
        (retainedTopPolynomial (p - 2) 0).eval x) /
          (collision.eval x * (escape.eval x) ^ 2) := by
  rw [original_full_Be_numerator p (by omega) x hx hM hE,
    original_full_numerator_regularized p hp]
  simp only [sourceDivisor, conductorRegularDenominator,
    eval_add, eval_mul, eval_pow, eval_X]
  field_simp [hx, hM, hE]
  ring

theorem conductor_regular_denominator_integral (p : ℕ) [Fact p.Prime] :
    conductorRegularDenominator ∈ coefficientSubring (integralSubring p) := by
  let P := coefficientSubring (integralSubring p)
  have hx : X ∈ P := X_mem_coefficientSubring (integralSubring p)
  have hM : collision ∈ P := P.sub_mem (natCast_mem P 25) (P.mul_mem (natCast_mem P 9) hx)
  have he : escape ∈ P := P.sub_mem (P.mul_mem (natCast_mem P 99) hx) (natCast_mem P 50)
  exact P.mul_mem hM (P.pow_mem he 2)

theorem conductor_regular_denominator_constant : conductorRegularDenominator.coeff 0 = 62500 := by
  norm_num [conductorRegularDenominator, collision, escape, pow_two, coeff_mul]

theorem retained_top_coefficient_precision (p n j k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (hhigh : p - 3 ≤ n) :
    precisionZero p 3 ((retainedTopPolynomial n j).coeff k) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hc : (729 / 15625 : ℚ) ∈ R := by
    rw [show (729 / 15625 : ℚ) = 729 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  have hk : C ((729 / 15625 : ℚ) ^ (n + 1)) * X ^ (3 * (n + 1) - 5) * scaledKernel j ∈ P :=
    P.mul_mem (P.mul_mem (C_mem_coefficientSubring R _ (R.pow_mem hc (n + 1)))
      (P.pow_mem (X_mem_coefficientSubring R) _)) (literal_scaled_kernel_integral p j (by omega))
  have hnative : precisionZero p 3 (WPReview.nativeCoefficient n) := by
    apply Or.inr
    rw [native_top_three_valuation p n hp hn hhigh]
    norm_num
  have hc2 : precisionZero p 3 (2 * WPReview.nativeCoefficient n) := by
    rw [mul_comm]
    exact precisionZero_mul_integral p 3 _ _ hnative (natCast_mem R 2)
  unfold retainedTopPolynomial
  rw [mul_assoc, mul_assoc, ← mul_assoc (C ((729 / 15625 : ℚ) ^ (n + 1))), coeff_C_mul]
  exact precisionZero_mul_integral p 3 _ _ hc2 ((mem_coefficientSubring R _).mp hk k)

/-- Full-to-short precision retains the actual uncanceled two top terms. -/
theorem actual_full_short_conductor_coefficient_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 3 (PowerSeries.coeff k
      (fullConductorSeries p - (Be p (p - 1 - p / 6) : PowerSeries ℚ))) := by
  let R := integralSubring p
  have h2 : (1 / 2 : ℚ) ∈ R := small_inverse_integral p 2 (by norm_num) (by omega)
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hD := (mem_coefficientSubring R _).mp (conductor_regular_denominator_integral p)
  have h0 : (PowerSeries.constantCoeff (conductorRegularDenominator : PowerSeries ℚ))⁻¹ ∈ R := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      conductor_regular_denominator_constant]
    rw [show (62500 : ℚ)⁻¹ = (1 / 2) ^ 2 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (R.pow_mem h2 2) (R.pow_mem h5 6)
  have hDi := integral_series_inverse R (conductorRegularDenominator : PowerSeries ℚ)
    (fun i => by simpa only [Polynomial.coeff_coe] using hD i) h0
  have hform : fullConductorSeries p - (Be p (p - 1 - p / 6) : PowerSeries ℚ) =
      ((Be p (p - 4) - Be p (p - 1 - p / 6) : ℚ[X]) : PowerSeries ℚ) +
        ((retainedTopPolynomial (p - 3) 1 + retainedTopPolynomial (p - 2) 0 : ℚ[X]) : PowerSeries ℚ) *
          (conductorRegularDenominator : PowerSeries ℚ)⁻¹ := by
    simp only [fullConductorSeries, Polynomial.coe_sub]
    ring
  rw [hform, map_add]
  apply precisionZero_add p 3
  · simpa only [Polynomial.coeff_coe] using canceled_full_short_conductor_precision p hp k
  · rw [PowerSeries.coeff_mul]
    apply precisionZero_sum
    intro a _ha
    apply precisionZero_mul_integral p 3
    · rw [Polynomial.coeff_coe, coeff_add]
      exact precisionZero_add p 3 _ _
        (retained_top_coefficient_precision p (p - 3) 1 a.1 hp (by omega) le_rfl)
        (retained_top_coefficient_precision p (p - 2) 0 a.1 hp (by omega) (by omega))
    · exact hDi a.2

theorem precisionZero_mul (p k l : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : precisionZero p k a) (hb : precisionZero p l b) : precisionZero p (k + l) (a * b) := by
  rcases ha with rfl | ha
  · exact Or.inl (by simp)
  rcases hb with rfl | hb
  · exact Or.inl (by simp)
  by_cases ha0 : a = 0
  · exact Or.inl (by simp [ha0])
  by_cases hb0 : b = 0
  · exact Or.inl (by simp [hb0])
  apply Or.inr
  rw [padicValRat.mul ha0 hb0]
  omega

theorem actual_full_short_source_coefficient_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 6 (WPReview.nativeEndpoint p * PowerSeries.coeff k
      (fullConductorSeries p - (Be p (p - 1 - p / 6) : PowerSeries ℚ))) := by
  have hA : precisionZero p 3 (WPReview.nativeEndpoint p) := by
    apply Or.inr
    rw [actual_native_endpoint_valuation p (by omega)]
    norm_num
  exact precisionZero_mul p 3 3 _ _ hA (actual_full_short_conductor_coefficient_precision p hp k)

theorem Gamma_scalar (L : ℕ) (c : ℚ) (f : ℕ → ℚ) :
    WPReview.Gamma L (fun k => c * f k) = c * WPReview.Gamma L f := by
  unfold WPReview.Gamma
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The literal full conductor may be replaced by the original short cutoff after the source multiplier. -/
theorem actual_full_short_conductor_Gamma_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : WPReview.RationalCongruent p 5
      (WPReview.nativeEndpoint p * WPReview.Gamma (3 * p - 1)
        (fun k => PowerSeries.coeff k (fullConductorSeries p)))
      (WPReview.nativeEndpoint p * WPReview.Gamma (3 * p - 1)
        (fun k => (Be p (p - 1 - p / 6)).coeff k)) := by
  have hfg (k : ℕ) (_hk : k ≤ 3 * p - 1) : WPReview.RationalCongruent p 6
      (WPReview.nativeEndpoint p * PowerSeries.coeff k (fullConductorSeries p))
      (WPReview.nativeEndpoint p * (Be p (p - 1 - p / 6)).coeff k) := by
    have h := actual_full_short_source_coefficient_precision p hp k
    have hd : WPReview.nativeEndpoint p * PowerSeries.coeff k (fullConductorSeries p) -
        WPReview.nativeEndpoint p * (Be p (p - 1 - p / 6)).coeff k =
          WPReview.nativeEndpoint p * PowerSeries.coeff k
            (fullConductorSeries p - (Be p (p - 1 - p / 6) : PowerSeries ℚ)) := by
      rw [map_sub, Polynomial.coeff_coe]
      ring
    rcases h with h | h
    · exact Or.inl (sub_eq_zero.mp (hd.trans h))
    · exact Or.inr (by simpa only [hd] using h)
  have h := WPReview.Gamma_p6_to_p5 p (3 * p - 1) Fact.out (by omega) le_rfl _ _ hfg
  simpa only [Gamma_scalar] using h

theorem actual_square_forcing_Gamma_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : WPReview.RationalCongruent p 5
      (WPReview.Gamma (3 * p - 1) (fun k => PowerSeries.coeff k (actualSquareForcingSeries p))) 0 := by
  have hfg (k : ℕ) (_hk : k ≤ 3 * p - 1) : WPReview.RationalCongruent p 6
      (PowerSeries.coeff k (actualSquareForcingSeries p)) 0 := by
    have h := actual_square_forcing_coefficient_precision p hp k
    simpa only [WPReview.RationalCongruent, sub_zero, precisionZero] using h
  have h := WPReview.Gamma_p6_to_p5 p (3 * p - 1) Fact.out (by omega) le_rfl _ _ hfg
  simpa only [WPReview.Gamma, mul_zero, Finset.sum_const_zero] using h

end WPForcedSourceStokes
