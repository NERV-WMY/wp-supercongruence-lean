import WPActualAngularEndpoint
import WPActualEtaUnits
import WPActualHighValuation
import WPActualSourceCoefficients

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 2000000

/-- The full high angular tail is an actual finite sum of the selected literal native coefficients. -/
theorem actual_angular_high_term_expansion (p a : ℕ) (hp : 3≤p) (ha : p+3≤a) :
    RatFunc.C (WPReview.nativeEndpoint p) *
        ((actualEtaNativePolynomial p).coeff a*lambda^a/lambda^3) =
      ∑ i : Fin 3, ∑ n ∈ Finset.range p,
        if p-3≤n then
          RatFunc.C (WPReview.nativeEndpoint p*((n : ℚ)^i.val*WPReview.nativeCoefficient n)) *
            ((etaClearedPolynomial i 2).coeff (a-n)*lambda^a/lambda^3)
        else 0 := by
  classical
  rw [actual_angular_high_coefficient p a hp ha]
  simp only [Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hh : p-3≤n
  · simp only [if_pos hh, map_mul]
    ring
  · rw [if_neg hh, if_neg hh]
    ring

/-- Every Laurent coefficient of the actual high angular error has precision six. -/
theorem actual_angular_high_error_origin_precision (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (k : ℤ) :
    precisionZero p 6 (actualRationalCoefficient
      (RatFunc.C (WPReview.nativeEndpoint p)*actualAngularHighError p) k) := by
  classical
  let R := WPFiniteConductorPolynomial.integralSubring p
  let I := integralRationalOrigin R
  have hlam : lambda ∈ I := actual_lambda_origin_integral p hp
  have hlaminv : lambda⁻¹ ∈ I := actual_lambda_inverse_origin_integral p hp
  have hη (i : Fin 3) (a : ℕ) : (etaClearedPolynomial i 2).coeff a ∈ I :=
    (mem_polynomialCoefficientSubring I _).mp (eta_cleared_polynomial_integral p hp i 2) a
  have hg (i : Fin 3) (a n : ℕ) :
      (etaClearedPolynomial i 2).coeff (a-n)*lambda^a/lambda^3 ∈ I := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact I.mul_mem (I.mul_mem (hη i (a-n)) (I.pow_mem hlam a)) (I.pow_mem hlaminv 3)
  unfold actualAngularHighError
  rw [Finset.mul_sum, actual_rational_coefficient_sum]
  apply precisionZero_sum
  intro a _ha
  by_cases ha : p+3≤a
  · rw [if_pos ha, actual_angular_high_term_expansion p a (by omega) ha]
    rw [actual_rational_coefficient_sum]
    apply precisionZero_sum
    intro i _hi
    rw [actual_rational_coefficient_sum]
    apply precisionZero_sum
    intro n hn
    by_cases hh : p-3≤n
    · rw [if_pos hh, actual_rational_coefficient_scalar]
      exact precisionZero_mul_integral p 6 _ _
        (actual_endpoint_weighted_top_three_precision p n i.val hp (Finset.mem_range.mp hn) hh)
        (hg i a n k)
    · rw [if_neg hh]
      exact Or.inl (by simp [actualRationalCoefficient, actualRationalSeries])
  · rw [if_neg ha, mul_zero]
    exact Or.inl (by simp [actualRationalCoefficient, actualRationalSeries])

end

end WPForcedSourceStokes
