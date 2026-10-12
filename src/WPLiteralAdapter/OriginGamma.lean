import WPActualSourceOriginPrecision
import WPActualNativeMoment
import WPLiteralNativeNormalization
import WPNativeFactorialNormalization
import WPReview.GammaPrecision

open scoped BigOperators
open WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

/-- The exact original literal sum, with the full extended cutoff and true weight. -/
theorem literal_extended_gamma (p : ℕ) :
    WPReview.Gamma (3*p-1)
      (fun k => (WPLiteralNativeNormalization.outerOperator
        (WPLiteralNativeNormalization.outerPolynomial p)).coeff k) =
      WPReview.literalSum p :=
  WPLiteralNativeNormalization.Gamma_outer_literal_extended p

/-- The internal finite factorial/harmonic proof supplies the original native coefficient. -/
theorem native_factorial_normalization (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPReview.RationalCongruent p 3 (WPReview.nativeCoefficient p)
      (120/(1728 : ℚ)^p) :=
  WPNativeFactorialNormalization.native_factorial_normalization p (by omega)

/-- Applying the actual outer moment to the full source error consumes exactly one digit. -/
theorem actual_source_gamma_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPReview.RationalCongruent p 5
      (WPReview.Gamma (3*p-1) (fun k => actualRationalCoefficient (actualTotalSource p) k))
      (WPReview.nativeEndpoint p * WPReview.Gamma (3*p-1)
        (fun k => actualRationalCoefficient (actualBetaFunctional p) k)) := by
  have h := WPReview.Gamma_p6_to_p5 p (3*p-1) Fact.out (by omega) le_rfl
    (fun k => actualRationalCoefficient (actualTotalSource p) k)
    (fun k => WPReview.nativeEndpoint p * actualRationalCoefficient (actualBetaFunctional p) k)
    (by
      intro k _hk
      have hc := actual_source_conductor_error_origin_precision p hp (k : ℤ)
      rw [actual_rational_coefficient_sub, actual_rational_coefficient_scalar] at hc
      rcases hc with hz | hv
      · exact Or.inl (sub_eq_zero.mp hz)
      · exact Or.inr hv)
  have he : WPReview.Gamma (3*p-1)
      (fun k => WPReview.nativeEndpoint p * actualRationalCoefficient (actualBetaFunctional p) k) =
      WPReview.nativeEndpoint p * WPReview.Gamma (3*p-1)
        (fun k => actualRationalCoefficient (actualBetaFunctional p) k) := by
    unfold WPReview.Gamma
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [he] at h
  exact h

/-- Every literal full-cutoff native coefficient is integral. -/
theorem actual_native_coefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7≤p) (hn : n<p) :
    0≤padicValRat p (WPReview.nativeCoefficient n) := by
  rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp hn]
  have h : 3*n/p ≤ 6*n/p := Nat.div_le_div_right (by omega)
  have hz : ((3*n/p : ℕ) : ℤ) ≤ ((6*n/p : ℕ) : ℤ) := by exact_mod_cast h
  omega

/-- The entire actual native moment is integral, including every term n<p. -/
theorem actual_full_native_moment_integral (p : ℕ) [Fact p.Prime] (hp : 7≤p) :
    0≤padicValRat p
      (∑ n∈Finset.range p, WPReview.nativeCoefficient n *
        WPNativeMomentIntegrality.actualMonomialMoment p n) := by
  let R := integralSubring p
  have hm : (∑ n∈Finset.range p, WPReview.nativeCoefficient n *
      WPNativeMomentIntegrality.actualMonomialMoment p n) ∈ R := by
    apply R.sum_mem
    intro n hn
    exact R.mul_mem
      (actual_native_coefficient_integral p n hp (Finset.mem_range.mp hn))
      (WPNativeMomentIntegrality.actual_monomial_moment_integral p n hp (Finset.mem_range.mp hn))
  exact hm

end

end WPLiteralAdapter
