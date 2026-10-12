import WPFieldAssembly.ActualBpairLowHBranchQuadratic
import WPFieldAssembly.ActualBpairLowHWeightedIntegral
import WPFieldAssembly.ActualBpairLowHTraceSeries

open scoped Polynomial PowerSeries LaurentSeries LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The original Js is the literal finite weighted branch density, including its origin coefficient. -/
theorem lowHBranchJs_weighted_source (p : ℕ) (H : K[X]) :
    lowHBranchJs p H =
      (Dsym p * (lowHWeightedBranchDensity ((p - 1) / 2) H).toLaurent).coeff (-1) := by
  simp only [lowHBranchJs, lowHWeightedBranchDensity, lowHBranchYQuotient,
    lowHLinearS, WPFiniteWSource.squaredCoordinate, map_mul, map_pow]
  congr 1
  ring

/-- The full even contraction identifies the actual finite primitive in the genuine conic germ. -/
theorem lowHConicCanonical_weighted_primitive_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent) =
      algebraMap K (LaurentSeries K) (2 / 15 : K) *
        ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
        ((Polynomial.aeval (lowHConicCanonicalT ε hu η)
          ((lowHEulerJ p H).comp lowHTripleC) : PowerSeries K) : LaurentSeries K) := by
  have hb := lowH_prime_six_band p hp
  have hcomp : (lowHWeightedXPrimitive p H).comp lowHQuadraticX = lowHWeightedTPrimitive p H := by
    rw [lowHWeightedXPrimitive, comp_assoc, lowHLinearS_quadratic_source p hp,
      ← expand_eq_comp_X_pow, lowHWeightedTPrimitive_expand p hp (p / 6) (by omega) hb.2 H hH]
  have hU : Polynomial.aeval
      ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) (lowHQuadraticX : K[X]) =
        (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2) := by
    have hc := congrArg (HahnSeries.ofPowerSeries ℤ K)
      (lowHConicCanonical_relation p hp ε hε hu η hη)
    simp only [map_mul, map_pow, map_add, map_one, map_ofNat] at hc
    simp only [lowHQuadraticX, map_sub, map_mul, map_pow, map_one,
      Polynomial.aeval_X, map_ofNat]
    linear_combination hc
  rw [lowHFiniteSeries_square_polynomial, ← hU, ← Polynomial.aeval_comp, hcomp,
    lowH_powerSeries_polynomial_field_eval]
  simp only [lowHWeightedTPrimitive, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

/-- Finite-series IBP retains the entire square source and the literal factor-two Js coefficient. -/
theorem lowHBranchJs_whole_finite_IBP (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
      lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent)).coeff (-1) +
      2 * lowHBranchJs p H = 0 := by
  have hb := lowH_prime_six_band p hp
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have hder := lowHSquareSource_derivative (lowHWeightedXPrimitive p H).toLaurent
  rw [D_toLaurent, lowHWeightedXPrimitive_derivative p ((p - 1) / 2) hp hN
    (p / 6) (by omega) hb.2 H hH] at hder
  have hQ : LaurentSeries.derivative K
      (lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent)) =
        lowHFiniteSeriesHom (LaurentPolynomial.C (2 : K) * T 1 *
          lowHSquareSource (lowHWeightedBranchDensity ((p - 1) / 2) H).toLaurent) := by
    change LaurentSeries.derivative K (lowHFiniteSeries (K := K) _) =
      lowHFiniteSeries (K := K) _
    rw [← lowHFiniteSeries_derivative, hder]
  have hdensity : lowHFiniteSeriesHom (lowHSquareSource (Dsym p)) *
      LaurentSeries.derivative K
        (lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent)) =
        lowHFiniteSeriesHom (LaurentPolynomial.C (2 : K) * T 1 *
          lowHSquareSource (Dsym p * (lowHWeightedBranchDensity ((p - 1) / 2) H).toLaurent)) := by
    rw [hQ]
    simp only [map_mul]
    ring
  have he := lowH_finite_series_IBP (lowHSquareSource (Dsym p))
    (lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent))
  rw [lowHFiniteSeries_derivative] at he
  change (LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
      lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent)).coeff (-1) +
    (lowHFiniteSeriesHom (lowHSquareSource (Dsym p)) * LaurentSeries.derivative K
      (lowHFiniteSeriesHom (lowHSquareSource (lowHWeightedXPrimitive p H).toLaurent))).coeff (-1) = 0 at he
  rw [hdensity] at he
  change _ + (lowHFiniteSeries _).coeff (-1) = 0 at he
  rw [lowHFiniteSeries_coeff, lowHSquareSource_residue, ← lowHBranchJs_weighted_source] at he
  exact he

/-- The whole Euler correction is removed by its proved quartic primitive, leaving the literal trace. -/
theorem lowHConicCanonical_Euler_period_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    ((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
      LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
      ((Polynomial.aeval (lowHConicCanonicalT ε hu η) ((lowHEulerJ p H).comp lowHTripleC) :
        PowerSeries K) : LaurentSeries K)).coeff (-1)) = (lowHEulerJ p H).eval 1 / 5 := by
  let τ : LaurentSeries K := (lowHConicCanonicalT ε hu η : PowerSeries K)
  let d : LaurentSeries K :=
    LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p)))
  let j := (lowHEulerJ p H).eval 1
  have hz := lowHConicCanonical_Dsym_EulerDelta_residue p hp ε hε hu η hη H hH
  rw [lowH_powerSeries_polynomial_field_eval] at hz
  simp only [lowHEulerDelta, map_sub, map_mul, Polynomial.aeval_C, mul_sub,
    HahnSeries.coeff_sub] at hz
  have ht := lowHConicCanonical_trace_residue p hp ε hε hu η hη
  rw [lowH_powerSeries_polynomial_field_eval] at ht
  have hc : (τ ^ p * d *
      (algebraMap K (LaurentSeries K) j * Polynomial.aeval τ (lowHTripleC : K[X]))).coeff (-1) =
        j * (τ ^ p * d * Polynomial.aeval τ (lowHTripleC : K[X])).coeff (-1) := by
    rw [show τ ^ p * d * (algebraMap K (LaurentSeries K) j * Polynomial.aeval τ (lowHTripleC : K[X])) =
        algebraMap K (LaurentSeries K) j * (τ ^ p * d * Polynomial.aeval τ (lowHTripleC : K[X])) by ring,
      LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero]
  rw [hc, ht] at hz
  rw [lowH_powerSeries_polynomial_field_eval]
  simpa only [j, div_eq_mul_inv, one_div, one_mul] using sub_eq_zero.mp hz

/-- The original Js is derived from full finite IBP, both conic phases and the two-pole trace. -/
theorem lowHBranchJs_conic_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    lowHBranchJs p H = -(lowHEulerJ p H).eval 1 / 75 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have hunit : (2 : K) * (1 / 2) = 1 := mul_one_div_cancel h2
  have he := lowHBranchJs_whole_finite_IBP p hp H hH
  rw [lowHConicCanonical_weighted_primitive_source p hp ε hε hu η hη H hH] at he
  rw [show LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
      (algebraMap K (LaurentSeries K) (2 / 15 : K) *
        ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
        ((Polynomial.aeval (lowHConicCanonicalT ε hu η)
          ((lowHEulerJ p H).comp lowHTripleC) : PowerSeries K) : LaurentSeries K)) =
      algebraMap K (LaurentSeries K) (2 / 15 : K) *
        (((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
          LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
          ((Polynomial.aeval (lowHConicCanonicalT ε hu η)
            ((lowHEulerJ p H).comp lowHTripleC) : PowerSeries K) : LaurentSeries K)) by ring,
    LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single_mul, sub_zero,
    lowHConicCanonical_Euler_period_residue p hp ε hε hu η hη H hH] at he
  apply (eq_div_iff h75).mpr
  field_simp [h5, h15, h75] at he
  linear_combination (1 / 2 : K) * he -
    (75 * lowHBranchJs p H + (lowHEulerJ p H).eval 1) * hunit

end WPFieldAssembly.ActualBpairContraction
