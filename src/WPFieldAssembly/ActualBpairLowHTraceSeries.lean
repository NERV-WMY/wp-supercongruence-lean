import WPFieldAssembly.ActualBpairLowHCanonicalSource
import WPFieldAssembly.ActualBpairLowHSquareHom
import WPFieldAssembly.ActualBpairLowHTraceDensityAlgebra
import WPFieldAssembly.ActualBpairLowHTraceFunctional

open scoped Polynomial PowerSeries LaurentSeries LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The entire original trace numerator is transported, with all eight finite signed bands. -/
theorem lowH_trace_square_series_numerator (p : ℕ) :
    lowHFiniteSeriesHom (lowHSquareSource (lowHOriginalTraceNumerator (K := K) p)) =
      ((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ (2 * p)) + 1) *
        (4 * (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2) - 11) *
        (((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^
          (2 * ((p - 1) / 2)))⁻¹) - 1) := by
  simp only [lowHOriginalTraceNumerator, map_mul, map_add, map_sub, map_one, map_ofNat,
    lowHSquareSource_T, lowHFiniteSeries_T, mul_one, mul_neg]
  have htwo : (HahnSeries.single (2 : ℤ) (1 : K) : LaurentSeries K) =
      (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ^ (2 : ℕ) := by
    simpa only [Nat.cast_ofNat] using RatFunc.single_one_eq_pow (R := K) 2
  rw [show -(2 * (((p - 1) / 2 : ℕ) : ℤ)) = -2 * (((p - 1) / 2 : ℕ) : ℤ) by ring,
    lowH_canonical_negative_phase (K := K) ((p - 1) / 2),
    show 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) by omega,
    RatFunc.single_one_eq_pow (2 * p), htwo]
  simp only [← PowerSeries.coe_X]

/-- This coefficient is derived from the actual two-pole quotient and its literal tame Jacobian. -/
theorem lowH_trace_square_quotient_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (algebraMap K (LaurentSeries K) (1 / 10 : K) *
      (HahnSeries.single 1 (2 : K) *
        (lowHFiniteSeriesHom (lowHSquareSource (lowHOriginalTraceNumerator p)) /
          lowHFiniteSeriesHom (lowHSquareSource ((WPFiniteZSource.Abar : K[X]).toLaurent))))).coeff (-1) =
      (1 / 5 : K) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single_mul,
    sub_zero, lowHSeriesSquareHom_quotient_residue,
    lowHFiniteSeries_Abar_quotient_residue p hp, lowH_original_trace_functional p hp,
    mul_one]
  field_simp [h5, h10]
  ring

/-- The literal cleared Dsym source yields the whole quotient trace density in both inverse germs. -/
theorem lowHConicCanonical_trace_density_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
      LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p))) *
      ((Polynomial.aeval (lowHConicCanonicalT ε hu η) (lowHTripleC : K[X]) : PowerSeries K) : LaurentSeries K) =
    algebraMap K (LaurentSeries K) (1 / 10 : K) *
      (HahnSeries.single 1 (2 : K) *
        (lowHFiniteSeriesHom (lowHSquareSource (lowHOriginalTraceNumerator p)) /
          lowHFiniteSeriesHom (lowHSquareSource ((WPFiniteZSource.Abar : K[X]).toLaurent)))) := by
  let τ : LaurentSeries K := (lowHConicCanonicalT ε hu η : PowerSeries K)
  let w : LaurentSeries K := (PowerSeries.X : PowerSeries K)
  let d : LaurentSeries K := LaurentSeries.derivative K
    (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p)))
  let : CharP (LaurentSeries K) p :=
    charP_of_injective_ringHom (RingHom.injective (algebraMap K (LaurentSeries K))) p
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h5L : (5 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (5 : K) ≠ 0
    exact HahnSeries.C_ne_zero h5
  have hc : 5 * τ ^ 2 = w ^ 2 + 1 := by
    have he := congrArg (HahnSeries.ofPowerSeries ℤ K)
      (lowHConicCanonical_relation p hp ε hε hu η hη)
    simpa only [map_mul, map_pow, map_add, map_one, map_ofNat] using he
  have haP : ((4 - PowerSeries.X ^ 2) * (4 * PowerSeries.X ^ 2 - 1) : PowerSeries K) ≠ 0 := by
    intro hz
    have he := congrArg PowerSeries.constantCoeff hz
    simp only [map_mul, map_sub, map_pow, map_ofNat, map_one, map_zero,
      PowerSeries.constantCoeff_X, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero] at he
    exact h4 (by linear_combination -he)
  have ha : (4 - w ^ 2) * (4 * w ^ 2 - 1) ≠ 0 := by
    intro hz
    apply haP
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    simpa only [map_mul, map_sub, map_pow, map_ofNat, map_one, map_zero] using hz
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have he := lowH_conic_trace_density p ((p - 1) / 2) hN τ w d h5L hc ha
    (lowHConicCanonical_Dsym_cleared_source p hp ε hε hu η hη)
  have hTc : ((Polynomial.aeval (lowHConicCanonicalT ε hu η) (lowHTripleC : K[X]) : PowerSeries K) :
      LaurentSeries K) = 4 * τ ^ 3 - 3 * τ := by
    rw [lowH_powerSeries_polynomial_field_eval]
    simp only [lowHTripleC, map_sub, map_mul, map_pow,
      Polynomial.aeval_X, map_ofNat, τ]
  have hJac : (HahnSeries.single 1 (2 : K) : LaurentSeries K) = 2 * w := by
    dsimp only [w]
    rw [PowerSeries.coe_X]
    change HahnSeries.single 1 (2 : K) = HahnSeries.single 0 (2 : K) * HahnSeries.single 1 1
    rw [HahnSeries.single_mul_single, zero_add, mul_one]
  have hcoef : (1 / 10 : K) * 2 = 1 / 5 := by field_simp [h5, h10]; ring
  have hcoefL := congrArg (algebraMap K (LaurentSeries K)) hcoef
  simp only [map_mul, map_div₀, map_one, map_ofNat] at hcoefL
  rw [hTc, he, hJac, lowH_trace_square_series_numerator, lowH_Dsym_square_series_Abar,
    ← PowerSeries.coe_X]
  simp only [map_div₀, map_one, map_ofNat]
  linear_combination -w * ((w ^ (2 * p) + 1) * (4 * w ^ 2 - 11) *
    ((w ^ (2 * ((p - 1) / 2)))⁻¹ - 1) / ((4 - w ^ 2) * (4 * w ^ 2 - 1))) * hcoefL

/-- The original trace is evaluated only after its full quotient and factor two are attached. -/
theorem lowHConicCanonical_trace_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    ((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
      LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p))) *
      ((Polynomial.aeval (lowHConicCanonicalT ε hu η) (lowHTripleC : K[X]) : PowerSeries K) :
        LaurentSeries K)).coeff (-1)) = (1 / 5 : K) := by
  rw [lowHConicCanonical_trace_density_source p hp ε hε hu η hη]
  exact lowH_trace_square_quotient_residue p hp

end WPFieldAssembly.ActualBpairContraction
