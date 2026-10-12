import WPFieldAssembly.ActualBpairLowHSourceSeries
import WPFieldAssembly.ActualBpairLowHConicDeltaResidue

open scoped Polynomial PowerSeries LaurentSeries LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The entire negative square phase is the inverse of the actual coordinate power. -/
theorem lowH_canonical_negative_phase (N : ℕ) :
    (HahnSeries.single (-2 * (N : ℤ)) (1 : K) : LaurentSeries K) =
      ((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ (2 * N))⁻¹) := by
  rw [RatFunc.single_zpow, ← PowerSeries.coe_X,
    show -2 * (N : ℤ) = -((2 * N : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]

/-- The original squared coordinate becomes tau squared in the genuine inverse germ. -/
theorem lowHConicCanonical_series_square (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2 =
      algebraMap K (LaurentSeries K) (1 / 5 : K) *
        ((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2) + 1) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (HahnSeries.ofPowerSeries ℤ K)
    (lowHConicCanonical_relation p hp ε hε hu η hη)
  simp only [map_mul, map_pow, map_add, map_one, map_ofNat] at hc
  have h5C := congrArg (algebraMap K (LaurentSeries K)) (mul_one_div_cancel h5)
  simp only [map_mul, map_ofNat, map_one] at h5C
  linear_combination algebraMap K (LaurentSeries K) (1 / 5 : K) * hc -
    (((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2) * h5C

/-- This is the complete original Dsym derivative, with both phases and proper ends. -/
theorem lowHConicCanonical_Dsym_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (4 - (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2)) *
        (4 * (((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^ 2) - 1) *
        LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) =
      5 * ((PowerSeries.X : PowerSeries K) : LaurentSeries K) *
        ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^
          (2 * ((p - 1) / 2)) *
        (((((PowerSeries.X : PowerSeries K) : LaurentSeries K) ^
          (2 * ((p - 1) / 2)))⁻¹) - 1) := by
  have he := lowH_Dsym_square_series_cleared_source (K := K) p hp
  rw [lowH_Dsym_square_series_Abar, lowH_Dsym_square_series_squaredCoordinate,
    ← PowerSeries.coe_X, ← lowHConicCanonical_series_square p hp ε hε hu η hη,
    ← pow_mul, lowH_canonical_negative_phase] at he
  simpa only [map_ofNat] using he

/-- The exact quartic cancellation is attached to the actual whole finite Dsym source. -/
theorem lowHConicCanonical_Dsym_delta_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (P : K[X]) :
    let τ : LaurentSeries K := (lowHConicCanonicalT ε hu η : PowerSeries K)
    let w : LaurentSeries K := (PowerSeries.X : PowerSeries K)
    let d : LaurentSeries K := LaurentSeries.derivative K
      (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p)))
    let dτ : LaurentSeries K := PowerSeries.derivative K (lowHConicCanonicalT ε hu η)
    let Pv : LaurentSeries K := Polynomial.aeval (lowHConicCanonicalT ε hu η) P
    τ ^ p * d * ((1 - τ ^ 2) * (4 * τ ^ 2 - 1) * Pv) =
      (τ / w * τ) ^ p * (Pv * w * dτ) - (τ ^ 2) ^ p * (Pv * dτ) := by
  dsimp only
  let τ : LaurentSeries K := (lowHConicCanonicalT ε hu η : PowerSeries K)
  let w : LaurentSeries K := (PowerSeries.X : PowerSeries K)
  let d : LaurentSeries K := LaurentSeries.derivative K
    (lowHFiniteSeriesHom (lowHSquareSource (Dsym (K := K) p)))
  let dτ : LaurentSeries K := PowerSeries.derivative K (lowHConicCanonicalT ε hu η)
  let Pv : LaurentSeries K := Polynomial.aeval (lowHConicCanonicalT ε hu η) P
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5L : (5 : LaurentSeries K) ≠ 0 := by
    change HahnSeries.C (5 : K) ≠ 0
    exact HahnSeries.C_ne_zero h5
  have hw : w ≠ 0 := by
    dsimp only [w]
    rw [PowerSeries.coe_X]
    exact HahnSeries.single_ne_zero one_ne_zero
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
  have hder : 5 * τ * dτ = w := by
    have he := congrArg (HahnSeries.ofPowerSeries ℤ K)
      (lowHConicCanonical_cleared_derivative p hp ε hε hu η hη)
    simpa only [map_mul, map_ofNat] using he
  have he := lowH_conic_Dsym_delta_cancellation ((p - 1) / 2) τ w d dτ Pv
    h5L hw hc ha (lowHConicCanonical_Dsym_cleared_source p hp ε hε hu η hη) hder
  rw [hN, lowH_conic_Dsym_delta_two_sources] at he
  exact he

/-- The original Euler correction, including both proper ends, has zero whole-series residue. -/
theorem lowHConicCanonical_Dsym_EulerDelta_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    ((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ p *
      LaurentSeries.derivative K (lowHFiniteSeriesHom (lowHSquareSource (Dsym p))) *
      ((Polynomial.aeval (lowHConicCanonicalT ε hu η) (lowHEulerDelta p H) : PowerSeries K) :
        LaurentSeries K)).coeff (-1)) = 0 := by
  have hb := lowH_prime_six_band p hp
  obtain ⟨P, hP, hdeg, hodd⟩ := lowHEulerDelta_conic_source p hp (p / 6) hb.1 hb.2 H hH
  have he := lowHConicCanonical_Dsym_delta_source p hp ε hε hu η hη P
  have hval : ((Polynomial.aeval (lowHConicCanonicalT ε hu η) (lowHEulerDelta p H) :
      PowerSeries K) : LaurentSeries K) =
    (1 - ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2) *
      (4 * ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2 - 1) *
      ((Polynomial.aeval (lowHConicCanonicalT ε hu η) P : PowerSeries K) : LaurentSeries K) := by
    rw [hP]
    simp only [lowH_powerSeries_polynomial_field_eval, map_mul, lowHBranchA,
      map_sub, map_one, map_pow, Polynomial.aeval_X, map_ofNat]
  rw [hval, he]
  simpa only [PowerSeries.coe_mul] using
    lowHConicCanonical_delta_two_sources_residue p hp ε hε hu η hη P hdeg hodd

end WPFieldAssembly.ActualBpairContraction
