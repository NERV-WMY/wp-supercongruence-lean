import WPFieldAssembly.ActualBpairLowHConicCoordinate
import WPFieldAssembly.ActualBpairLowHDeltaAlgebra
import WPFieldAssembly.ActualBpairLowHEuler

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The cleared original conic Jacobian is transported to both genuine w coordinates. -/
theorem lowHConicCanonical_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : PowerSeries K) * lowHConicCanonicalT ε hu η *
      PowerSeries.derivative K (lowHConicCanonicalT ε hu η) = PowerSeries.X := by
  let g := lowHConicWCoordinate ε hu
  have hg := lowHConicWCoordinate_hasSubst ε hu
  let φ := PowerSeries.substAlgHom (R := K) hg
  have hφ (a : PowerSeries K) : φ a = PowerSeries.subst g a :=
    congr_fun (PowerSeries.coe_substAlgHom hg) a
  have hτ : lowHConicCanonicalT ε hu η = φ (lowHConicGermT ε η) := by
    rw [hφ]
    rfl
  have hW : φ (lowHConicGermW ε) = PowerSeries.X := by
    simpa only [hφ, g] using lowHConicWCoordinate_source p hp ε hε hu
  have hDW : φ (PowerSeries.derivative K (lowHConicGermW ε)) * PowerSeries.derivative K g = 1 := by
    have he := congrArg (PowerSeries.derivative K) (lowHConicWCoordinate_source p hp ε hε hu)
    rw [PowerSeries.derivative_subst hg, PowerSeries.derivative_X] at he
    simpa only [hφ, g] using he
  have hDT : PowerSeries.derivative K (lowHConicCanonicalT ε hu η) =
      φ (PowerSeries.derivative K (lowHConicGermT ε η)) * PowerSeries.derivative K g := by
    simpa only [hφ, g, lowHConicCanonicalT] using
      (PowerSeries.derivative_subst (f := lowHConicGermT ε η) hg)
  calc
    _ = φ (5 * lowHConicGermT ε η * PowerSeries.derivative K (lowHConicGermT ε η)) *
        PowerSeries.derivative K g := by
      rw [map_mul, map_mul, map_ofNat, hDT, hτ]
      ring
    _ = φ (lowHConicGermW ε * PowerSeries.derivative K (lowHConicGermW ε)) *
        PowerSeries.derivative K g := by rw [lowHConicGerm_cleared_derivative p hp ε η hη]
    _ = PowerSeries.X * (φ (PowerSeries.derivative K (lowHConicGermW ε)) *
        PowerSeries.derivative K g) := by rw [map_mul, hW]; ring
    _ = PowerSeries.X := by rw [hDW, mul_one]

/-- The actual inverse Jacobian gives P(tau)*w*d tau in the whole w coordinate. -/
theorem lowHConicCanonical_direct_pullback (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (P : K[X]) :
    PowerSeries.subst (lowHConicWCoordinate ε hu)
        (LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicPullback η P)) *
      PowerSeries.derivative K (lowHConicWCoordinate ε hu) =
        Polynomial.aeval (lowHConicCanonicalT ε hu η) P * PowerSeries.X *
          PowerSeries.derivative K (lowHConicCanonicalT ε hu η) := by
  let g := lowHConicWCoordinate ε hu
  have hg := lowHConicWCoordinate_hasSubst ε hu
  let φ := PowerSeries.substAlgHom (R := K) hg
  have hφ (a : PowerSeries K) : φ a = PowerSeries.subst g a :=
    congr_fun (PowerSeries.coe_substAlgHom hg) a
  have hτ : lowHConicCanonicalT ε hu η = φ (lowHConicGermT ε η) := by
    rw [hφ]
    rfl
  rw [lowHConicGerm_original_pullback]
  change PowerSeries.subst g (Polynomial.aeval (lowHConicGermT ε η) P * lowHConicGermW ε *
      PowerSeries.derivative K (lowHConicGermT ε η)) * PowerSeries.derivative K g = _
  rw [← hφ]
  rw [map_mul, map_mul, ← Polynomial.aeval_algHom_apply]
  have hW : φ (lowHConicGermW ε) = PowerSeries.X := by
    simpa only [hφ, g] using lowHConicWCoordinate_source p hp ε hε hu
  rw [hW]
  have hder : PowerSeries.derivative K (lowHConicCanonicalT ε hu η) =
      φ (PowerSeries.derivative K (lowHConicGermT ε η)) * PowerSeries.derivative K g := by
    simpa only [hφ, g, lowHConicCanonicalT] using
      (PowerSeries.derivative_subst (f := lowHConicGermT ε η) hg)
  rw [hder, hτ]
  ring

/-- Every regular polynomial source has its genuine composed power-series primitive. -/
theorem lowHConicCanonical_regular_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hu : IsUnit ((lowHConicGermW ε).coeff 1))
    (η : K) (P : K[X]) (hdeg : P.natDegree ≤ p - 8) :
    ∃ J : PowerSeries K, PowerSeries.derivative K J =
      Polynomial.aeval (lowHConicCanonicalT ε hu η) P *
        PowerSeries.derivative K (lowHConicCanonicalT ε hu η) := by
  let I : K[X] := lowHIntegralP p P
  have hi : I.derivative = P := lowHIntegralP_derivative p hp P (by omega)
  refine ⟨Polynomial.aeval (lowHConicCanonicalT ε hu η) I, ?_⟩
  have he := Derivation.comp_aeval_eq (a := lowHConicCanonicalT ε hu η) (PowerSeries.derivative K) I
  simpa only [hi, smul_eq_mul] using he

/-- Both complete Frobenius terms created by the actual quartic cancellation have zero residue. -/
theorem lowHConicCanonical_delta_two_sources_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (ε : Kˣ) (hε : ε = 1 ∨ ε = -1)
    (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) (hη : (5 : K) * η ^ 2 = 1)
    (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    (((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) /
          ((PowerSeries.X : PowerSeries K) : LaurentSeries K) *
          ((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K)) ^ p *
        ((Polynomial.aeval (lowHConicCanonicalT ε hu η) P * PowerSeries.X *
          PowerSeries.derivative K (lowHConicCanonicalT ε hu η) : PowerSeries K) : LaurentSeries K)) -
      (((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2) ^ p *
        ((Polynomial.aeval (lowHConicCanonicalT ε hu η) P *
          PowerSeries.derivative K (lowHConicCanonicalT ε hu η) : PowerSeries K) : LaurentSeries K)).coeff (-1) = 0 := by
  have hfirst := lowHConicCanonical_reciprocal_residue p hp ε hε hu η hη P hdeg hodd
    (((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K))
  rw [lowHConicCanonical_direct_pullback p hp ε hε hu η P] at hfirst
  obtain ⟨J, hJ⟩ := lowHConicCanonical_regular_primitive p hp ε hu η P hdeg
  have hsecond := lowH_regular_exact_series_residue p
    ((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) ^ 2)) J
  rw [hJ] at hsecond
  rw [HahnSeries.coeff_sub, hfirst, hsecond, sub_self]

end WPFieldAssembly.ActualBpairContraction
