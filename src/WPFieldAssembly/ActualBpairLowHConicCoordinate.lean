import WPFieldAssembly.ActualBpairLowHConicGermAttachment
import Mathlib.RingTheory.PowerSeries.Substitution

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- Both genuine conic points have the same unit first coefficient in w. -/
theorem lowHConicGermW_first_unit (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (hε : ε = 1 ∨ ε = -1) : IsUnit ((lowHConicGermW ε).coeff 1) := by
  have he := (lowHConicGerm_two_parameters (K := K) p hp) ε hε
  have hh := he.2
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at hh
  have h1 : (lowHConicGermW ε).coeff 1 = 1 := by
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add, mul_one] using hh
  rw [h1]
  exact isUnit_one

/-- This is Mathlib's actual whole formal inverse, rather than a truncated coordinate. -/
noncomputable def lowHConicWCoordinate (ε : Kˣ) (hu : IsUnit ((lowHConicGermW ε).coeff 1)) : PowerSeries K :=
  (lowHConicGermW ε).substInvOfIsUnit hu

theorem lowHConicWCoordinate_zero (ε : Kˣ) (hu : IsUnit ((lowHConicGermW ε).coeff 1)) :
    PowerSeries.constantCoeff (lowHConicWCoordinate ε hu) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

theorem lowHConicWCoordinate_hasSubst (ε : Kˣ) (hu : IsUnit ((lowHConicGermW ε).coeff 1)) :
    PowerSeries.HasSubst (lowHConicWCoordinate ε hu) :=
  PowerSeries.HasSubst.substInvOfIsUnit _ _

theorem lowHConicWCoordinate_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (hε : ε = 1 ∨ ε = -1) (hu : IsUnit ((lowHConicGermW ε).coeff 1)) :
    PowerSeries.subst (lowHConicWCoordinate ε hu) (lowHConicGermW ε) = PowerSeries.X := by
  exact PowerSeries.subst_substInvOfIsUnit_right _
    ((lowHConicGerm_two_parameters (K := K) p hp) ε hε).1 hu

noncomputable def lowHConicCanonicalT (ε : Kˣ) (hu : IsUnit ((lowHConicGermW ε).coeff 1)) (η : K) :
    PowerSeries K := PowerSeries.subst (lowHConicWCoordinate ε hu) (lowHConicGermT ε η)

/-- The original conic relation is transported to w itself as the exact local coordinate. -/
theorem lowHConicCanonical_relation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (hε : ε = 1 ∨ ε = -1) (hu : IsUnit ((lowHConicGermW ε).coeff 1))
    (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : PowerSeries K) * lowHConicCanonicalT ε hu η ^ 2 = PowerSeries.X ^ 2 + 1 := by
  let φ := PowerSeries.substAlgHom (R := K) (lowHConicWCoordinate_hasSubst ε hu)
  have he := congrArg φ (lowHConicGerm_relation p hp ε η hη)
  simpa only [map_mul, map_pow, map_add, map_one, map_ofNat, φ, PowerSeries.coe_substAlgHom,
    lowHConicCanonicalT, lowHConicWCoordinate_source p hp ε hε hu] using he

/-- The full original finite differential is composed and multiplied by the actual inverse Jacobian. -/
theorem lowHConicCanonical_original_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (hε : ε = 1 ∨ ε = -1) (hu : IsUnit ((lowHConicGermW ε).coeff 1))
    (η : K) (hη : (5 : K) * η ^ 2 = 1) (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    PowerSeries.subst (lowHConicWCoordinate ε hu)
        (LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicPullback η P)) *
      PowerSeries.derivative K (lowHConicWCoordinate ε hu) =
        Polynomial.aeval (PowerSeries.X : PowerSeries K) (lowHConicLocalP P) := by
  let g := lowHConicWCoordinate ε hu
  have hg := lowHConicWCoordinate_hasSubst ε hu
  let φ := PowerSeries.substAlgHom (R := K) hg
  have hφ (a : PowerSeries K) : φ a = PowerSeries.subst g a :=
    congr_fun (PowerSeries.coe_substAlgHom hg) a
  have hW := lowHConicWCoordinate_source p hp ε hε hu
  have hDW : φ (PowerSeries.derivative K (lowHConicGermW ε)) * PowerSeries.derivative K g = 1 := by
    have he := congrArg (PowerSeries.derivative K) hW
    rw [PowerSeries.derivative_subst hg, PowerSeries.derivative_X] at he
    simpa only [hφ, g] using he
  have he := congrArg φ (lowHConicGerm_local_source p hp ε η hη P hodd)
  simp only [map_mul] at he
  rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply] at he
  change Polynomial.aeval (φ (lowHConicGermT ε η)) P * φ (lowHConicGermW ε) *
      φ (PowerSeries.derivative K (lowHConicGermT ε η)) =
    Polynomial.aeval (φ (lowHConicGermW ε)) (lowHConicLocalP P) *
      φ (PowerSeries.derivative K (lowHConicGermW ε)) at he
  have hφW : φ (lowHConicGermW ε) = PowerSeries.X := by
    simpa only [hφ, g] using hW
  rw [hφW] at he
  rw [lowHConicGerm_original_pullback]
  change PowerSeries.subst g (Polynomial.aeval (lowHConicGermT ε η) P * lowHConicGermW ε *
      PowerSeries.derivative K (lowHConicGermT ε η)) * PowerSeries.derivative K g = _
  rw [← hφ]
  rw [map_mul, map_mul, ← Polynomial.aeval_algHom_apply, hφW, he]
  rw [mul_assoc, hDW, mul_one]

/-- The moving reciprocal denominator remains in the complete infinite Laurent series. -/
theorem lowHConicCanonical_reciprocal_residue (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (ε : Kˣ) (hε : ε = 1 ∨ ε = -1) (hu : IsUnit ((lowHConicGermW ε).coeff 1))
    (η : K) (hη : (5 : K) * η ^ 2 = 1) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (B : LaurentSeries K) :
    ((((lowHConicCanonicalT ε hu η : PowerSeries K) : LaurentSeries K) /
        ((PowerSeries.X : PowerSeries K) : LaurentSeries K) * B) ^ p *
      ((PowerSeries.subst (lowHConicWCoordinate ε hu)
          (LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicPullback η P)) *
        PowerSeries.derivative K (lowHConicWCoordinate ε hu) : PowerSeries K) : LaurentSeries K)).coeff (-1) = 0 := by
  rw [lowHConicCanonical_original_source p hp ε hε hu η hη P hodd]
  have hS : (lowHConicLocalP P).natDegree < p - 1 := by
    have he := lowHConicLocalP_degree P hodd
    omega
  have hcoe : Polynomial.aeval (PowerSeries.X : PowerSeries K) (lowHConicLocalP P) =
      (lowHConicLocalP P : PowerSeries K) := by
    simpa only [Polynomial.aeval_def, PowerSeries.algebraMap_eq] using
      (Polynomial.eval₂_C_X_eq_coe (φ := lowHConicLocalP P))
  rw [hcoe]
  exact lowH_series_full_frobenius_residue p hp _ hS _

end WPFieldAssembly.ActualBpairContraction
