import WPFieldAssembly.ActualBpairLowHConicGerm
import WPFieldAssembly.ActualBpairLowHCoordinates

open scoped Polynomial LaurentPolynomial PowerSeries LaurentSeries
open Polynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The original r coordinate is a genuine unit in its r=epsilon+z local germ. -/
noncomputable def lowHConicGermParameterUnit (ε : Kˣ) : (PowerSeries K)ˣ where
  val := lowHConicGermR ε
  inv := (lowHConicGermR ε)⁻¹
  val_inv := lowHConicGermR_inverse ε
  inv_val := by rw [mul_comm]; exact lowHConicGermR_inverse ε

theorem lowHConicGerm_original_t (ε : Kˣ) (η : K) :
    LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicT η) =
      lowHConicGermT ε η := by
  simp only [lowHConicT, map_mul, map_add, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one]
  rfl

theorem lowHConicGerm_original_w (ε : Kˣ) :
    LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicW : K[T;T⁻¹]) =
      lowHConicGermW ε := by
  simp only [lowHConicW, map_mul, map_sub, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one]
  rfl

theorem lowHConicGerm_original_dt (ε : Kˣ) (η : K) :
    LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (D (lowHConicT η)) =
      PowerSeries.derivative K (lowHConicGermT ε η) := by
  rw [lowHConicT_derivative, lowHConicGermT_derivative]
  simp only [map_mul, map_sub, map_one, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
  change PowerSeries.C (η / 2) * (1 - ((lowHConicGermParameterUnit ε) ^ (-2 : ℤ)).val) = _
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by rfl, zpow_neg, zpow_natCast, ← inv_pow,
    Units.val_pow_eq_pow_val]
  rfl

theorem lowHConicGerm_original_polynomial (ε : Kˣ) (η : K) (P : K[X]) :
    LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε)
        (Polynomial.eval₂ LaurentPolynomial.C (lowHConicT η) P) =
      Polynomial.aeval (lowHConicGermT ε η) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial n a =>
    simp only [Polynomial.eval₂_monomial, map_mul, map_pow, LaurentPolynomial.eval₂_C,
      lowHConicGerm_original_t, Polynomial.aeval_def, PowerSeries.algebraMap_eq]

/-- The full finite conic numerator is attached to its actual local expansion before residue extraction. -/
theorem lowHConicGerm_original_pullback (ε : Kˣ) (η : K) (P : K[X]) :
    LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε) (lowHConicPullback η P) =
      Polynomial.aeval (lowHConicGermT ε η) P * lowHConicGermW ε *
        PowerSeries.derivative K (lowHConicGermT ε η) := by
  rw [lowHConicPullback, map_mul, map_mul, lowHConicGerm_original_polynomial,
    lowHConicGerm_original_w, lowHConicGerm_original_dt]

/-- Both original conic points and the actual moving reciprocal denominator are retained. -/
theorem lowHConicGerm_original_reciprocal_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0)
    (ε : Kˣ) (η : K) (hη : (5 : K) * η ^ 2 = 1) (B : LaurentSeries K) :
    ((((lowHConicGermT ε η : PowerSeries K) : LaurentSeries K) /
        ((lowHConicGermW ε : PowerSeries K) : LaurentSeries K) * B) ^ p *
      ((LaurentPolynomial.eval₂ PowerSeries.C (lowHConicGermParameterUnit ε)
        (lowHConicPullback η P) : PowerSeries K) : LaurentSeries K)).coeff (-1) = 0 := by
  rw [lowHConicGerm_original_pullback]
  exact lowHConicGerm_reciprocal_residue p hp P hdeg hodd ε η hη B

end WPFieldAssembly.ActualBpairContraction
