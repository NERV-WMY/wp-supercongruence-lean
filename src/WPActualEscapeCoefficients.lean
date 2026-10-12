import WPRationalTranslation
import WPActualEtaUnits

open scoped LaurentSeries BigOperators

namespace WPForcedSourceStokes

noncomputable section

set_option maxHeartbeats 1000000

/-- The actual Laurent series at the original escape point x=50/99. -/
def actualEscapeRationalSeries (f : RatFunc ℚ) : LaurentSeries ℚ :=
  actualRationalSeries (rationalTranslationHom escapePoint f)

def actualEscapeRationalCoefficient (f : RatFunc ℚ) (n : ℤ) : ℚ :=
  (actualEscapeRationalSeries f).coeff n

def integralRationalEscape (R : Subring ℚ) : Subring (RatFunc ℚ) :=
  (integralRationalOrigin R).comap (rationalTranslationHom escapePoint)

theorem integral_rational_escape_iff (R : Subring ℚ) (f : RatFunc ℚ) :
    f∈integralRationalEscape R ↔ ∀ n, actualEscapeRationalCoefficient f n∈R := Iff.rfl

theorem integral_rational_escape_scalar (R : Subring ℚ) (q : ℚ) (hq : q∈R) :
    RatFunc.C q∈integralRationalEscape R := by
  change rationalTranslationHom escapePoint (RatFunc.C q)∈integralRationalOrigin R
  rw [rational_translation_scalar]
  exact integral_rational_origin_scalar R q hq

theorem actual_escape_coefficient_sum {ι : Type*} (s : Finset ι)
    (f : ι → RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (∑ i∈s,f i) n =
      ∑ i∈s,actualEscapeRationalCoefficient (f i) n := by
  simp only [actualEscapeRationalCoefficient, actualEscapeRationalSeries,
    actualRationalSeries, map_sum, HahnSeries.coeff_sum]

theorem actual_escape_coefficient_scalar (q : ℚ) (f : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (RatFunc.C q*f) n =
      q*actualEscapeRationalCoefficient f n := by
  change actualRationalCoefficient (rationalTranslationHom escapePoint (RatFunc.C q*f)) n = _
  rw [map_mul, rational_translation_scalar, actual_rational_coefficient_scalar]
  rfl

theorem actual_escape_derivative_coefficient (f : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient (rationalDerivative f) n =
      (n+1 : ℤ)*actualEscapeRationalCoefficient f (n+1) := by
  change actualRationalCoefficient (rationalTranslationHom escapePoint (rationalDerivative f)) n = _
  rw [rational_translation_derivative, actual_rational_derivative_coefficient]
  rfl

/-- Translation keeps the complete coefficient of the scalar connection, including its shift. -/
theorem actual_escape_beta_coefficient (f : RatFunc ℚ) (n : ℤ) :
    actualEscapeRationalCoefficient ((1-symbol)*rationalDerivative f-f/2) n =
      (1-escapePoint)*(n+1 : ℤ)*actualEscapeRationalCoefficient f (n+1)-
        ((n : ℚ)+1/2)*actualEscapeRationalCoefficient f n := by
  let T := rationalTranslationHom escapePoint f
  have he : rationalTranslationHom escapePoint ((1-symbol)*rationalDerivative f-f/2) =
      ((1-symbol)*rationalDerivative T-T/2)-RatFunc.C escapePoint*rationalDerivative T := by
    simp only [map_sub, map_mul, map_div₀, map_one, _root_.map_ofNat,
      rational_translation_symbol, rational_translation_derivative, T]
    ring
  change actualRationalCoefficient (rationalTranslationHom escapePoint
    ((1-symbol)*rationalDerivative f-f/2)) n = _
  rw [he, actual_rational_coefficient_sub, actual_beta_coefficient,
    actual_rational_coefficient_scalar, actual_rational_derivative_coefficient]
  change _ = (1-escapePoint)*(n+1 : ℤ)*actualRationalCoefficient T (n+1)-
    ((n : ℚ)+1/2)*actualRationalCoefficient T n
  ring

end

end WPForcedSourceStokes
