import WPLiteralAdapter.PrimitiveNumerator
import WPLiteralAdapter.ResidueAttachment
import WPLiteralAdapter.EscapeDecomposition

open Polynomial WPForcedSourceStokes WPFiniteConductorPolynomial

namespace WPLiteralAdapter

noncomputable section

/-- The complete actual numerator includes the conductor residue and native primitive. -/
noncomputable def actualPrimitiveNumerator (p : ℕ) : ℚ[X] :=
  actualResidueNumerator p+nativePrimitiveNumerator p

theorem actual_total_primitive_numerator (p : ℕ) (hp : 2≤p) :
    actualTotalPrimitive p=
      algebraMap ℚ[X] (RatFunc ℚ) (actualPrimitiveNumerator p)/
        algebraMap ℚ[X] (RatFunc ℚ) (escape^2) := by
  rw [actualTotalPrimitive, actual_conductor_residue_numerator p hp,
    actual_native_primitive_numerator p hp, ← add_div, ← map_add]
  rfl

theorem actual_total_primitive_numerator_X_dvd (p : ℕ) :
    (X : ℚ[X])∣actualPrimitiveNumerator p := by
  apply dvd_add _ (native_primitive_numerator_X_dvd p)
  have hX2 : (X : ℚ[X])∣X^2 := ⟨X, by ring⟩
  exact dvd_trans hX2 (actual_residue_numerator_X_squared p)

theorem actual_total_primitive_numerator_degree (p : ℕ) (hp : 2≤p) :
    (actualPrimitiveNumerator p).natDegree≤3*p+7 := by
  apply (natDegree_add_le _ _).trans
  exact max_le (actual_residue_numerator_degree p)
    (native_primitive_numerator_degree p hp)

theorem actual_total_primitive_constant_zero (p : ℕ) (hp : 2≤p) :
    actualRationalCoefficient (actualTotalPrimitive p) 0=0 := by
  rw [actual_total_primitive_numerator p hp]
  exact escape_square_actual_constant_zero _ (actual_total_primitive_numerator_X_dvd p)

theorem actual_total_primitive_decomposition (p : ℕ) (hp : 2≤p) :
    actualTotalPrimitive p=
      algebraMap ℚ[X] (RatFunc ℚ) (rationalPolynomialPart (actualTotalPrimitive p))+
        actualEscapeTail (escapeSquareTailOne (actualPrimitiveNumerator p))
          (escapeSquareTailTwo (actualPrimitiveNumerator p)) := by
  rw [actual_total_primitive_numerator p hp]
  exact escape_square_fraction_decomposition _

theorem actual_total_primitive_polynomial_degree (p : ℕ) (hp : 2≤p) :
    (rationalPolynomialPart (actualTotalPrimitive p)).natDegree≤3*p+5 := by
  rw [actual_total_primitive_numerator p hp]
  have h := escape_square_polynomialPart_degree _ (3*p+7)
    (actual_total_primitive_numerator_degree p hp)
  simpa only [show 3*p+7-2=3*p+5 by omega] using h

end

end WPLiteralAdapter
