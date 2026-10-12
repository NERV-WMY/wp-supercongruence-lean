import WPFieldAssembly.SourceClosureSigmaLogCarry

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPFieldAssembly.ActualUW16PrimitiveSource WPFieldAssembly.SourceClosureSigmaKCarry
  WPFieldAssembly.SourceClosureSigmaProductCarry WPFieldAssembly.SourceClosureSigmaWholePrimitive
  WPFieldAssembly.SourceClosureSigmaCanonicalTransport WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureSigmaLogCarry

namespace WPFieldAssembly.SourceClosureSigmaWholeCarry

set_option maxHeartbeats 1500000

/- The complete original divided counterterm. Each summand is integral
only after its actual whole numerator, canonical slots and rational
endpoints have been transported. The literal C and Zp terms cancel over Q. -/

noncomputable def originalWholeVSI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  originalProductEndSymI p hp +
    LaurentPolynomial.C (properCarryDigitI p) * properEndSymI p hp - originalLogEndSymI p hp

/-- Honest rational p-division of the whole original S counterterm and its full comparison. -/
theorem originalWholeVSI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (literalC : ℚ) :
    coefficientMap (integralRationals p).subtype (originalWholeVSI p hp) =
      LaurentPolynomial.C (1 / (p : ℚ)) *
        (originalSactQ p literalC - originalSbarQ p literalC (originalKbarQ p)) := by
  rw [originalWholeVSI, _root_.map_sub, _root_.map_add,
    originalProductEndSymI_value p hp, properCarryEndSymI_value p hp,
    originalLogEndSymI_value p hp, originalSactQ_first_difference p hp]
  have hscalar : (LaurentPolynomial.C (1 / (p : ℚ)) : ℚ[T;T⁻¹]) *
      LaurentPolynomial.C (properCarryQ p) = LaurentPolynomial.C (properCarryQ p / (p : ℚ)) := by
    rw [← _root_.map_mul]
    congr 1
    ring
  simp only [hscalar]
  rfl

/-- UW16l is the residue of the same actual whole quotient, with every p-slot correction retained. -/
theorem originalWholeVSI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (originalWholeVSI p hp) =
      endSym (fourUnitField p hp) (canSlots p
        (originalK1Field p * (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent +
          originalK0Field p *
            (Polynomial.C (-2 * (5 : ZMod p) ^ ((p - 1) / 2) *
              (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) / 15) *
                originalE4CenteredField p).toLaurent)) -
      LaurentPolynomial.C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) *
        properEndSymField p hp -
      endSym (fourUnitField p hp) (nonresonantPrimitiveField p (originalLogProductField p)) := by
  rw [originalWholeVSI, _root_.map_sub, _root_.map_add,
    originalProductEndSymI_field p hp, properCarryEndSymI_field p hp,
    originalLogEndSymI_field p hp]
  ring

end WPFieldAssembly.SourceClosureSigmaWholeCarry
