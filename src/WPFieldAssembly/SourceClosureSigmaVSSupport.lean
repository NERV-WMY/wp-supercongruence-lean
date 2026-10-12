import WPFieldAssembly.SourceClosureSigmaWholeSupport
import WPFieldAssembly.SourceClosureSigmaActualVS

open scoped LaurentPolynomial
open LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPFieldAssembly.SourceClosureSigmaWholeCarry
  WPFieldAssembly.SourceClosureSigmaWholeSupport
  WPFieldAssembly.SourceClosureSigmaActualVS

namespace WPFieldAssembly.SourceClosureSigmaVSSupport

/- The field carrier is the residue of the original whole integral quotient.
No support premise is supplied to the actual VS statement. -/

theorem actualVSField_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (j : ℤ)
    (hj : j < -((3 * ((p - 1) / 2) + 1 : ℕ) : ℤ) ∨
      ((3 * ((p - 1) / 2) + 1 : ℕ) : ℤ) < j) :
    (actualVSField p hp).coeff j = 0 := by
  have hexp := WPFiniteWSource.half_exponent p hp
  have hbound : (p : ℤ) + ((p - 1) / 2 : ℕ) =
      ((3 * ((p - 1) / 2) + 1 : ℕ) : ℤ) := by omega
  rw [actualVSField, coefficientMap_coeff, originalWholeVSI_support p hp j
    (by simpa only [hbound] using hj), _root_.map_zero]

/-- Both original p holes survive the genuine whole integral division. -/
theorem actualVSField_pivots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualVSField p hp).coeff (p : ℤ) = 0 ∧
      (actualVSField p hp).coeff (-(p : ℤ)) = 0 := by
  obtain ⟨hpivot, hmirror⟩ := originalWholeVSI_pivots p hp
  constructor
  · rw [actualVSField, coefficientMap_coeff, hpivot, _root_.map_zero]
  · rw [actualVSField, coefficientMap_coeff, hmirror, _root_.map_zero]

/-- Whole rational division fixes all nonzero Frobenius slots, rather than
identifying the actual carrier from its derivative. -/
theorem actualVSField_nonzero_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (p : ℤ) ∣ j) (hj0 : j ≠ 0) :
    (actualVSField p hp).coeff j = 0 := by
  rw [actualVSField, coefficientMap_coeff,
    originalWholeVSI_nonzero_frobenius p hp j hj hj0, _root_.map_zero]

/-- The full support bound also fixes both doubled-p coefficients. -/
theorem actualVSField_double_pivots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualVSField p hp).coeff (2 * (p : ℤ)) = 0 ∧
      (actualVSField p hp).coeff (-2 * (p : ℤ)) = 0 := by
  constructor
  · exact actualVSField_nonzero_frobenius p hp _ ⟨2, by ring⟩ (by omega)
  · exact actualVSField_nonzero_frobenius p hp _ ⟨-2, by ring⟩ (by omega)

/-- The entire bound fixes the squared-p slots that field differentiation cannot see. -/
theorem actualVSField_square_pivots (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualVSField p hp).coeff ((p : ℤ) ^ 2) = 0 ∧
      (actualVSField p hp).coeff (-((p : ℤ) ^ 2)) = 0 := by
  have hpz : (p : ℤ) ≠ 0 := by omega
  have hsq0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hpz
  constructor
  · exact actualVSField_nonzero_frobenius p hp _ ⟨(p : ℤ), by ring⟩ hsq0
  · exact actualVSField_nonzero_frobenius p hp _ ⟨-(p : ℤ), by ring⟩
      (neg_ne_zero.mpr hsq0)

end WPFieldAssembly.SourceClosureSigmaVSSupport
