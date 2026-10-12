import WPFieldAssembly.ActualComparisonKwAttachment
import WPFieldAssembly.ActualKwFiniteHBridge

open scoped LaurentPolynomial
open LaurentPolynomial WPPIntegralReduction WPActualChiSource
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualComparisonKwAttachment
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.ActualKwPhaseTrace
  WPFieldAssembly.ActualKwFiniteHBridge

namespace WPFieldAssembly.ActualComparisonF1Attachment

set_option maxHeartbeats 1200000

/-- The actual F1 trace uses only the full original D_N and L_N values. -/
noncomputable def actualTwField (p : ℕ) [Fact p.Prime] : ZMod p :=
  -2*movingMinus p (1/4 : ZMod p) 4 (1/4)+movingMinus p (1/4 : ZMod p) 4 4-
    (4/5 : ZMod p)*
      ((1/4 : ZMod p)*movingRplus p (1/4 : ZMod p)+
        (4 : ZMod p)*movingRplus p (4 : ZMod p)-
          (11/4 : ZMod p)*movingRplus p (11/4 : ZMod p))

theorem comparisonKwCarryI_full_F1 (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (comparisonKwCarryI p hp)=(-3 : ZMod p)*fieldDlogQ p
      (literalF1Laurent p*(comparisonField p : (ZMod p)[T;T⁻¹])) := by
  rw [comparisonKwCarryI,←comparisonIntegral_field p hp]
  apply actualFiniteCarry_field_full_source p (p+(p-1)/2) hp (by omega)
    (comparisonIntegral p) (comparisonField p : (ZMod p)[T;T⁻¹]).coeff.support
    (comparisonField p : (ZMod p)[T;T⁻¹]).coeff
  · rw [comparisonIntegral_field p hp]
    exact laurent_full_signed_expansion _
  · exact comparisonField_support_upper p hp

/-- This attaches the finite triangular theorem to the whole original comparison carry. -/
theorem comparisonKwCarryI_Tw (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (comparisonKwCarryI p hp)=actualTwField p := by
  rw [comparisonKwCarryI_full_F1 p hp,fieldDlogQ_endpoint p hp]
  have h := literalF1_movingEven_Tw p hp 0
  simpa only [comparisonField,movingEvenField,WPFiniteZSource.phase,
    map_zero,add_zero,actualTwField] using h

end WPFieldAssembly.ActualComparisonF1Attachment
