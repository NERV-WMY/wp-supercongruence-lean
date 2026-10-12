import WPFieldAssembly.BalancedVbalSuccessorCrossSupport
import WPFieldAssembly.SourceClosureVbalCrossTruncation

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.SourceClosureVbalCrossTruncation

namespace WPFieldAssembly.BalancedVbalSuccessorCrossTruncation

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The positive polynomial is projected from the entire original cross carrier. -/
noncomputable def actualCrossShift : (ZMod p)[X] :=
  trunc (T (((p-1)/2 : ℕ) : ℤ)*actualCrossDx p)

/-- All four original signed phases are present before support projection. -/
noncomputable def actualNcross : (ZMod p)[T;T⁻¹] :=
  crossFourPhase (K:=ZMod p) p ((p-1)/2)*actualCrossDx p

theorem actual_cross_shift_realization (hp : 19≤p) :
    (actualCrossShift p).toLaurent=T (((p-1)/2 : ℕ) : ℤ)*actualCrossDx p := by
  have hN : 2*((p-1)/2)+1=p := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5 <;> omega
  exact shifted_carrier_is_trunc _ _ _ (actual_cross_Dx_support p hp).2 (by omega)

/-- The two surviving phases follow from the SAME actual support theorem. -/
theorem actual_cross_four_phase_projection (hp : 19≤p) :
    trunc (actualNcross p)=
      Polynomial.C (1/250 : ZMod p)*(93-44*X^p)*actualCrossShift p := by
  have hN : 2*((p-1)/2)+1=p := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5 <;> omega
  have hD : Above (actualCrossDx p) (-1) :=
    Above_mono (actual_cross_Dx_support p hp).1 (by omega)
  exact cross_four_phase_trunc p ((p-1)/2) (actualCrossDx p) _ hD
    (actual_cross_Dx_support p hp).2 (by omega)

end WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
