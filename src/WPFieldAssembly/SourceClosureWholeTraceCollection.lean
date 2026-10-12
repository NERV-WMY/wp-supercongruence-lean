import WPFieldAssembly.ScalarFinalSuccessorWholeTraceSource
import WPFieldAssembly.ActualVbalFieldClosure

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualIntegralGreenTrace
  WPFieldAssembly.ActualCommonTraceReduction WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureCommonWholeSource
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVFiniteCollection
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
  WPFieldAssembly.SourceClosureBalancedNativeNormalization
  WPFieldAssembly.SourceClosureBalancedOriginalDensity
  WPFieldAssembly.SourceClosureNormalizedZFinite

namespace WPFieldAssembly.SourceClosureWholeTraceCollection

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The actual rational Vbal/p cancels T5 in the same common+balanced-period consumer. -/
theorem actual_Vbal_whole_trace_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=1/5) (hw : w^2=3/11) :
    (ZMod.castHom (dvd_refl p) K)
      ((2/3 : ZMod p)*(residueHom p (vBalancedDividedIntegral p hp)+
        residueHom p (commonSourceTraceIntegral p hp)+residueHom p (balancedTraceIntegral p hp)-
        residueHom p (periodCarryIntegral p hp)))=
      ActualVbalFieldClosure.vbalMomentConsumer p u w+originalUVFiniteRemainder p u+
      normalizedZFiniteValue p u+
      (2/3 : K)*(ZMod.castHom (dvd_refl p) K)
        (LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp)) := by
  let f : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have ht := actual_whole_trace_UW18_collection p hp f u hu
  have hv := ActualVbalFieldClosure.actual_vBalanced_T5_consumer p hp u w hu hw
  simp only [map_mul,map_add,map_sub,map_div₀,map_ofNat] at ht ⊢
  dsimp only [f] at ht
  linear_combination ht+hv

end WPFieldAssembly.SourceClosureWholeTraceCollection
