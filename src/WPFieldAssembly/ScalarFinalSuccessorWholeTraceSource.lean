import WPFieldAssembly.SourceClosureBalancedOriginalDensity
import WPFieldAssembly.SourceClosureUVFiniteCollection
import WPFieldAssembly.SourceClosurePSquareTrace
import WPFieldAssembly.SourceClosureNormalizedZFinite
import WPFieldAssembly.ScalarFinalSuccessorWholeTraceAlphabet

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
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedOriginalDensity
  WPFieldAssembly.SourceClosureNormalizedZFinite

namespace WPFieldAssembly.SourceClosureWholeTraceCollection

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- This attaches the original actual UV and branch carrier to the entire UW18f alphabet. -/
theorem actual_UV_branch_finite_remainder (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f ((2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp)-
      (66/25 : ZMod p)*(actualMu p hp+actualBalancedBranchB p))=
      ActualKwOrderedEndpoints.originalT5 p u+originalUVFiniteRemainder p u := by
  have h := actualUV_joint_finite_alphabet p hp f u (0 : K) hu
  simp only [mul_zero,sub_zero] at h
  have hc : residueHom p (nativeComparisonBranchCarryIntegral p)=actualBalancedBranchB p := by
    rw [actual_comparison_branch_carry_field p hp]
    unfold actualBalancedBranchB
    ring
  rw [hc] at h
  rw [add_comm (actualMu p hp)]
  unfold originalUVFiniteRemainder
  rw [originalC_descended p hp u hu]
  simpa only [sub_eq_add_neg,add_assoc] using h

/-- The SAME actual whole trace uses the evaluated original Z and retains its original low density. -/
theorem actual_whole_trace_UW18_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f ((2/3 : ZMod p)*(residueHom p (commonSourceTraceIntegral p hp)+
      residueHom p (balancedTraceIntegral p hp)-residueHom p (periodCarryIntegral p hp)))=
      ActualKwOrderedEndpoints.originalT5 p u+originalUVFiniteRemainder p u+
      normalizedZFiniteValue p u+
      (2/3 : K)*f (LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp)) := by
  have hw := congrArg f (actual_whole_trace_original_density p hp)
  rw [weighted_add] at hw
  have hurow := actual_UV_branch_finite_remainder p hp f u hu
  have hzrow := actual_original_normalized_Z_finite p hp f u hu
  simp only [map_add,map_sub,map_mul,map_div₀,map_ofNat] at hw hurow hzrow ⊢
  linear_combination hw+hurow+hzrow

/-- This is the SAME native whole proper density, with the original proper product still attached. -/
theorem actual_native_proper_density_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    ActualSimplePoleResidue.originPole
      (WPActualChiSource.coefficientMap f (wholeTraceProperNativeDensity p hp))=
      ActualKwOrderedEndpoints.originalT5 p u+originalUVFiniteRemainder p u+
      normalizedZFiniteValue p u+
      (2/3 : K)*f (LaurentPoleField.fieldTrace p (p+1) (actualOriginalLowDensity p hp))+
      (2/3 : K)*f (ActualDeltaUNextSource.QO p (properSource p)) := by
  rw [←actual_whole_trace_proper_native_origin_transport p hp f,map_add,
    actual_whole_trace_UW18_collection p hp f u hu]
  simp only [map_mul,map_div₀,map_ofNat]

end WPFieldAssembly.SourceClosureWholeTraceCollection
