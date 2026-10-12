import WPFieldAssembly.SourceClosureUVThirdBand
import WPFieldAssembly.SourceClosureUVSupport
import WPFieldAssembly.SourceClosureUVWeightedLog
import WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
import WPFieldAssembly.SourceClosureVbalFrobeniusNormalization

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.SourceClosureUVSupport
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVThirdBand
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
  WPFieldAssembly.SourceClosureVbalFrobeniusNormalization

namespace WPFieldAssembly.SourceClosurePSquareTrace

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- These are the two parts of the SAME original beta, not independent input scalars. -/
noncomputable def actualOriginalBetaP : ZMod p :=
  (-LaurentPolynomial.C (1/2 : ZMod p)*(descendedP p)^2).coeff (2*(p : ℤ))

noncomputable def actualOriginalBetaJ : ZMod p :=
  (WPFiniteJCarrier.GJ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ))

theorem actual_original_beta_split :
    actualOriginalBeta p=actualOriginalBetaP p+actualOriginalBetaJ p := by
  unfold actualOriginalBeta originalDescendedZ actualOriginalBetaP actualOriginalBetaJ
  simp only [neg_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]

/-- The original P-square boundary uses the actual finite primitive at both ends. -/
theorem actual_original_betaP_finite {K : Type*} [Field K] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f (actualOriginalBetaP p)=
      -(WPFiniteABSourceTail.uSlot p u)^2/2+
      4/(15*WPFiniteABSourceTail.epsilon p)*
        (WPFiniteProductTail.originPrimitive p (WPFiniteWSource.W p) (1/4)-
          WPFiniteProductTail.originPrimitive p (WPFiniteWSource.W p) 4) := by
  have h := congrArg f (actual_original_beta_split p)
  rw [map_add,actual_original_beta_both_roots p f hp u hu,
    actual_finite_frobenius_boundary p hp u] at h
  have ht := congrArg (fun J : K[T;T⁻¹] => J.coeff (2*(p : ℤ)))
    (original_GJ_transport f p)
  simp only [WPActualChiSource.coefficientMap_coeff] at ht
  have hj : f (actualOriginalBetaJ p)=
      -4*(WPFiniteJSource.HJP p : K[X]).coeff p/45 := by
    rw [actualOriginalBetaJ,ht]
    exact WPFiniteJCarrier.actual_GJ_2p_coefficient p hp
  rw [hj] at h
  linear_combination -h

/-- The actual P square reaches the third window; the shorter combined-Z bound is not used. -/
theorem actual_Psquare_three_windows (hp : 19≤p) :
    originalWeightedFieldTrace p ((descendedP p)^2)=
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 ((descendedP p)^2)-
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*(descendedP p)^2)-
      (129/8 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-2*(p : ℤ))*(descendedP p)^2) := by
  have hP := descendedP_bounds (K:=ZMod p) p hp
  have hs := Above_mul hP.1 hP.1
  have hSquare : Above ((descendedP p : (ZMod p)[T;T⁻¹])^2) (3*(p : ℤ)-1) := by
    simpa only [pow_two] using Above_mono (b:=3*(p : ℤ)-1) hs (by omega)
  exact original_weight_above_third_band p hp _ hSquare

theorem actual_normalized_Psquare_three_windows (hp : 19≤p) :
    -(1/3 : ZMod p)*originalWeightedFieldTrace p ((descendedP p)^2)-
      (207/4 : ZMod p)*actualOriginalBetaP p=
      endpointTrace (1/4 : ZMod p) 4 ((descendedP p)^2)+
      (3/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*(descendedP p)^2)+
      (43/8 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-2*(p : ℤ))*(descendedP p)^2)-
      (207/4 : ZMod p)*actualOriginalBetaP p := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  rw [actual_Psquare_three_windows p hp]
  field_simp [h2,h3,h4,h8]
  ring

/-- The disjoint P and J evaluations feed the original normalized Z consumer exactly. -/
theorem actual_normalized_Z_split (hp : 19≤p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p (originalDescendedZ p)-
      (207/4 : ZMod p)*actualOriginalBeta p=
      (-(1/3 : ZMod p)*originalWeightedFieldTrace p ((descendedP p)^2)-
        (207/4 : ZMod p)*actualOriginalBetaP p)+
      ((2/3 : ZMod p)*originalWeightedFieldTrace p (WPFiniteJCarrier.GJ p)-
        (207/4 : ZMod p)*actualOriginalBetaJ p) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  rw [actual_original_beta_split,originalDescendedZ]
  rw [show -(LaurentPolynomial.C (1/2 : ZMod p))*(descendedP p)^2=
    LaurentPolynomial.C (-1/2 : ZMod p)*(descendedP p)^2 by
      simp only [neg_div,map_neg],weighted_add,weighted_C_mul]
  field_simp [h2,h3,h4]
  ring

end WPFieldAssembly.SourceClosurePSquareTrace
