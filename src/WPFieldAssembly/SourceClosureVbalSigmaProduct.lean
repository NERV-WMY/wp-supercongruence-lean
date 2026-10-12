import WPFieldAssembly.ActualNormCrossAttachment
import WPFieldAssembly.ActualFirstGreen

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualRankTwoResidueSource WPActualNativeJacobiJet WPFiniteWSource
  WPFiniteJHighCoefficient WPFiniteCubicLog WPFieldAssembly.NativeIR28
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.SourceClosureVbalSigmaProduct

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The literal odd n times Re source, with its original cubic carrier. -/
noncomputable def actualNRCubicCarrier (hp : 19≤p) : (ZMod p)[X] :=
  C (1/5 : ZMod p)*X^p*
    (properLegendreJacobi p*actualRankDividedField p (by omega)).comp Tc

/-- Its full even contraction in the original x coordinate. -/
noncomputable def actualNRNativeCarrier (hp : 19≤p) : (ZMod p)[X] :=
  (contract 2 (actualNRCubicCarrier p hp)).comp squaredCoordinate

private theorem actual_NR_odd (hp : 19≤p) :
    (properLegendreJacobi p*actualRankDividedField p (by omega)).comp (-X)=
      -(properLegendreJacobi p*actualRankDividedField p (by omega)) := by
  have hs : (C ((-1 : ZMod p)^(p/6)) : (ZMod p)[X])^2=1 := by
    rw [←C_pow,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  rw [mul_comp,actual_proper_legendre_reflect p hp,actual_rank_divided_reflect p hp]
  linear_combination -(properLegendreJacobi p*actualRankDividedField p (by omega))*hs

private theorem actual_NR_carrier_even (hp : 19≤p) :
    (actualNRCubicCarrier p hp).comp (-X)=actualNRCubicCarrier p hp := by
  have ht : (Tc : (ZMod p)[X]).comp (-X)=(-X).comp Tc := by
    simp [Tc,mul_comp,sub_comp,pow_comp]
    ring
  have ho := actual_NR_odd p hp
  dsimp only [actualNRCubicCarrier]
  generalize hNR : properLegendreJacobi p*actualRankDividedField p (by omega)=NR at ho ⊢
  simp only [mul_comp,C_comp,pow_comp,X_comp]
  rw [comp_assoc,ht,←comp_assoc,ho,neg_comp,
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)).neg_pow]
  ring

theorem actual_NR_native_conic (hp : 19≤p) :
    (actualNRNativeCarrier p hp).comp conic=actualNRCubicCarrier p hp := by
  rw [actualNRNativeCarrier,comp_assoc,squaredCoordinate_conic p hp]
  have h := even_expand_contract_two p hp _ (actual_NR_carrier_even p hp)
  rw [expand_eq_comp_X_pow] at h
  exact h

private theorem actual_Sigma_native_conic (hp : 19≤p) :
    ((actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p)).comp conic=
      (actualLegendreJacobi p*actualRankDividedField p (by omega)).comp Tc := by
  rw [comp_assoc,actual_native_V_conic p hp]
  have he : (actualSigmaNative p hp).comp (1-X^2)=
      actualLegendreJacobi p*actualRankDividedField p (by omega) :=
    even_native_attachment p hp _ (actual_YR_even p hp)
  calc
    _ = ((actualSigmaNative p hp).comp (1-X^2)).comp Tc := by
      rw [comp_assoc]
      congr 1
      simp only [sub_comp,one_comp,pow_comp,X_comp]
    _ = _ := by rw [he]

private theorem actual_f_native_conic (hp : 19≤p) :
    ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).comp conic=
      (actualLegendreJacobi p).comp Tc^2 := by
  rw [comp_assoc,actual_native_V_conic p hp]
  have he : (actualF p).comp (1-X^2)=actualLegendreJacobi p^2 :=
    even_native_attachment p hp _ (actual_Y_square_even p hp)
  calc
    _ = ((actualF p).comp (1-X^2)).comp Tc := by
      rw [comp_assoc]
      congr 1
      simp only [sub_comp,one_comp,pow_comp,X_comp]
    _ = _ := by rw [he,pow_comp]

/-- The same actual CB and native Sigma have their cleared proper product at every root. -/
theorem actual_CB_Sigma_product (hp : 19≤p) :
    ActualFirstGreen.CB p*((actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p))=
      ((actualF p).comp (WPHasseIntegralTransport.fieldV p))*actualNRNativeCarrier p hp := by
  have hconic : (conic : (ZMod p)[X]).natDegree≠0 := by
    have hd : (conic : (ZMod p)[X]).natDegree=2 := by
      unfold conic
      change (C (5 : ZMod p)*X^2-1).natDegree=2
      compute_degree
      exact WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
    rw [hd]
    norm_num
  apply comp_injective_nonconstant (conic : (ZMod p)[X]) hconic
  dsimp only
  rw [mul_comp,mul_comp,(ActualFirstGreen.actual_carrier_pullbacks p hp).1,
    actual_Sigma_native_conic p hp,actual_f_native_conic p hp,actual_NR_native_conic p hp]
  simp only [ActualFirstGreen.CBt,ActualFirstGreen.B,actualNRCubicCarrier,mul_comp]
  ring

end WPFieldAssembly.SourceClosureVbalSigmaProduct
