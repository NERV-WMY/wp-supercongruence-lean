import WPFieldAssembly.ActualFirstGreen
import WPFieldAssembly.ActualNormCrossAttachment
import WPFieldAssembly.SourceClosureVbalParity

open scoped Polynomial
open Polynomial WPFiniteWSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPActualRankTwoLegendreField WPActualRankTwoProper WPActualGaussBottom
  WPActualNativeJacobiJet WPFieldAssembly.SourceClosureVbalParity
  WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.BalancedVbalSuccessorCBParity

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/- STATEMENT_FIDELITY: the full original CB is factored through the
   actual Y and proper n parity polynomials. The conic pullback is the
   original CBt, with its full X^p. The consecutive parity remainders
   sum to one; neither branch nor a nonzero endpoint is divided out.
   Every prime p >= 19 in both classes is retained. -/

noncomputable def actualCBParityY0 : (ZMod p)[X] :=
  (parityPolynomial p (p/6) (actualLegendreJacobi p)).comp
    (1-WPHasseIntegralTransport.fieldV p)

noncomputable def actualCBParityN0 : (ZMod p)[X] :=
  (parityPolynomial p (p/6+1) (properLegendreJacobi p)).comp
    (1-WPHasseIntegralTransport.fieldV p)

omit [Fact p.Prime] in
theorem actual_CB_parity_remainders : (p/6)%2+(p/6+1)%2=1 := by omega

/-- The SAME original polynomial CB has the entire parity factor. -/
theorem actual_CB_full_parity_factor (hp : 19≤p) :
    ActualFirstGreen.CB p=
      C (1/25 : ZMod p)*
        (squaredCoordinate : (ZMod p)[X])^((p-1)/2+1)*
        (4*X-11)*actualCBParityY0 p*actualCBParityN0 p := by
  let ZY := parityPolynomial p (p/6) (actualLegendreJacobi p)
  let Zn := parityPolynomial p (p/6+1) (properLegendreJacobi p)
  have hY : actualLegendreJacobi p=X^((p/6)%2)*ZY.comp (X^2) :=
    (actual_Y_parity p hp).1
  have hn : properLegendreJacobi p=X^((p/6+1)%2)*Zn.comp (X^2) :=
    (actual_n_parity p hp).1
  have hB : ActualFirstGreen.B p=X*(ZY.comp (X^2)*Zn.comp (X^2)) := by
    calc
      _ = (X^((p/6)%2)*ZY.comp (X^2))*
          (X^((p/6+1)%2)*Zn.comp (X^2)) := by
        rw [ActualFirstGreen.B,hY,hn]
      _ = X^((p/6)%2+(p/6+1)%2)*(ZY.comp (X^2)*Zn.comp (X^2)) := by
        rw [pow_add]
        ring
      _ = _ := by rw [actual_CB_parity_remainders,pow_one]
  have hBc : (ActualFirstGreen.B p).comp Tc=
      Tc*(ZY.comp (Tc^2)*Zn.comp (Tc^2)) := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.comp Tc) hB
    simpa only [mul_comp,X_comp,comp_assoc,pow_comp] using h
  have hY0 : (actualCBParityY0 p).comp conic=ZY.comp (Tc^2) := by
    simp only [actualCBParityY0,comp_assoc,sub_comp,one_comp,
      actual_native_V_conic p hp,sub_sub_cancel]
    rfl
  have hn0 : (actualCBParityN0 p).comp conic=Zn.comp (Tc^2) := by
    simp only [actualCBParityN0,comp_assoc,sub_comp,one_comp,
      actual_native_V_conic p hp,sub_sub_cancel]
    rfl
  have hb : (4*X-11 : (ZMod p)[X]).comp conic=5*(4*X^2-3) := by
    simp only [mul_comp,ofNat_comp,X_comp,sub_comp,conic,Nat.cast_ofNat]
    ring
  have ht : (Tc : (ZMod p)[X])=X*(4*X^2-3) := by
    simp only [Tc]
    ring
  have hN : 2*((p-1)/2+1)=p+1 := by
    have hhalf := half_exponent p hp
    omega
  have hXp : ((X : (ZMod p)[X])^2)^((p-1)/2+1)=X^(p+1) := by
    rw [←pow_mul,hN]
  have hXsucc : (X : (ZMod p)[X])^(p+1)=X^p*X := pow_succ X p
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have hu : (C (1/25 : ZMod p)*5 : (ZMod p)[X])=C (1/5 : ZMod p) := by
    change C (1/25 : ZMod p)*C (5 : ZMod p)=C (1/5 : ZMod p)
    rw [←map_mul]
    congr 1
    field_simp [h5,h25]
    ring
  have hconic : (conic : (ZMod p)[X]).natDegree≠0 := by
    have hd : (conic : (ZMod p)[X]).natDegree=2 := by
      unfold conic
      compute_degree
      exact h5
    rw [hd]
    norm_num
  apply comp_injective_nonconstant (conic : (ZMod p)[X]) hconic
  dsimp only
  rw [(ActualFirstGreen.actual_carrier_pullbacks p hp).1]
  simp only [mul_comp,C_comp,pow_comp,squaredCoordinate_conic p hp,hY0,hn0,hb,hXp]
  rw [ActualFirstGreen.CBt,hBc,hXsucc]
  calc
    _ = C (1/5 : ZMod p)*X^p*X*(4*X^2-3)*ZY.comp (Tc^2)*Zn.comp (Tc^2) := by
      rw [ht]
      ring
    _ = _ := by
      linear_combination -X^p*X*(4*X^2-3)*ZY.comp (Tc^2)*Zn.comp (Tc^2)*hu

/-- The actual parity factors keep both original endpoint normalizations. -/
theorem actual_CB_parity_factor_ends (hp : 19≤p) :
    (actualCBParityY0 p).eval (1/4)=1 ∧
      (actualCBParityY0 p).eval 4=1 ∧
      (actualCBParityN0 p).eval (1/4)= -fieldHarmonic p (p/6) ∧
      (actualCBParityN0 p).eval 4= -fieldHarmonic p (p/6) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc1 : (conic : (ZMod p)[X]).eval 1=4 := by norm_num [conic]
  have ht1 : (Tc : (ZMod p)[X]).eval 1=1 := by norm_num [Tc]
  have hchalf : (conic : (ZMod p)[X]).eval (1/2)=1/4 := by
    simp only [conic,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    field_simp [h2,h4]
    ring
  have hthalf : (Tc : (ZMod p)[X]).eval (1/2)= -1 := by
    simp only [Tc,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X]
    field_simp [h2]
    ring
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1/4)=0 := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval (1/2))
      (actual_native_V_conic p hp)
    simpa only [eval_comp,eval_sub,eval_one,eval_pow,hchalf,hthalf,neg_sq,
      one_pow,sub_self] using h
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4=0 := by
    have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1)
      (actual_native_V_conic p hp)
    simpa only [eval_comp,eval_sub,eval_one,eval_pow,hc1,ht1,one_pow,sub_self] using h
  have hY1 := (actual_Y_parity p hp).2
  have hn1 := (actual_n_parity p hp).2
  simp only [actualCBParityY0,actualCBParityN0,eval_comp,eval_sub,eval_one,
    hVa,hVb,sub_zero,hY1,hn1,and_self]

end WPFieldAssembly.BalancedVbalSuccessorCBParity
