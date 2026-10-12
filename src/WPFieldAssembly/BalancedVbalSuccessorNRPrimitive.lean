import WPFieldAssembly.SourceClosureVbalIR61ExactPart
import WPFieldAssembly.SourceClosureVbalConicExact
import WPFieldAssembly.SourceClosureVbalSigmaProduct

open scoped Polynomial
open Polynomial WPFiniteWSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPFieldAssembly.NativeIR28 WPFieldAssembly.SourceClosureVbalIR61ExactPart

namespace WPFieldAssembly.BalancedVbalSuccessorNRPrimitive

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/- STATEMENT_FIDELITY: Eprim uses the SAME exact zero-origin primitive
   of the actual n*Re source. Its full t^p/5 carrier is contracted only
   after actual evenness is proved. Both prime classes are retained.
   The final equation has no caller primitive, derivative or source
   hypothesis; its n*Re carrier is the original SigmaProduct carrier. -/

noncomputable def actualEprimCubicCarrier (hp : 19≤p) : (ZMod p)[X] :=
  C (1/5 : ZMod p)*X^p*(actualNRPrimitive p hp).comp Tc

noncomputable def actualEprim (hp : 19≤p) : (ZMod p)[X] :=
  (contract 2 (actualEprimCubicCarrier p hp)).comp squaredCoordinate

/-- The whole t^p primitive carrier is even before its exact contraction. -/
theorem actual_Eprim_cubic_even (hp : 19≤p) :
    (actualEprimCubicCarrier p hp).comp (-X)=actualEprimCubicCarrier p hp := by
  have ht : (Tc : (ZMod p)[X]).comp (-X)=(-X).comp Tc := by
    simp [Tc,mul_comp,sub_comp,pow_comp]; ring
  have ho := (actual_NR_primitive_source_degree_odd p hp).2.2.2
  simp only [actualEprimCubicCarrier,mul_comp,C_comp,pow_comp,X_comp,comp_assoc]
  rw [ht,←comp_assoc,ho,neg_comp,
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)).neg_pow]
  ring

/-- The specified Eprim pulls back to its full original cubic carrier. -/
theorem actual_Eprim_native_conic (hp : 19≤p) :
    (actualEprim p hp).comp conic=actualEprimCubicCarrier p hp := by
  rw [actualEprim,comp_assoc,squaredCoordinate_conic p hp]
  have h := even_expand_contract_two p hp _ (actual_Eprim_cubic_even p hp)
  rw [expand_eq_comp_X_pow] at h
  exact h

/-- The actual whole Eprim has the cleared original n*Re differential. -/
theorem actual_Eprim_cleared_source (hp : 19≤p) :
    (WPFiniteZSource.Abar : (ZMod p)[X])*(actualEprim p hp).derivative=
      -3*(4*X-11)*SourceClosureVbalSigmaProduct.actualNRNativeCarrier p hp := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hJ : (actualEprim p hp).comp (5*X^2-1)=
      C (1/5 : ZMod p)*X^p*(actualNRPrimitive p hp).comp (4*X^3-3*X) := by
    simpa only [actualEprimCubicCarrier,conic,Tc] using actual_Eprim_native_conic p hp
  have hNR : (SourceClosureVbalSigmaProduct.actualNRNativeCarrier p hp).comp (5*X^2-1)=
      C (1/5 : ZMod p)*X^p*(actualNRPolynomial p hp).comp (4*X^3-3*X) := by
    simpa only [SourceClosureVbalSigmaProduct.actualNRCubicCarrier,actualNRPolynomial,
      conic,Tc] using SourceClosureVbalSigmaProduct.actual_NR_native_conic p hp
  change ((4-X)*(4*X-1))*(actualEprim p hp).derivative=
    -3*(4*X-11)*SourceClosureVbalSigmaProduct.actualNRNativeCarrier p hp
  exact SourceClosureVbalConicExact.conic_exact_primitive_cleared p (by simp) h2 h5
    (actualNRPrimitive p hp) (actualNRPolynomial p hp)
    (actualEprim p hp) (SourceClosureVbalSigmaProduct.actualNRNativeCarrier p hp)
    hJ hNR (actual_NR_primitive_source_degree_odd p hp).1

/-- The original conic origin has the actual carrier's zero value. -/
theorem actual_Eprim_native_origin (hp : 19≤p) : (actualEprim p hp).eval (-1)=0 := by
  have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) (actual_Eprim_native_conic p hp)
  simpa only [eval_comp,conic,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,
    zero_pow (by omega : p≠0),zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,
    zero_mul,eval_one,zero_sub,actualEprimCubicCarrier,eval_C] using h

end WPFieldAssembly.BalancedVbalSuccessorNRPrimitive
