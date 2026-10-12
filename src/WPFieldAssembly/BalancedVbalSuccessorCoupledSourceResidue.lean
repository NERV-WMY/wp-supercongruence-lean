import WPFieldAssembly.BalancedVbalSuccessorCoupledSource
import WPFieldAssembly.SourceClosureTraceReduction
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.BalancedVbalSuccessorCoupledSourceResidue

open BalancedVbalSuccessorCoupledSource SourceClosureSigmaNativeKernel
  SourceClosureBalancedNativeParticular SourceClosureHFNativeTransport
  ActualSimplePoleResidue SourceClosureTraceReduction

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- The literal reflected Sigma trace has the original negative inversion sign.
Both full shifts are cancelled against the same successor denominator. -/
theorem actual_reflected_Sigma_original_trace (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (actualReflectedSigmaWeightedNumerator p hp)=
      originPole (nativeKSigma p*(4*T 1-11)*(actualSigmaPullback p hp).toLaurent) := by
  let F := actualReflectedSigmaWeightedNumerator p hp
  let G := nativeKSigma p*(4*T 1-11)*(actualSigmaPullback p hp).toLaurent
  let A : (ZMod p)[T;T⁻¹] := (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent
  have hs : LaurentPolynomial.C (-2/3 : ZMod p)*T (2*(p : ℤ))*invert F=A^p*G :=
    actual_reflected_sigma_source_attachment p hp
  have hi := congrArg (invert : (ZMod p)[T;T⁻¹] → (ZMod p)[T;T⁻¹]) hs
  dsimp only [A] at hi
  simp only [map_mul,map_pow,invert_C,invert_T,
    WPFiniteZSource.invert_Abar,mul_pow] at hi
  rw [LaurentPolynomial.involutive_invert F] at hi
  change LaurentPolynomial.C (-2/3 : ZMod p)*T (-(2*(p : ℤ)))*F=
    (T (-2)^p*A^p)*invert G at hi
  have ht : (T (2*(p : ℤ))*T (-(2*(p : ℤ))) : (ZMod p)[T;T⁻¹])=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  have hpw : (T (2*(p : ℤ))*T (-2)^p : (ZMod p)[T;T⁻¹])=1 := by
    have hpow : (T (-2) : (ZMod p)[T;T⁻¹])^p=T (-(2*(p : ℤ))) := by
      rw [T_pow]
      congr 1
      ring
    rw [hpow,←T_add,add_neg_cancel,T_zero]
  have hr : LaurentPolynomial.C (-2/3 : ZMod p)*F=A^p*invert G := by
    calc
      _ = T (2*(p : ℤ))*(LaurentPolynomial.C (-2/3 : ZMod p)*
          T (-(2*(p : ℤ)))*F) := by
        rw [show T (2*(p : ℤ))*(LaurentPolynomial.C (-2/3 : ZMod p)*
            T (-(2*(p : ℤ)))*F)=LaurentPolynomial.C (-2/3 : ZMod p)*
              (T (2*(p : ℤ))*T (-(2*(p : ℤ))))*F by ring,ht,mul_one]
      _ = T (2*(p : ℤ))*(T (-2)^p*A^p*invert G) := by
        simpa only [mul_assoc] using
          congrArg (fun H : (ZMod p)[T;T⁻¹] => T (2*(p : ℤ))*H) hi
      _ = (T (2*(p : ℤ))*T (-2)^p)*A^p*invert G := by ring
      _ = _ := by rw [hpw,one_mul]
  have hA : (LaurentPoleField.fieldAbar p).toLaurent=A := by
    dsimp only [A]
    congr 1
    unfold LaurentPoleField.fieldAbar WPFiniteZSource.Abar
    ring
  have hc (c : ZMod p) (H : (ZMod p)[T;T⁻¹]) :
      LaurentPoleField.fieldTrace p (p+1) (LaurentPolynomial.C c*H)=
        c*LaurentPoleField.fieldTrace p (p+1) H := by
    simpa only [LaurentPolynomial.smul_eq_C_mul,smul_eq_mul] using
      (LaurentPoleField.fieldTrace p (p+1)).map_smul c H
  have he : (-2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1) F=
      -originPole G := by
    calc
      _ = LaurentPoleField.fieldTrace p (p+1)
          (LaurentPolynomial.C (-2/3 : ZMod p)*F) := (hc _ _).symm
      _ = LaurentPoleField.fieldTrace p (p+1) (A^p*invert G) :=
        congrArg (LaurentPoleField.fieldTrace p (p+1)) hr
      _ = LaurentPoleField.fieldTrace p 1 (invert G) := by
        rw [←hA,show p+1=1+p by omega]
        exact LaurentPoleField.fieldTrace_cleared_pow p 1 p hp (invert G)
      _ = _ := by rw [fieldTrace_one_native_origin p hp,
        LaurentPolynomial.involutive_invert]
  change (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1) F=originPole G
  linear_combination -he

/-- The original QO consumer retains the full proper source and its zero slot. -/
theorem actual_proper_QO_original_origin (hp : 19≤p) :
    ActualDeltaUNextSource.QO p (SourceClosureCommonWholeSource.properSource p)=
      originPole ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
        SourceClosureCommonWholeSource.properOriginDensity p) := by
  rw [SourceClosureCommonWholeSource.actual_proper_origin_source,
    originPole_cleared p hp]

/-- This identifies the three existing carriers. Identification of the literal
original j-series with the full product is a separate source attachment. -/
theorem actual_Jjoint_origin_three_carriers (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (actualReflectedSigmaWeightedNumerator p hp)+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p
        (SourceClosureCommonWholeSource.properSource p)-
      originPole (actualJSubtractionCleared p)=originPole (actualJjoint p hp) := by
  rw [actual_reflected_Sigma_original_trace p hp,actual_proper_QO_original_origin p hp,
    actualJjoint,originPole_sub,originPole_add]
  rw [show LaurentPolynomial.C (2/3 : ZMod p)*
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
        SourceClosureCommonWholeSource.properOriginDensity p=
      LaurentPolynomial.C (2/3 : ZMod p)*
        ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
          SourceClosureCommonWholeSource.properOriginDensity p) by ring,
    originPole_C_mul]

end WPFieldAssembly.BalancedVbalSuccessorCoupledSourceResidue
