import WPFieldAssembly.BalancedVbalSuccessorCoupledSource
import WPFieldAssembly.BalancedVbalSuccessorNRPrimitive
import WPFieldAssembly.BalancedVbalSuccessorCrossAttachment
import WPFieldAssembly.BalancedVbalSuccessorCrossReciprocal
import WPFieldAssembly.BalancedVbalSuccessorCrossDetector

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualGaussBottom
  WPFieldAssembly.ActualLowEuler WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureVbalSigmaProduct
  WPFieldAssembly.BalancedVbalSuccessorHasse
  WPFieldAssembly.BalancedVbalSuccessorCoupledSource
  WPFieldAssembly.BalancedVbalSuccessorNRPrimitive
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.BalancedVbalSuccessorCrossAttachment
  WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
  WPFieldAssembly.BalancedVbalSuccessorCrossReciprocal
  WPFieldAssembly.BalancedVbalSuccessorCrossDetector
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.BalancedVbalSuccessorCoupledEvaluation

set_option maxHeartbeats 2000000

variable (p : ℕ) [Fact p.Prime]

private theorem actual_native_norm_nonzero (hp : 19≤p) :
    ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).toLaurent≠0 := by
  intro hz
  have hzP : (actualF p).comp (WPHasseIntegralTransport.fieldV p)=0 :=
    Polynomial.toLaurent_injective (by simpa only [map_zero] using hz)
  have he := (actual_Hasse_native_unit_ends p hp).2
  rw [hzP,eval_zero] at he
  exact zero_ne_one he

/-- Both actual cleared products remove f without division at any Hasse zero. -/
theorem actual_Jjoint_NR_cross (hp : 19≤p) :
    actualJjoint p hp=
      -LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
        ((actualNRNativeCarrier p hp).toLaurent-
          (4*T (p : ℤ)-11)*actualCrossCarrier p) := by
  let f := ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).toLaurent
  have hS := congrArg Polynomial.toLaurent (actual_CB_Sigma_product p hp)
  simp only [map_mul] at hS
  change (ActualFirstGreen.CB p).toLaurent*(actualSigmaPullback p hp).toLaurent=
    f*(actualNRNativeCarrier p hp).toLaurent at hS
  have hC := actual_CB_cross_product p hp
  change (ActualFirstGreen.CB p).toLaurent*actualBv p=f*actualCrossCarrier p at hC
  have hJ := actual_Jjoint_cleared_source p hp
  rw [←ActualBpairContraction.actual_f_pullback_field_eq p hp] at hJ
  apply mul_left_cancel₀ (actual_native_norm_nonzero p hp)
  change f*actualJjoint p hp=f*_
  calc
    _ = -LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
        ((ActualFirstGreen.CB p).toLaurent*(actualSigmaPullback p hp).toLaurent-
          (4*T (p : ℤ)-11)*((ActualFirstGreen.CB p).toLaurent*actualBv p)) := by
      simpa only [mul_assoc] using hJ
    _ = -LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
        (f*(actualNRNativeCarrier p hp).toLaurent-
          (4*T (p : ℤ)-11)*(f*actualCrossCarrier p)) := by rw [hS,hC]
    _ = _ := by ring

private theorem negative_frobenius_phase_derivative :
    D (4*T (-(p : ℤ))-11 : (ZMod p)[T;T⁻¹])=0 := by
  have hp0 : ((p : ℤ) : ZMod p)=0 := by
    simpa only [Int.cast_natCast] using ZMod.natCast_self p
  have ht : D (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])=0 := by
    have h := D_monomial (1 : ZMod p) (-(p : ℤ))
    simpa only [map_one,one_mul,Int.cast_neg,hp0,neg_zero,mul_zero,map_zero,zero_mul]
      using h
  change D (LaurentPolynomial.C (4 : ZMod p)*T (-(p : ℤ))-
    LaurentPolynomial.C (11 : ZMod p))=0
  rw [map_sub,D_C_mul,ht,D_C,mul_zero,sub_zero]

/-- The SAME original coupled carrier has the full primitive plus inverse four-phase numerator. -/
theorem actual_Jjoint_primitive_decomposition (hp : 19≤p) :
    actualJjoint p hp=
      LaurentPolynomial.C (2/9 : ZMod p)*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
        D ((4*T (-(p : ℤ))-11)*(actualEprim p hp).toLaurent)+
      LaurentPolynomial.C (2/9 : ZMod p)*invert (actualNcross p) := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h9 : (9 : ZMod p)≠0 := by
    rw [show (9 : ZMod p)=3^2 by ring]
    exact pow_ne_zero _ h3
  have hs : (2/9 : ZMod p)*3=2/3 := by field_simp [h3,h9]; ring
  have hsl := congrArg (LaurentPolynomial.C : ZMod p→+*(ZMod p)[T;T⁻¹]) hs
  simp only [map_mul,map_ofNat] at hsl
  have hE := congrArg Polynomial.toLaurent (actual_Eprim_cleared_source p hp)
  simp only [map_mul,map_neg,map_sub,map_ofNat,toLaurent_X,←D_toLaurent] at hE
  rw [actual_Jjoint_NR_cross p hp,D_mul,negative_frobenius_phase_derivative p,
    zero_mul,zero_add,actual_Ncross_inverse_source p hp]
  simp only [map_sub,map_mul,map_ofNat,toLaurent_X]
  linear_combination
    -(LaurentPolynomial.C (2/9 : ZMod p)*(4*T (-(p : ℤ))-11))*hE+
      (4*T 1-11)*(4*T (-(p : ℤ))-11)*
        ((actualNRNativeCarrier p hp).toLaurent-
          (4*T (p : ℤ)-11)*actualCrossCarrier p)*hsl

/-- The first term vanishes in the original origin operator; all four cross phases remain. -/
theorem actual_Jjoint_origin_detector (hp : 19≤p) :
    originPole (actualJjoint p hp)=(194/375 : ZMod p)*fieldHarmonic p (p/6)^2 := by
  have hz : originPole ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
      D ((4*T (-(p : ℤ))-11)*(actualEprim p hp).toLaurent))=0 := by
    rw [originPole_cleared p hp,D_coeff]
    norm_num
  have he : actualJjoint p hp=
      LaurentPolynomial.C (2/9 : ZMod p)*
        ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
          D ((4*T (-(p : ℤ))-11)*(actualEprim p hp).toLaurent))+
      LaurentPolynomial.C (2/9 : ZMod p)*invert (actualNcross p) := by
    rw [actual_Jjoint_primitive_decomposition p hp]
    ring
  rw [he,originPole_add,originPole_C_mul,originPole_C_mul,hz,mul_zero,zero_add]
  exact actual_Ncross_origin_inverse_normalized p hp

/-- The original arithmetic h is identified before the scalar consumer receives the detector. -/
theorem actual_Jjoint_origin_finite_h (hp : 19≤p) :
    originPole (actualJjoint p hp)=(194/375 : ZMod p)*(WPFiniteNC122.h p)^2 := by
  rw [actual_Jjoint_origin_detector p hp,
    ActualBpairContraction.actual_harmonic_is_finite_h p hp]

end WPFieldAssembly.BalancedVbalSuccessorCoupledEvaluation
