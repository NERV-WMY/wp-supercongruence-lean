import WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
import WPFieldAssembly.BalancedVbalSuccessorHasse

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteWSource
  WPFieldAssembly.BalancedVbalSuccessorHasse
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
  WPFieldAssembly.SourceClosureVbalCrossTruncation

namespace WPFieldAssembly.BalancedVbalSuccessorCrossReciprocal

set_option maxHeartbeats 2400000

variable (p : ℕ) [Fact p.Prime]

private theorem shift_unit (a : ℤ) :
    (T a : (ZMod p)[T;T⁻¹])*T (-a)=1 := by rw [←T_add]; simp only [add_neg_cancel,T_zero]

private theorem invert_S :
    invert (nativeS p).toLaurent=T (-1)*(nativeS p).toLaurent := by
  simp only [nativeS,map_mul,map_add,toLaurent_C,toLaurent_X,map_one,invert_C,invert_T]
  have ht := shift_unit p (-1)
  simp only [neg_neg] at ht
  linear_combination -LaurentPolynomial.C (1/5 : ZMod p)*ht

private theorem invert_B :
    invert (4*X-11 : (ZMod p)[X]).toLaurent=
      T (-1)*(4-11*X : (ZMod p)[X]).toLaurent := by
  simp only [map_mul,map_sub,map_ofNat,toLaurent_X,invert_T]
  have ht := shift_unit p (-1)
  simp only [neg_neg] at ht
  linear_combination (11 : (ZMod p)[T;T⁻¹])*ht

private theorem invert_C :
    invert (4-11*X : (ZMod p)[X]).toLaurent=
      T (-1)*(4*X-11 : (ZMod p)[X]).toLaurent := by
  simp only [map_mul,map_sub,map_ofNat,toLaurent_X,invert_T]
  have ht := shift_unit p (-1)
  simp only [neg_neg] at ht
  linear_combination (-4 : (ZMod p)[T;T⁻¹])*ht

/-- The whole actual proper product has the exact cleared reciprocal before any residue. -/
theorem actual_cross_Dx_reciprocal (hp : 19≤p) :
    (4-11*X : (ZMod p)[X]).toLaurent*invert (actualCrossDx p)=
      T (((p-1)/2 : ℕ) : ℤ)*(4*X-11 : (ZMod p)[X]).toLaurent*actualCrossDx p := by
  let N := (p-1)/2
  let rn := (p/6+1)%2
  let e := actualCrossE p
  let s := (nativeS p).toLaurent
  let B := (4*X-11 : (ZMod p)[X]).toLaurent
  let Cx := (4-11*X : (ZMod p)[X]).toLaurent
  let bc := (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X))).toLaurent
  let n := (actualCrossN0 p).toLaurent
  have he : 2*e=N+1+3*rn := by
    dsimp only [e,actualCrossE,N,rn]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5 <;> omega
  have hs : invert s=T (-1)*s := invert_S p
  have hB : invert B=T (-1)*Cx := invert_B p
  have hC : invert Cx=T (-1)*B := invert_C p
  have hbc : invert bc=T (-2)*bc := by
    dsimp only [bc]
    simp only [map_mul,toLaurent_C,LaurentPolynomial.invert_C]
    rw [invert_B p,invert_C p]
    have ht : (T (-1) : (ZMod p)[T;T⁻¹])*T (-1)=T (-2) := by rw [←T_add]; norm_num
    linear_combination
      LaurentPolynomial.C (1/25 : ZMod p)*B*Cx*ht
  have hn : invert (n*invert n)=n*invert n := by
    rw [map_mul,LaurentPolynomial.involutive_invert]
    ring
  have hD : actualCrossDx p=
      LaurentPolynomial.C (6*SourceClosureVbalIR61FourEnds.actualCrossHasseSign p)*
        T (-(e : ℤ))*Cx*s^rn*bc^rn*(n*invert n) := by
    dsimp only [actualCrossDx,actualCrossPositiveNumerator,Cx,s,bc,n,nativeS,rn,e]
    simp only [map_mul,map_pow]
    ring
  have ht : (T (e : ℤ) : (ZMod p)[T;T⁻¹])*T (-1)*T (-1)^rn*T (-2)^rn=
      T (N : ℤ)*T (-(e : ℤ)) := by
    simp only [T_pow,←T_add]
    congr 1
    omega
  rw [hD]
  simp only [map_mul,map_pow,LaurentPolynomial.invert_C,invert_T,neg_neg,hC,hs,hbc,hn,mul_pow]
  calc
    _ = LaurentPolynomial.C (6*SourceClosureVbalIR61FourEnds.actualCrossHasseSign p)*
        (T (e : ℤ)*T (-1)*T (-1)^rn*T (-2)^rn)*
          B*Cx*s^rn*bc^rn*(n*invert n) := by
      dsimp only [B,Cx]
      simp only [map_mul,map_sub,map_ofNat,toLaurent_X]
      ring
    _ = _ := by
      rw [ht]
      dsimp only [N,B,Cx]
      simp only [map_mul,map_sub,map_ofNat,toLaurent_X]
      ring

theorem actual_native_S_frobenius :
    (nativeS p).toLaurent^p=LaurentPolynomial.C (1/5 : ZMod p)*(T (p : ℤ)+1) := by
  have h5 : (5 : ZMod p)^p=5 := ZMod.pow_card 5
  have hi : (1/5 : ZMod p)^p=1/5 := by rw [div_pow,one_pow,h5]
  have hpoly : (nativeS p)^p=Polynomial.C (1/5 : ZMod p)*(X^p+1) := by
    rw [nativeS,mul_pow,←map_pow,hi,add_pow_char (p:=p),one_pow]
  have h := congrArg Polynomial.toLaurent hpoly
  simpa only [map_pow,map_mul,map_add,toLaurent_C,toLaurent_X,map_one,T_pow,mul_one]
    using h

private theorem inverse_phase_shift (hp : 19≤p) :
    invert (crossFourPhase (K:=ZMod p) p ((p-1)/2))*T (((p-1)/2 : ℕ) : ℤ)=
      LaurentPolynomial.C (1/250 : ZMod p)*
        (-44*T (-(p : ℤ))+93+93*T (p : ℤ)-44*T (2*(p : ℤ))) := by
  let N := (p-1)/2
  have hN : 2*N+1=p := by
    dsimp only [N]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5 <;> omega
  have h1 : (T (-((p : ℤ)+(N : ℤ))) : (ZMod p)[T;T⁻¹])*T (N : ℤ)=T (-(p : ℤ)) := by
    rw [←T_add]; congr 1; ring
  have h2 : (T (-(N : ℤ)) : (ZMod p)[T;T⁻¹])*T (N : ℤ)=1 := by rw [←T_add]; simp
  have h3 : (T ((N : ℤ)+1) : (ZMod p)[T;T⁻¹])*T (N : ℤ)=T (p : ℤ) := by
    rw [←T_add]; congr 1; omega
  have h4 : (T ((p : ℤ)+(N : ℤ)+1) : (ZMod p)[T;T⁻¹])*T (N : ℤ)=T (2*(p : ℤ)) := by
    rw [←T_add]; congr 1; omega
  simp only [crossFourPhase,map_mul,map_add,map_sub,map_neg,LaurentPolynomial.invert_C,
    invert_T,map_ofNat]
  change _=LaurentPolynomial.C (1/250 : ZMod p)*_
  calc
    _ = LaurentPolynomial.C (1/250 : ZMod p)*
        (-44*(T (-((p : ℤ)+(N : ℤ)))*T (N : ℤ))+
          93*(T (-(N : ℤ))*T (N : ℤ))+
          93*(T ((N : ℤ)+1)*T (N : ℤ))-
          44*(T ((p : ℤ)+(N : ℤ)+1)*T (N : ℤ))) := by
      dsimp only [N]
      ring
    _ = _ := by rw [h1,h2,h3,h4]; ring

/-- The original four-phase numerator has the exact no-extra-x-squared differential inversion. -/
theorem actual_Ncross_inverse_source (hp : 19≤p) :
    invert (actualNcross p)=
      3*(4*X-11 : (ZMod p)[X]).toLaurent*
        (4*T (-(p : ℤ))-11)*(4*T (p : ℤ)-11)*actualCrossCarrier p := by
  let B := (4*X-11 : (ZMod p)[X]).toLaurent
  let Cx := (4-11*X : (ZMod p)[X]).toLaurent
  let phi : (ZMod p)[T;T⁻¹] := 4*T (-(p : ℤ))-11
  let alpha : (ZMod p)[T;T⁻¹] := 4*T (p : ℤ)-11
  let F : (ZMod p)[T;T⁻¹] := -44*T (-(p : ℤ))+93+93*T (p : ℤ)-44*T (2*(p : ℤ))
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h50 : (50 : ZMod p)≠0 := by rw [show (50 : ZMod p)=2*5^2 by ring]; exact mul_ne_zero h2 (pow_ne_zero _ h5)
  have h150 : (150 : ZMod p)≠0 := by
    have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
    rw [show (150 : ZMod p)=3*50 by ring]
    exact mul_ne_zero h3 h50
  have h250 : (250 : ZMod p)≠0 := by rw [show (250 : ZMod p)=2*5^3 by ring]; exact mul_ne_zero h2 (pow_ne_zero _ h5)
  have hCx : Cx≠0 := by
    intro hz
    have hzP : (4-11*X : (ZMod p)[X])=0 :=
      Polynomial.toLaurent_injective (by simpa only [map_zero] using hz)
    have hc := congrArg (fun Q : (ZMod p)[X] => Q.eval 0) hzP
    have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
    exact h4 (by simpa only [eval_sub,eval_ofNat,eval_mul,eval_X,mul_zero,sub_zero,eval_zero] using hc)
  have hleft : Cx*invert (actualNcross p)=
      LaurentPolynomial.C (1/250 : ZMod p)*F*B*actualCrossDx p := by
    rw [actualNcross,map_mul]
    calc
      _ = invert (crossFourPhase (K:=ZMod p) p ((p-1)/2))*
          (Cx*invert (actualCrossDx p)) := by ring
      _ = (invert (crossFourPhase (K:=ZMod p) p ((p-1)/2))*T (((p-1)/2 : ℕ) : ℤ))*
          B*actualCrossDx p := by rw [actual_cross_Dx_reciprocal p hp]; ring
      _ = _ := by rw [inverse_phase_shift p hp]
  have hphase : phi*alpha*(T (p : ℤ)+1)=F := by
    have ht := shift_unit p (p : ℤ)
    have ht2 : (T (p : ℤ) : (ZMod p)[T;T⁻¹])^2=T (2*(p : ℤ)) := by rw [T_pow]; congr 1
    dsimp only [phi,alpha,F]
    linear_combination (16*T (p : ℤ)-28)*ht-44*ht2
  have hs : (1/50 : ZMod p)*(1/5)=1/250 := by field_simp [h5,h50,h250]; ring
  have h3s : (1/50 : ZMod p)*150=3 := by field_simp [h50]; ring
  have hc := congrArg (fun G : (ZMod p)[T;T⁻¹] =>
      LaurentPolynomial.C (1/50 : ZMod p)*B*phi*alpha*G) (actual_cross_Dx_cleared p hp)
  have hS : (Polynomial.C (1/5 : ZMod p)*(X+1)).toLaurent^p=
      LaurentPolynomial.C (1/5 : ZMod p)*(T (p : ℤ)+1) := by
    simpa only [nativeS] using actual_native_S_frobenius p
  rw [hS] at hc
  change LaurentPolynomial.C (1/50 : ZMod p)*B*phi*alpha*
      (actualCrossDx p*(LaurentPolynomial.C (1/5 : ZMod p)*(T (p : ℤ)+1)))=
    LaurentPolynomial.C (1/50 : ZMod p)*B*phi*alpha*
      (LaurentPolynomial.C (150 : ZMod p)*Cx*actualCrossCarrier p) at hc
  simp only [map_ofNat] at hc
  have hright : Cx*(3*B*phi*alpha*actualCrossCarrier p)=
      LaurentPolynomial.C (1/250 : ZMod p)*F*B*actualCrossDx p := by
    have hsl := congrArg (LaurentPolynomial.C : ZMod p→+*(ZMod p)[T;T⁻¹]) hs
    have h3l := congrArg (LaurentPolynomial.C : ZMod p→+*(ZMod p)[T;T⁻¹]) h3s
    simp only [map_mul,map_ofNat] at hsl h3l
    linear_combination -hc+
      B*phi*alpha*actualCrossDx p*(T (p : ℤ)+1)*hsl+
      -(B*phi*alpha*Cx*actualCrossCarrier p)*h3l+
      LaurentPolynomial.C (1/250 : ZMod p)*B*actualCrossDx p*hphase
  exact mul_left_cancel₀ hCx (hleft.trans hright.symm)

end WPFieldAssembly.BalancedVbalSuccessorCrossReciprocal
