import WPFieldAssembly.BalancedVbalSuccessorHasse
import WPFieldAssembly.BalancedVbalSuccessorCBParity
import WPFieldAssembly.BalancedVbalSuccessorCrossSupport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.BalancedVbalSuccessorHasse
  WPFieldAssembly.BalancedVbalSuccessorCBParity
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.SourceClosureVbalHasseSign

namespace WPFieldAssembly.BalancedVbalSuccessorCrossAttachment

set_option maxHeartbeats 2400000

variable (p : ℕ) [Fact p.Prime]

private theorem shift_product (a : ℤ) :
    (T a : (ZMod p)[T;T⁻¹])*T (-a)=1 := by
  rw [←T_add]
  simp only [add_neg_cancel,T_zero]

private theorem scalar_reciprocal_cross (eta : ZMod p) (heta : eta^2=1)
    (M : ℤ) (r : ℕ) (hr : r=0 ∨ r=1)
    (b c y : (ZMod p)[T;T⁻¹])
    (hrec : b^r*y=LaurentPolynomial.C eta*T (M-(r : ℤ))*c^r*invert y) :
    b*c*y*invert y=
      LaurentPolynomial.C eta*T ((r : ℤ)-M)*b^(r+1)*c^(1-r)*y^2 := by
  have hs : (LaurentPolynomial.C eta : (ZMod p)[T;T⁻¹])^2=1 := by
    rw [←map_pow,heta,map_one]
  have ht : (T ((r : ℤ)-M) : (ZMod p)[T;T⁻¹])*T (M-(r : ℤ))=1 := by
    rw [←T_add]
    norm_num
  have hsolve : c^r*invert y=
      LaurentPolynomial.C eta*T ((r : ℤ)-M)*b^r*y := by
    calc
      _ = LaurentPolynomial.C eta*T ((r : ℤ)-M)*
          (LaurentPolynomial.C eta*T (M-(r : ℤ))*c^r*invert y) := by
        linear_combination
          -(T ((r : ℤ)-M)*T (M-(r : ℤ))*c^r*invert y)*hs-(c^r*invert y)*ht
      _ = _ := by rw [←hrec]; ring
  rcases hr with hr | hr
  · subst r
    simp only [pow_zero,one_mul,Nat.zero_add,Nat.sub_zero,pow_one,
      Int.natCast_zero,zero_sub] at hsolve ⊢
    rw [hsolve]
    ring
  · subst r
    simp only [pow_one,Nat.reduceAdd,Nat.sub_self,pow_zero,mul_one,
      Int.natCast_one] at hsolve ⊢
    linear_combination b*y*hsolve

private theorem native_S_invert :
    invert (nativeS p).toLaurent=T (-1)*(nativeS p).toLaurent := by
  simp only [nativeS,map_mul,map_add,toLaurent_C,toLaurent_X,map_one,
    invert_C,invert_T]
  have ht := shift_product p (-1)
  simp only [neg_neg] at ht
  linear_combination -LaurentPolynomial.C (1/5 : ZMod p)*ht

private theorem native_B_invert :
    invert (Polynomial.C (1/5 : ZMod p)*(4*X-11)).toLaurent=
      T (-1)*(Polynomial.C (1/5 : ZMod p)*(4-11*X)).toLaurent := by
  simp only [map_mul,map_sub,toLaurent_C,toLaurent_X,map_ofNat,
    invert_C,invert_T]
  have ht := shift_product p (-1)
  simp only [neg_neg] at ht
  linear_combination (11*LaurentPolynomial.C (1/5 : ZMod p))*ht

/-- The actual proper cross is the cleared product of the SAME original CB and its reciprocal. -/
theorem actual_CB_cross_product (hp : 19≤p) :
    (ActualFirstGreen.CB p).toLaurent*
      (T (((p-1)/2 : ℕ) : ℤ)*invert (ActualFirstGreen.CB p).toLaurent)=
      ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).toLaurent*
        actualCrossCarrier p := by
  let N := (p-1)/2
  let r := (p/6)%2
  let rn := (p/6+1)%2
  let M := (N-r)/2
  let eta := SourceClosureVbalIR61FourEnds.actualCrossHasseSign p
  let s := (nativeS p).toLaurent
  let b := (Polynomial.C (1/5 : ZMod p)*(4*X-11)).toLaurent
  let c := (Polynomial.C (1/5 : ZMod p)*(4-11*X)).toLaurent
  let y := (actualCBParityY0 p).toLaurent
  let n := (actualCBParityN0 p).toLaurent
  have hrn : r+rn=1 := actual_CB_parity_remainders p
  have hr : r=0 ∨ r=1 := by dsimp only [r]; omega
  have hM : 2*M+r=N := actual_half_parity p hp
  have hNp : 2*N+1=p := by
    dsimp only [N]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5 <;> omega
  have he : (actualCrossE p : ℤ)=(M : ℤ)+2-(r : ℤ) := by
    dsimp only [actualCrossE,N,M,r,rn] at *
    omega
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h55 : (1/5 : ZMod p)^2=1/25 := by
    field_simp [h5,h25]
    ring
  have hc55 : (LaurentPolynomial.C (1/5 : ZMod p) : (ZMod p)[T;T⁻¹])^2=
      LaurentPolynomial.C (1/25 : ZMod p) := by rw [←map_pow,h55]
  have hP : (actualHasseParity p).toLaurent=b^r*y := by
    rw [actualHasseParity,map_mul,map_pow]
    rfl
  have hrec : b^r*y=LaurentPolynomial.C eta*T ((M : ℤ)-(r : ℤ))*c^r*invert y := by
    have h := actual_Hasse_parity_reciprocal p hp
    rw [hP] at h
    change b^r*y=LaurentPolynomial.C eta*T (M : ℤ)*invert (b^r*y) at h
    have hib : invert b=T (-1)*c := native_B_invert p
    rw [map_mul,map_pow,hib,mul_pow] at h
    have hshift : (T ((M : ℤ)-(r : ℤ)) : (ZMod p)[T;T⁻¹])=
        T (M : ℤ)*T (-1)^r := by
      rw [T_pow,←T_add]
      congr 1
      omega
    rw [hshift]
    convert h using 1; ring
  have hcross := scalar_reciprocal_cross p eta
    (actual_cross_hasse_sign_square p hp) (M : ℤ) r hr b c y hrec
  have hcb : (ActualFirstGreen.CB p).toLaurent=
      LaurentPolynomial.C (1/5 : ZMod p)*s^(N+1)*b*y*n := by
    rw [actual_CB_full_parity_factor p hp]
    simp only [map_mul,map_pow,toLaurent_C]
    dsimp only [s,b,y,n,nativeS,N,WPFiniteWSource.squaredCoordinate]
    simp only [map_mul,toLaurent_C]
    rw [←hc55]
    ring
  have hf : ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).toLaurent=
      s^r*b^(2*r)*y^2 := by
    rw [actual_Hasse_native_norm p hp]
    rw [map_mul,map_pow,map_pow,hP]
    change s^r*(b^r*y)^2=s^r*b^(2*r)*y^2
    rw [mul_pow,←pow_mul,Nat.mul_comm r 2]
    ring
  have hbc : (Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X))).toLaurent=b*c := by
    dsimp only [b,c]
    simp only [map_mul,toLaurent_C]
    rw [←hc55]
    ring
  have hcarrier : actualCrossCarrier p=
      LaurentPolynomial.C (eta/25)*T (-(actualCrossE p : ℤ))*
        s^(p+rn)*(b*c)^rn*n*invert n := by
    rw [actualCrossCarrier,map_mul,map_mul,map_pow,map_pow]
    change LaurentPolynomial.C (eta/25)*T (-(actualCrossE p : ℤ))*
      (s^(p+rn)*(Polynomial.C (1/25 : ZMod p)*((4*X-11)*(4-11*X))).toLaurent^rn*
      n)*invert n=_
    rw [hbc]
    ring
  have hscalar : LaurentPolynomial.C (eta/25 : ZMod p)=
      LaurentPolynomial.C (1/25 : ZMod p)*LaurentPolynomial.C eta := by
    rw [←map_mul]
    congr 1
    ring
  have hcbprod : (ActualFirstGreen.CB p).toLaurent*
      (T (N : ℤ)*invert (ActualFirstGreen.CB p).toLaurent)=
      LaurentPolynomial.C (1/25 : ZMod p)*T (-2)*s^(p+1)*
        (b*c*y*invert y)*n*invert n := by
    rw [hcb]
    have his : invert s=T (-1)*s := native_S_invert p
    have hib : invert b=T (-1)*c := native_B_invert p
    simp only [map_mul,map_pow,invert_C,his,hib,mul_pow]
    have ht : (T (N : ℤ) : (ZMod p)[T;T⁻¹])*T (-1)^(N+1)*T (-1)=T (-2) := by
      rw [T_pow,←T_add,←T_add]
      congr 1
      push_cast
      ring
    have hpw : s^(N+1)*s^(N+1)=s^(p+1) := by rw [←pow_add]; congr 1; omega
    calc
      _ = LaurentPolynomial.C (1/5 : ZMod p)^2*
          (T (N : ℤ)*T (-1)^(N+1)*T (-1))*(s^(N+1)*s^(N+1))*
            (b*c*y*invert y)*n*invert n := by ring
      _ = _ := by rw [hc55,ht,hpw]
  have ht : (T (-2) : (ZMod p)[T;T⁻¹])*T ((r : ℤ)-(M : ℤ))=
      T (-(actualCrossE p : ℤ)) := by
    rw [←T_add,he]
    congr 1
    ring
  have hs : s^r*s^(p+rn)=s^(p+1) := by rw [←pow_add]; congr 1; omega
  have hfac : b^(2*r)*(b*c)^rn=b^(r+1)*c^(1-r) := by
    rcases hr with hr | hr
    · have hn1 : rn=1 := by omega
      rw [hr,hn1]
      ring
    · have hn0 : rn=0 := by omega
      rw [hr,hn0]
      ring
  rw [hcbprod,hcross,hf,hcarrier,hscalar]
  calc
    _ = LaurentPolynomial.C (1/25 : ZMod p)*LaurentPolynomial.C eta*
        (T (-2)*T ((r : ℤ)-(M : ℤ)))*s^(p+1)*
          (b^(r+1)*c^(1-r))*y^2*n*invert n := by ring
    _ = LaurentPolynomial.C (1/25 : ZMod p)*LaurentPolynomial.C eta*
        T (-(actualCrossE p : ℤ))*(s^r*s^(p+rn))*
          (b^(2*r)*(b*c)^rn)*y^2*n*invert n := by rw [ht,hs,hfac]
    _ = _ := by ring

end WPFieldAssembly.BalancedVbalSuccessorCrossAttachment
