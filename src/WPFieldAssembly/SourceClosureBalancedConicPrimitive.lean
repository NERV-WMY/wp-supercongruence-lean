import WPFieldAssembly.ConicKernel
import Mathlib.Algebra.Polynomial.Derivative

open scoped Polynomial
open Polynomial WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.SourceClosureBalancedConicPrimitive

set_option maxHeartbeats 1600000

/-- The original cubic conic transports the whole proper primitive source.
The factor X^p is differentiated in the field only after its full source is retained. -/
theorem conic_primitive_cleared {K : Type*} [Field K]
    (p N : ℕ) (hN : 2*N+1=p) (hp : (p : K)=0) (h5 : (5 : K)≠0)
    (f F H Sigma TB Hx Sigmax TBx : K[X]) (h : K)
    (hf : f.comp (5*X^2-1)=F.comp (4*X^3-3*X))
    (hH : Hx.comp (5*X^2-1)=C (1/5 : K)*X^p*H.comp (4*X^3-3*X))
    (hSigma : Sigmax.comp (5*X^2-1)=Sigma.comp (4*X^3-3*X))
    (hTB : TBx.comp (5*X^2-1)=TB.comp (4*X^3-3*X))
    (hsource : (1-X^2)*(F*H.derivative-F.derivative*H)=
      Sigma+C h*F^2+F*TB) :
    2*(X+1)*((4-X)*(4*X-1))*
        (f*Hx.derivative-Hx*f.derivative)=
      3*(X+1)*(C (1/5 : K)*(X+1))^N*(Sigmax+C h*f^2+f*TBx) := by
  let x : K[X] := 5*X^2-1
  let T : K[X] := 4*X^3-3*X
  let q : K[X] := 1-X^2
  let b : K[X] := 4*X^2-1
  change f.comp x=F.comp T at hf
  change Hx.comp x=C (1/5 : K)*X^p*H.comp T at hH
  change Sigmax.comp x=Sigma.comp T at hSigma
  change TBx.comp x=TB.comp T at hTB
  have hdx : x.derivative=10*X := by
    dsimp only [x]
    norm_num [derivative_sub,derivative_mul,derivative_pow,derivative_ofNat,C_ofNat]
    ring
  have hdT : T.derivative=3*b := by
    dsimp only [T,b]
    norm_num [derivative_sub,derivative_mul,derivative_pow,derivative_ofNat,C_ofNat]
    ring
  have hpD : (X^p : K[X]).derivative=0 := by
    rw [derivative_X_pow,hp,C_0,zero_mul]
  have hdc := congrArg Polynomial.derivative hH
  change (Hx.comp x).derivative=(C (1/5 : K)*X^p*H.comp T).derivative at hdc
  rw [derivative_comp,hdx] at hdc
  simp only [derivative_mul,derivative_C,hpD,derivative_comp,hdT,
    zero_mul,mul_zero,zero_add,add_zero] at hdc
  have hdf := congrArg Polynomial.derivative hf
  change (f.comp x).derivative=(F.comp T).derivative at hdf
  rw [derivative_comp,hdx,derivative_comp,hdT] at hdf
  have hm := congrArg (fun P : K[X] => P.comp T) hsource
  have hqT : q.comp T=q*b^2 := by
    dsimp only [q,b,T]
    simp only [sub_comp,one_comp,pow_comp,X_comp]
    ring
  change (q*(F*H.derivative-F.derivative*H)).comp T=
    (Sigma+C h*F^2+F*TB).comp T at hm
  simp only [mul_comp,sub_comp,add_comp,pow_comp,C_comp,hqT] at hm
  have ha : ((4-X)*(4*X-1) : K[X]).comp x=25*q*b := by
    dsimp only [x,q,b]
    simp only [mul_comp,sub_comp,ofNat_comp,one_comp,X_comp]
    ring
  have hs : (C (1/5 : K)*(X+1)).comp x=X^2 := by
    simp only [mul_comp,C_comp,add_comp,X_comp,one_comp,x]
    have hc : C (1/5 : K)*5=1 := by
      change C (1/5 : K)*C (5 : K)=1
      rw [←C_mul,one_div_mul_cancel h5,C_1]
    linear_combination X^2*hc
  have hxp : x+1=5*X^2 := by dsimp only [x]; ring
  have hpow : (X^2 : K[X])^N*X^2=X^(p+1) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  have hpow' : (X^2 : K[X])^N*(5*X^2)=5*X^(p+1) := by
    linear_combination 5*hpow
  have hcd : x.natDegree=2 := by
    dsimp only [x]
    compute_degree
    exact h5
  apply comp_injective_nonconstant x (by rw [hcd]; norm_num)
  simp only [mul_comp,sub_comp,add_comp,pow_comp,ofNat_comp,C_comp,one_comp,X_comp,Nat.cast_ofNat]
  rw [hf,hH,hSigma,hTB]
  have ha' : (4-x)*(4*x-1)=25*q*b := by
    simpa only [mul_comp,sub_comp,ofNat_comp,one_comp,X_comp,Nat.cast_ofNat] using ha
  have hs' : C (1/5 : K)*(x+1)=X^2 := by
    simpa only [mul_comp,C_comp,add_comp,X_comp,one_comp] using hs
  rw [ha',hs']
  change 2*(x+1)*(25*q*b)*
      ((F.comp T)*(Hx.derivative.comp x)-
        (C (1/5 : K)*X^p*H.comp T)*(f.derivative.comp x))=
    3*(x+1)*(X^2)^N*(Sigma.comp T+C h*(F.comp T)^2+(F.comp T)*(TB.comp T))
  rw [hxp,mul_assoc 3 (5*X^2) ((X^2)^N),
    mul_comm (5*X^2) ((X^2)^N),hpow',pow_succ]
  have hc : 5*C (1/5 : K)=1 := by
    change C (5 : K)*C (1/5 : K)=1
    rw [←C_mul,mul_one_div_cancel h5,C_1]
  linear_combination
    25*X*q*b*(F.comp T)*hdc-
      25*X*q*b*(C (1/5 : K)*X^p*H.comp T)*hdf+
      15*X^p*X*hm+
      15*X^p*X*q*b^2*((F.comp T)*(H.derivative.comp T)-
        (F.derivative.comp T)*(H.comp T))*hc

end WPFieldAssembly.SourceClosureBalancedConicPrimitive
