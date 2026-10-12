import WPFieldAssembly.ConicKernel
import Mathlib.Algebra.Polynomial.Derivative

open scoped Polynomial LaurentPolynomial
open Polynomial WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.SourceClosureVbalConicExact

set_option maxHeartbeats 1600000

/-- The full native exact primitive descends through the original cubic conic without an inverse Y. -/
theorem conic_exact_primitive_cleared {K : Type*} [Field K]
    (p : ℕ) (hp : (p : K)=0) (h2 : (2 : K)≠0) (h5 : (5 : K)≠0)
    (J NR Jx NRx : K[X])
    (hJ : Jx.comp (5*X^2-1)=C (1/5 : K)*X^p*J.comp (4*X^3-3*X))
    (hNR : NRx.comp (5*X^2-1)=C (1/5 : K)*X^p*NR.comp (4*X^3-3*X))
    (hsource : (1-X^2)*J.derivative= -2*X*NR) :
    ((4-X)*(4*X-1))*Jx.derivative= -3*(4*X-11)*NRx := by
  let x : K[X] := 5*X^2-1
  let Tc : K[X] := 4*X^3-3*X
  let q : K[X] := 1-X^2
  let b : K[X] := 4*X^2-1
  change Jx.comp x=C (1/5 : K)*X^p*J.comp Tc at hJ
  change NRx.comp x=C (1/5 : K)*X^p*NR.comp Tc at hNR
  have hdx : x.derivative=10*X := by
    dsimp only [x]
    norm_num [derivative_sub,derivative_mul,derivative_pow,C_ofNat]
    ring
  have hdT : Tc.derivative=3*b := by
    dsimp only [Tc,b]
    norm_num [derivative_sub,derivative_mul,derivative_pow,C_ofNat]
    ring
  have hpD : (X^p : K[X]).derivative=0 := by
    rw [derivative_X_pow,hp,C_0,zero_mul]
  have hD := congrArg Polynomial.derivative hJ
  rw [derivative_comp,hdx] at hD
  simp only [derivative_mul,derivative_C,hpD,derivative_comp,hdT,
    zero_mul,mul_zero,zero_add,add_zero] at hD
  have hqT : (1-X^2 : K[X]).comp Tc=q*b^2 := by
    simp only [sub_comp,one_comp,pow_comp,X_comp,Tc,q,b]
    ring
  have hS := congrArg (fun P : K[X] => P.comp Tc) hsource
  simp only [mul_comp,hqT,neg_comp,ofNat_comp,X_comp] at hS
  have hA : ((4-X)*(4*X-1) : K[X]).comp x=25*q*b := by
    simp only [mul_comp,sub_comp,ofNat_comp,one_comp,X_comp,x,q,b]
    ring
  have hB : 4*x-11=5*(4*X^2-3) := by dsimp only [x]; ring
  have hc : (5 : K[X])*C (1/5 : K)=1 := by
    change C (5 : K)*C (1/5 : K)=1
    rw [←C_mul,mul_one_div_cancel h5,C_1]
  have hc75 : (75 : K[X])*C (1/5 : K)=15 := by linear_combination 15*hc
  have h10 : (10 : K)≠0 := by
    rw [show (10 : K)=2*5 by ring]
    exact mul_ne_zero h2 h5
  have h10P : (10*X : K[X])≠0 :=
    mul_ne_zero (by simpa only [C_ofNat] using (Polynomial.C_ne_zero.mpr h10)) X_ne_zero
  have hdeg : x.natDegree=2 := by
    dsimp only [x]
    compute_degree
    exact h5
  apply comp_injective_nonconstant x (by rw [hdeg]; norm_num)
  simp only [mul_comp,neg_comp,ofNat_comp,sub_comp,X_comp,one_comp]
  rw [hNR]
  apply mul_left_cancel₀ h10P
  calc
    _ = (25*q*b)*((Jx.derivative.comp x)*(10*X)) := by
      have ha := hA
      simp only [mul_comp,sub_comp,ofNat_comp,one_comp,X_comp] at ha
      rw [ha]
      ring
    _ = (25*q*b)*(C (1/5 : K)*X^p*(J.derivative.comp Tc)*(3*b)) := by
      linear_combination (25*q*b)*hD
    _ = (75*C (1/5 : K))*X^p*((q*b^2)*(J.derivative.comp Tc)) := by ring
    _ = -30*X^p*Tc*(NR.comp Tc) := by rw [hc75,hS]; ring
    _ = _ := by
      simp only [Nat.cast_ofNat]
      rw [hB]
      dsimp only [Tc]
      linear_combination 30*X^p*(4*X^3-3*X)*(NR.comp (4*X^3-3*X))*hc

end WPFieldAssembly.SourceClosureVbalConicExact
