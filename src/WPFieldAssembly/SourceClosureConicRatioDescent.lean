import WPFieldAssembly.SourceClosureConicWeightedDivision
import WPFieldAssembly.ActualGreenPrimitive

open scoped Polynomial
open Polynomial WPFieldAssembly.SourceClosureConicWeightedDivision
  WPFieldAssembly.ActualGreenPrimitive WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.SourceClosureConicRatioDescent

set_option maxHeartbeats 1600000

/-- Proper conic division descends to the original multiplier, including its zeros at x=0. -/
theorem actual_conic_ratio_division {K : Type*} [Field K]
    (f Q A y m : K[X]) (hy : y≠0)
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h4 : (4 : K)≠0) (h5 : (5 : K)≠0)
    (hf : f.comp (5*X^2-1)=y^2)
    (hw : A*(y*m.derivative-y.derivative*m)=1-y^2)
    (hs : f*Q.derivative-2*Q*f.derivative=0) :
    ∃ B : K[X], Q=f^2*B ∧ B.derivative=0 := by
  let x : K[X] := 5*X^2-1
  have hx : x.comp (-X)=x := by
    simp only [x,sub_comp,mul_comp,ofNat_comp,pow_comp,X_comp,one_comp]
    ring
  have hc : (f.comp x)*(Q.comp x).derivative-
      2*(Q.comp x)*(f.comp x).derivative=0 := by
    have ht := congrArg (fun P : K[X] => P.comp x) hs
    simp only [mul_comp,sub_comp,ofNat_comp,zero_comp] at ht
    rw [derivative_comp,derivative_comp]
    linear_combination x.derivative*ht
  change f.comp x=y^2 at hf
  rw [hf] at hc
  obtain ⟨Bt,hBt,_⟩ := squared_multiplier_ratio_division A y m (Q.comp x) hy
    h2 h3 h4 hw hc
  have hye : (y^2).comp (-X)=y^2 := by rw [←hf,comp_assoc,hx]
  have hy4e : (y^4).comp (-X)=y^4 := by
    calc
      _=((y^2)^2).comp (-X) := by congr 1; ring
      _=(y^2)^2 := by rw [pow_comp,hye]
      _=y^4 := by ring
  have hte : Bt.comp (-X)=Bt := by
    apply mul_left_cancel₀ (pow_ne_zero 4 hy)
    have he := congrArg (fun P : K[X] => P.comp (-X)) hBt
    simp only [comp_assoc,hx,mul_comp,hy4e] at he
    rw [hBt] at he
    exact he.symm
  let B : K[X] := (contract 2 Bt).comp (C (1/5 : K)*(X+1))
  have hb : B.comp x=Bt := by
    have ht := even_expand_contract Bt h2 hte
    rw [expand_eq_comp_X_pow] at ht
    have hcoord : (C (1/5 : K)*(X+1)).comp x=X^2 := by
      simp only [mul_comp,C_comp,add_comp,X_comp,one_comp,x]
      have hi : (C (1/5 : K) : K[X])*5=1 := by
        change C (1/5 : K)*C (5 : K)=1
        rw [←C_mul,one_div_mul_cancel h5,C_1]
      linear_combination X^2*hi
    simpa only [B,comp_assoc,hcoord] using ht
  have hxdeg : x.natDegree=2 := by
    dsimp only [x]
    compute_degree
    exact h5
  have hQ : Q=f^2*B := by
    apply comp_injective_nonconstant x (by rw [hxdeg]; norm_num)
    change Q.comp x=(f^2*B).comp x
    rw [mul_comp,pow_comp,hf,hb,hBt]
    ring
  have hf0 : f≠0 := by
    intro hz
    rw [hz,zero_comp] at hf
    exact (pow_ne_zero 2 hy) hf.symm
  refine ⟨B,hQ,?_⟩
  have hd : f^3*B.derivative=0 := by
    rw [hQ] at hs
    simp only [derivative_mul,derivative_sq,C_ofNat] at hs
    linear_combination hs
  exact (mul_eq_zero.mp hd).resolve_left (pow_ne_zero 3 hf0)

end WPFieldAssembly.SourceClosureConicRatioDescent
