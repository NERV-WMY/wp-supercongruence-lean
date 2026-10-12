import WPFieldAssembly.SourceClosureHalfPrimitive

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFieldAssembly.SourceClosureHalfPrimitive

namespace WPFieldAssembly.SourceClosureHalfPrimitiveTransport

/- STATEMENT_FIDELITY: identify UW17a's full D_N expression with the
   original actual zero-origin unit primitive of W. The exact squared
   coordinate and full cutoff are retained. No finite manifest is used.
   This unit does not identify the actual VS carry or assign the trace. -/

variable {K : Type*} [Field K]

theorem originalW_halfLog (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteWSource.W p : K[X])=
      C (WPFiniteABSourceTail.epsilon p/15 : K)*
        ((halfLogP p).comp (4*WPFiniteWSource.squaredCoordinate)-
          (halfLogP p).comp WPFiniteWSource.squaredCoordinate-
          C ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5))) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hc : C (2*WPFiniteABSourceTail.epsilon p/15 : K)*C (1/2 : K)=
      C (WPFiniteABSourceTail.epsilon p/15 : K) := by
    rw [←C_mul]
    congr 1
    field_simp [h2,h15]
  rw [WPFiniteWSource.W,deltaE_halfLog]
  simp only [mul_comp,C_comp,sub_comp,comp_assoc,ofNat_comp,X_comp,
    eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,eval_X]
  calc
    _ = C (2*WPFiniteABSourceTail.epsilon p/15 : K)*C (1/2 : K)*
        ((halfLogP p).comp (4*WPFiniteWSource.squaredCoordinate)-
          (halfLogP p).comp WPFiniteWSource.squaredCoordinate-
          C ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5))) := by
      simp only [C_mul,C_sub]
      ring
    _ = _ := by rw [hc]

theorem finitePrimitive_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c : K) :
    (X-C c)*(finitePrimitive p c).derivative=
      WPFiniteWSource.W p-C ((WPFiniteWSource.W p).eval c) := by
  let s : K[X] := WPFiniteWSource.squaredCoordinate
  let sc : K := (1+c)/5
  have hs : s.derivative=C (1/5 : K) := by
    simp [s,WPFiniteWSource.squaredCoordinate,one_div,derivative_mul]
  have hs4 : (4*s).derivative=C (4/5 : K) := by
    rw [show (4 : K[X])=C (4 : K) from rfl,derivative_C_mul,hs,←C_mul]
    congr 1
    ring
  have hscC : (C sc : K[X])=C (1/5 : K)*(1+C c) := by
    dsimp only [sc]
    rw [show (1+c)/5=(1/5 : K)*(1+c) by ring, C_mul, C_add, C_1]
  have hf1 : (X-C c)*C (1/5 : K)=s-C sc := by
    rw [hscC]
    dsimp only [s,WPFiniteWSource.squaredCoordinate]
    ring
  have hf4 : (X-C c)*C (4/5 : K)=4*s-C (4*sc) := by
    rw [show (4/5 : K)=4*(1/5) by ring]
    simp only [C_mul,C_ofNat]
    linear_combination 4*hf1
  have he1 := congrArg (fun P : K[X] => P.comp s) (halfDP_source p hp sc)
  have he4 := congrArg (fun P : K[X] => P.comp (4*s)) (halfDP_source p hp (4*sc))
  simp only [mul_comp,sub_comp,X_comp,C_comp] at he1 he4
  have hd1 : (X-C c)*((halfDP p sc).comp s).derivative=
      (halfLogP p).comp s-C ((halfLogP p).eval sc) := by
    rw [derivative_comp,hs]
    calc
      _=(s-C sc)*(halfDP p sc).derivative.comp s := by
        linear_combination (halfDP p sc).derivative.comp s*hf1
      _=_ := he1
  have hd4 : (X-C c)*((halfDP p (4*sc)).comp (4*s)).derivative=
      (halfLogP p).comp (4*s)-C ((halfLogP p).eval (4*sc)) := by
    rw [derivative_comp,hs4]
    calc
      _=(4*s-C (4*sc))*(halfDP p (4*sc)).derivative.comp (4*s) := by
        linear_combination (halfDP p (4*sc)).derivative.comp (4*s)*hf4
      _=_ := he4
  have hsc : s.eval c=sc := by
    simp only [s,sc,WPFiniteWSource.squaredCoordinate,eval_mul,eval_C,
      eval_add,eval_X,eval_one]
    ring
  rw [originalW_halfLog p hp]
  change (X-C c)*(finitePrimitive p c).derivative=
    C (WPFiniteABSourceTail.epsilon p/15 : K)*
      ((halfLogP p).comp (4*s)-(halfLogP p).comp s-
        C ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5)))-
      C ((C (WPFiniteABSourceTail.epsilon p/15 : K)*
        ((halfLogP p).comp (4*s)-(halfLogP p).comp s-
          C ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5)))).eval c)
  simp only [eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,hsc]
  change (X-C c)*(finitePrimitive p c).derivative=
    C (WPFiniteABSourceTail.epsilon p/15 : K)*
      ((halfLogP p).comp (4*s)-(halfLogP p).comp s-
        C ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5)))-
      C (WPFiniteABSourceTail.epsilon p/15*
        ((halfLogP p).eval (4*sc)-(halfLogP p).eval sc-
          ((halfLogP p).eval (4/5)-(halfLogP p).eval (1/5))))
  simp only [finitePrimitive,derivative_C_mul,derivative_sub,derivative_C,
    sub_zero,C_mul,C_sub]
  change (X-C c)*(C (WPFiniteABSourceTail.epsilon p/15 : K)*
    (((halfDP p (4*sc)).comp (4*s)).derivative-
      ((halfDP p sc).comp s).derivative))=_
  linear_combination C (WPFiniteABSourceTail.epsilon p/15 : K)*(hd4-hd1)

/-- Actual coefficient-source identification, including the zero-origin convention. -/
theorem original_unitPrimitive_eq_finite (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c : K) :
    WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) c=
      finitePrimitive p c := by
  symm
  exact WPFinitePrimitiveTransport.unitPrimitiveP_unique p _
    ((WPFiniteWSource.W_degree p hp).trans_lt (by omega))
    (WPFiniteWSource.W_origin p) c _
    ((finitePrimitive_degree p c).trans_lt (by omega))
    (finitePrimitive_origin p c) (finitePrimitive_source p hp c)

/-- The complete original D_N evaluation; its diagonal is not deleted. -/
theorem original_unitPrimitive_eval_full (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c y : K) :
    (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) c).eval y=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.D ((p-1)/2) (4*((1+y)/5)) (4*((1+c)/5))-
          WPFiniteLoop.D ((p-1)/2) ((1+y)/5) ((1+c)/5)-
          WPFiniteLoop.D ((p-1)/2) (4/5) (4*((1+c)/5))+
          WPFiniteLoop.D ((p-1)/2) (1/5) ((1+c)/5)) := by
  rw [original_unitPrimitive_eq_finite p hp c]
  simp only [finitePrimitive,eval_mul,eval_C,eval_sub,eval_comp,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,eval_ofNat,
    halfDP_eval]
  have hs : (5 : K)⁻¹*(y+1)=(1+y)/5 := by
    simp only [div_eq_mul_inv]
    ring
  rw [hs]
  ring

end WPFieldAssembly.SourceClosureHalfPrimitiveTransport
