import WPFieldAssembly.SourceClosureUVJointSource
import WPFieldAssembly.SourceClosureUVWeightedK0
import WPFieldAssembly.SourceClosureUVWeightedContraction

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureSigmaProperEndpoint WPFieldAssembly.SourceClosureSigmaGclosed
  WPFieldAssembly.SourceClosureActualUVAttachment WPFieldAssembly.SourceClosureUVJointSource
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWeightedContraction WPFieldAssembly.SourceClosureUVWeightedK0

namespace WPFieldAssembly.SourceClosureUVWholeContraction

/- UW18d is an equality for the same actual whole UV, not a new scalar
   assignment. The full Tprod contraction and the same p-hole remain. -/

theorem original_Hm_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p
      (originalK0 p*((originalHm p).toLaurent+invert (originalHm p).toLaurent))=
      -(33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalHm p).eval (1/4)+(originalHm p).eval 4) := by
  have hdeg := (originalH_degree (K:=ZMod p) p hp).2.2.2
  have hdegree : (originalHm p : (ZMod p)[X]).natDegree<p :=
    hdeg.trans_lt (by omega)
  have h0 : (originalHm p : (ZMod p)[X]).coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero]
    exact WPFiniteProductTail.unitPrimitiveP_zero p _ _
  simpa only [h0,mul_zero,add_zero] using
    originalK0_low_symmetric_weight p hp (originalHm p) hdegree

theorem weighted_constant_zero (p : ℕ) [Fact p.Prime] (hp : 19≤p) (c : ZMod p) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c)=0 := by
  simpa only [T_zero, mul_one] using weighted_nonpositive p hp 0 (by omega) c

/-- The complete UW18d contraction retains the original product and its canonical p-hole. -/
theorem actualUV_whole_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (actualUV p hp)=
      -originalWeightedFieldTrace p (endSym (fourUnitField p hp) (Tprod p)) +
      (99/4 : ZMod p)*(Tprod p).coeff (p : ℤ) +
      (33/(4*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalHm p).eval (1/4)+(originalHm p).eval 4) -
      ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)*
        WPFiniteField.ell p (16 : ZMod p)/10 +
      WPFiniteField.R p (16 : ZMod p)/20 := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : ZMod p)≠0 := by
    rw [show (20 : ZMod p)=4*5 by ring]
    exact mul_ne_zero h4 h5
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  have hH : originalWeightedFieldTrace p
      (LaurentPolynomial.C (1/2 : ZMod p)*originalK0 p*
        ((originalHm p).toLaurent+invert (originalHm p).toLaurent))=
      -(33/(4*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalHm p).eval (1/4)+(originalHm p).eval 4) := by
    rw [mul_assoc,weighted_C_mul,original_Hm_weight p hp]
    field_simp [h2,h4,heps]; ring
  have hJ : originalWeightedFieldTrace p
      (LaurentPolynomial.C
        (WPFiniteABSourceTail.epsilon p*
          ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)/15)*
        (originalJa p+originalJb p))=
      -(((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)*
        WPFiniteField.ell p (16 : ZMod p)/10) := by
    rw [weighted_C_mul,original_Jab_weight p hp]
    field_simp [h2,h10,h15,heps]; ring
  have hD : originalWeightedFieldTrace p
      (LaurentPolynomial.C (1/2 : ZMod p)*originalJ2log p)=
      -(WPFiniteField.R p (16 : ZMod p)/20) := by
    rw [weighted_C_mul,original_J2_weight p hp]
    field_simp [h2,h10,h20]; ring
  rw [actualUV_joint_weight_p_hole p hp,jointUncanonicalUV,
    weighted_sub,weighted_sub,weighted_add,weighted_sub,
    show originalWeightedFieldTrace p (-endSym (fourUnitField p hp) (Tprod p))=
      -originalWeightedFieldTrace p (endSym (fourUnitField p hp) (Tprod p)) by
      simp only [originalWeightedFieldTrace, mul_neg, map_neg],
    hH,hJ,hD,weighted_constant_zero p hp]
  ring

/-- The actual p-hole cancels with its own branch term before any arithmetic collection. -/
theorem actualUV_whole_weight_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp)-
      (66/25 : ZMod p)*actualMu p hp =
      -(2/3 : ZMod p)*originalWeightedFieldTrace p (endSym (fourUnitField p hp) (Tprod p)) +
      (11/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalHm p).eval (1/4)+(originalHm p).eval 4) -
      ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-4*descendedC p)*
        WPFiniteField.ell p (16 : ZMod p)/15 +
      WPFiniteField.R p (16 : ZMod p)/30 -
      (66/25 : ZMod p)*jointUncanonicalMu p hp := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : ZMod p)≠0 := by
    rw [show (20 : ZMod p)=4*5 by ring]
    exact mul_ne_zero h4 h5
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5*5 by ring]
    exact mul_ne_zero h5 h5
  have h30 : (30 : ZMod p)≠0 := by
    rw [show (30 : ZMod p)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  rw [actualUV_whole_weight p hp, actualMu_joint_p_hole p hp]
  field_simp [h2, h3, h4, h5, h10, h15, h20, h25, h30, heps]
  ring

end WPFieldAssembly.SourceClosureUVWholeContraction
