import WPFieldAssembly.ActualUVSourceIdentification
import WPFieldAssembly.SourceClosureHalfPrimitiveTransport
import WPFieldAssembly.SourceClosureWEndpoint
import WPFiniteJWeightedResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.SourceClosureHalfPrimitive
  WPFieldAssembly.SourceClosureHalfPrimitiveTransport

namespace WPFieldAssembly.SourceClosureUVEndpoint

/- STATEMENT_FIDELITY: the literal UW17b--e branch x=-1 of the original
   Ucan. All four primitives have their complete D_N cutoff, including
   diagonal terms. The original integer Q3 and R(-4)/6 are retained.
   This unit identifies the integration constant; it does not identify
   the actual rational VS or infer a common-trace value. -/

variable {K : Type*} [Field K]

theorem originalW_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (WPFiniteWSource.W p).eval (-1)=
      -2*(WPFiniteABSourceTail.epsilon p : K)*WPFifthEntropy.C p u/15 := by
  have h0 : (WPFiniteWSource.deltaE p : K[X]).eval 0=0 := by
    simp only [WPFiniteWSource.deltaE,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j≠0 := by have := (Finset.mem_Ico.mp hj).1; omega
    simp only [zero_pow hj0,mul_zero]
  simp only [WPFiniteWSource.W,eval_mul,eval_C,eval_sub,eval_comp,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,
    neg_add_cancel,mul_zero,h0,WPFiniteWSource.deltaE_fifth p hp u hu]
  ring

theorem unitPrimitive_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (c : K) :
    (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) c).eval (-1)=
      -(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.D ((p-1)/2) (4/5) (4*((1+c)/5))-
          WPFiniteLoop.D ((p-1)/2) (1/5) ((1+c)/5)) := by
  rw [original_unitPrimitive_eval_full p hp]
  simp only [add_neg_cancel,mul_zero,zero_div,WPFiniteLoop.D_zero_left]
  ring

theorem unitPrimitive_branch_quadratic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u c y : K) (hu : u^2=1/5) (hy : y^2=(1+c)/5) :
    (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) c).eval (-1)=
      -(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.S p (2*u) (2*y)-WPFiniteLoop.S p u y) := by
  rw [unitPrimitive_branch p hp]
  have hu4 : (2*u)^2=4/5 := by rw [mul_pow,hu]; norm_num; ring
  have hy4 : (2*y)^2=4*((1+c)/5) := by rw [mul_pow,hy]; norm_num
  simp only [WPFiniteLoop.S,hu4,hy4,hu,hy]

theorem originalH_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (originalHx p).eval (-1)=-(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.S p (2*u) (2*u)-WPFiniteLoop.S p u u) ∧
      (originalHa p).eval (-1)=-(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.S p (2*u) 1-WPFiniteLoop.S p u (1/2)) ∧
      (originalHb p).eval (-1)=-(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.S p (2*u) 2-WPFiniteLoop.S p u 1) ∧
      (originalHm p).eval (-1)=-(WPFiniteABSourceTail.epsilon p/15 : K)*
        (WPFiniteLoop.S p (2*u) 0-WPFiniteLoop.S p u 0) := by
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hx := unitPrimitive_branch_quadratic p hp u 0 u hu (by simpa using hu)
  have ha := unitPrimitive_branch_quadratic p hp u (1/4) (1/2) hu (by
    field_simp [h2,h4,h5]
    ring)
  have hb := unitPrimitive_branch_quadratic p hp u 4 1 hu (by
    field_simp [h5]
    ring)
  have hm := unitPrimitive_branch_quadratic p hp u (-1) 0 hu (by simp)
  have hhalf : (2 : K)*(1/2)=1 := by field_simp [h2]
  simp only [hhalf] at ha
  simp only [mul_one] at hb
  simp only [mul_zero] at hm
  simpa only [originalHx,originalHa,originalHb,originalHm,mul_zero]
    using ⟨hx,ha,hb,hm⟩

theorem originalZE_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    originalZE p u=-(WPFiniteABSourceTail.epsilon p : K)*
      (4*WPFiniteNC122.q p+3*(WPFiniteInversion.integerFermatQuotient p 3 : K))/30 := by
  rw [originalZE,←WPFiniteWSource.deltaE_fifth p hp u hu,
    ←WPFieldAssembly.SourceClosureWEndpoint.squaredEntropyC_deltaE]
  exact WPFieldAssembly.SourceClosureWEndpoint.actual_W_endpoint_balance p hp

theorem originalJab_branch (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ)
      (originalJa p+originalJb p)=-5*WPFiniteField.ell p (-4)/
        WPFiniteABSourceTail.epsilon p := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpneg : (-1 : K)^p=-1 := by simpa using hodd.neg_pow (1 : K)
  have h4p : (-4 : K)^p=-4 := by
    rw [hodd.neg_pow (4 : K)]
    exact congrArg (fun z : K => -z) (WPFiniteField.natCast_pow_char p 4)
  have hinv := WPFiniteField.ell_inversion p (-4 : K) (neg_ne_zero.mpr h4)
  rw [h4p,show (-4 : K)⁻¹=-(1/4 : K) by simp only [inv_neg,one_div]] at hinv
  simp only [originalJa,originalJb,map_add,map_mul,map_sub,
    LaurentPolynomial.eval₂_C,LaurentPolynomial.eval₂_T_neg_n,
    RingHom.id_apply,Units.val_neg,Units.val_one,
    inv_neg,inv_one,hpneg,
    scaledLog,LaurentPolynomial.eval₂_toLaurent,eval₂_id,eval_comp,
    eval_mul,eval_C,eval_X,WPFiniteAffineLog.LP_eval_eq,mul_neg,mul_one]
  rw [hinv]
  field_simp [h4,heps]
  ring

/-- The original full constant is derived from the actual branch value. -/
theorem originalUcan_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (originalUcan p u)=
      originalU0 p u := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have h6 : (6 : K)≠0 := by
    rw [show (6 : K)=2*3 by ring]
    exact mul_ne_zero h2 h3
  have heps : (WPFiniteABSourceTail.epsilon p : K)≠0 := pow_ne_zero _ h5
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpneg : (-1 : K)^p=-1 := by simpa using hodd.neg_pow (1 : K)
  have hh := originalH_branch p hp u hu
  rw [originalUcan,map_sub,map_sub,map_mul,map_mul,map_mul,
    LaurentPolynomial.eval₂_C,RingHom.id_apply,originalZE_value p hp u hu,
    originalJab_branch p hp,originalJ2log_branch p hp]
  simp only [originalK0,originalHsym,map_add,map_sub,map_mul,
    LaurentPolynomial.eval₂_C,WPFiniteJWeightedResidue.inversion_eval,
    inv_neg,inv_one,LaurentPolynomial.eval₂_toLaurent,eval₂_id,
    Units.val_neg,Units.val_one,LaurentPolynomial.eval₂_T_n,
    LaurentPolynomial.eval₂_T_neg_n,RingHom.id_apply,hpneg]
  rw [hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
  unfold originalU0
  field_simp [h2,h3,h5,h6,h15,h30,heps]
  ring

theorem originalU_branch_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ) (originalU p u)=0 := by
  rw [originalU,map_sub,originalUcan_branch p hp u hu,
    LaurentPolynomial.eval₂_C,RingHom.id_apply,sub_self]

end WPFieldAssembly.SourceClosureUVEndpoint
