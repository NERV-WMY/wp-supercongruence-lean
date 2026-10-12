import WPFieldAssembly.SourceClosureUVJointEndpoint
import WPFieldAssembly.SourceClosureUVTprodWeight
import WPFieldAssembly.SourceClosureUVOrderedH

open scoped BigOperators Polynomial
open Polynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureHalfPrimitive
  WPFieldAssembly.SourceClosureHalfPrimitiveTransport
  WPFieldAssembly.SourceClosureUVDescent WPFieldAssembly.SourceClosureWEndpoint
  WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.SourceClosureUVTprodWeight

namespace WPFieldAssembly.SourceClosureUVFiniteEnds

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/- These are evaluations of the actual W, W1 and Hm polynomials. The
   full half cutoff and its diagonal survive the consumer's 2/3 factor. -/

theorem evenSquared_eval_halfLog (p : ℕ) (x : K) :
    (WPFiniteLVSource.evenSquared p).eval x=WPFiniteLoop.L ((p-1)/2) x/2 := by
  simp only [WPFiniteLVSource.evenSquared,WPFiniteLoop.L,eval_finsetSum,
    eval_mul,eval_C,eval_pow,eval_X,div_eq_mul_inv,mul_inv_rev]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_W_ends_finite (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteWSource.W p : K[X]).eval (1/4)=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (-4*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
          (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)-2*descendedC p) ∧
    (WPFiniteWSource.W p : K[X]).eval 4=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (2*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
          3*(WPFiniteInversion.integerFermatQuotient p 3 : K)-2*descendedC p) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hC : WPFiniteLoop.L ((p-1)/2) (4/5 : K)-
      WPFiniteLoop.L ((p-1)/2) (1/5 : K)=2*descendedC p := by
    rw [descendedC,←squaredEntropyC_deltaE,squaredEntropyC_halfLog]
    field_simp [h2]
  have ha : (5 : K)⁻¹*((1/4)+1)=1/4 := by field_simp [h4,h5]; ring
  have hb : (5 : K)⁻¹*(4+1)=1 := by field_simp [h5]; ring
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  obtain ⟨hL1,hL4,hLa⟩ := WPFiniteLoop.L_rational_ends (K:=K) p hp
  simp only [originalW_halfLog p hp,eval_mul,eval_C,eval_sub,eval_comp,eval_ofNat,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,halfLogP_eval,
    ha,hb,h4a,mul_one,hL1,hL4,hLa]
  constructor <;>
    linear_combination (norm := (field_simp [h2,h15]; ring))
      -(WPFiniteABSourceTail.epsilon p/15)*hC

theorem actual_W1_ends_finite (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (originalW1Field p).eval (1/4)=
      (2*WPFiniteABSourceTail.epsilon p/15 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          (WPFiniteLVSource.evenSquared p).eval (4/5)) ∧
    (originalW1Field p).eval 4=
      (2*WPFiniteABSourceTail.epsilon p/15 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        ((3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
          (WPFiniteLVSource.evenSquared p).eval (4/5)) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ha : (4 : ZMod p)*((5 : ZMod p)⁻¹*((1/4)+1))=1 := by
    field_simp [h4,h5]; ring
  have hb : (4 : ZMod p)*((5 : ZMod p)⁻¹*(4+1))=4 := by
    field_simp [h5]
    ring
  obtain ⟨hL1,hL4,_⟩ := WPFiniteLoop.L_rational_ends (K:=ZMod p) p hp
  simp only [originalW1Field_formula p hp,eval_mul,eval_C,originalE4CenteredField,eval_sub,eval_comp,
    eval_ofNat,WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,ha,hb]
  rw [evenSquared_eval_halfLog p (1 : ZMod p),hL1,
    evenSquared_eval_halfLog p (4 : ZMod p),hL4]
  constructor <;> field_simp [h2,h15] <;> ring

theorem D_zero_right_full (n : ℕ) (x : K) :
    WPFiniteLoop.D n x 0=∑ j∈Finset.Ico 1 (n+1),x^j/(j : K)^2 := by
  unfold WPFiniteLoop.D
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single j]
  · simp only [Nat.sub_self,pow_zero,mul_one]
    congr 1
    ring
  · intro k hk hkj
    have hk' := Finset.mem_Ico.mp hk
    simp only [zero_pow (by omega : j-k≠0),mul_zero,zero_div]
  · intro hjnot
    exact False.elim (hjnot (Finset.mem_Ico.mpr (by
      have := (Finset.mem_Ico.mp hj).1
      omega)))

theorem D_full_zero_right_R (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    WPFiniteLoop.D (p-1) x 0=WPFiniteField.R p x := by
  rw [D_zero_right_full,Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rfl

theorem D_half_square_zero_right (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (x : K) :
    WPFiniteLoop.D ((p-1)/2) (x^2) 0=
      2*(WPFiniteField.R p x+WPFiniteField.R p (-x)) := by
  have h := WPFiniteSignTrace.full_trace_eq_half_cutoff p hp x (0 : K)
  simp only [WPFiniteSignTrace.fullTraceS,WPFiniteLoop.S,zero_pow (by decide : 2≠0),
    neg_zero,D_full_zero_right_R] at h
  linear_combination -h

theorem actual_Hm_ends_finite (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    2*(originalHm p : K[X]).eval (1/4)+(originalHm p : K[X]).eval 4=
      (WPFiniteABSourceTail.epsilon p/15 : K)*
        (4*WPFiniteField.R p (-2)-3*(WPFiniteLoop.D ((p-1)/2) (4/5) 0-
          WPFiniteLoop.D ((p-1)/2) (1/5) 0)) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hR1 : WPFiniteField.R p (1 : K)=0 := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.R_castHom,map_one,map_zero] using h
  have hRm1 : WPFiniteField.R p (-1 : K)=0 := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_neg_one_eq_zero p hp)
    simpa only [←WPFiniteField.R_castHom,map_neg,map_one,map_zero] using h
  have hD1 := D_half_square_zero_right p hp (1 : K)
  rw [one_pow,hR1,hRm1,add_zero,mul_zero] at hD1
  have hD4 := D_half_square_zero_right p hp (2 : K)
  rw [show (2 : K)^2=4 by ring] at hD4
  have hDa := D_half_square_zero_right p hp (1/2 : K)
  rw [show (1/2 : K)^2=1/4 by
    rw [div_pow,one_pow,show (2 : K)^2=4 by ring]] at hDa
  have hRi := WPFiniteField.R_inversion p (2 : K) h2
  have hRmi := WPFiniteField.R_inversion p (-2 : K) (neg_ne_zero.mpr h2)
  have hp2 : (2 : K)^p=2 := WPFiniteField.natCast_pow_char p 2
  have hpm2 : (-2 : K)^p=-2 := by
    rw [(Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow,hp2]
  rw [hp2] at hRi
  rw [hpm2] at hRmi
  have hRa : WPFiniteField.R p (1/2 : K)=
      (1/2 : K)*WPFiniteField.R p 2 := by
    simpa only [one_div] using hRi
  have hRma : WPFiniteField.R p (-(1/2) : K)=
      -(1/2 : K)*WPFiniteField.R p (-2) := by
    simpa only [inv_neg,one_div] using hRmi
  rw [hRa,hRma] at hDa
  have ha : (1+(1/4 : K))/5=1/4 := by field_simp [h4,h5]; ring
  have hb : (1+(4 : K))/5=1 := by field_simp [h5]; ring
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  unfold originalHm
  rw [original_unitPrimitive_eval_full p hp,original_unitPrimitive_eval_full p hp]
  simp only [ha,hb,h4a,mul_one,add_neg_cancel,zero_div,mul_zero,hD1,hD4,hDa]
  field_simp [h2,h15]
  ring

end WPFieldAssembly.SourceClosureUVFiniteEnds
