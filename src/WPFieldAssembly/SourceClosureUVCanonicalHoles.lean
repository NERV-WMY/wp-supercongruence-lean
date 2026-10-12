import WPFieldAssembly.ActualUVSourceIdentification

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFiniteJCarrier WPFieldAssembly.SourceClosureUniversalLog
  WPFieldAssembly.ActualUVSourceIdentification

namespace WPFieldAssembly.SourceClosureUVCanonicalHoles

/- The holes are properties of the specified UW17 Ucan itself. They are
   not imposed by projecting an unrelated primitive after differentiation. -/

variable {K : Type*} [Field K]

theorem constant_mul_coeff (a : K) (F : K[T;T⁻¹]) (j : ℤ) :
    (LaurentPolynomial.C a*F).coeff j=a*F.coeff j := by
  simpa only [T_zero,mul_one,sub_zero] using shifted_coeff a 0 j F

theorem shift_mul_coeff (n j : ℤ) (F : K[T;T⁻¹]) :
    (T n*F).coeff j=F.coeff (j-n) := by
  simpa only [map_one,one_mul] using shifted_coeff (1 : K) n j F

theorem zero_origin_low_coeff (p : ℕ) (P : K[X]) (hdeg : P.natDegree<p)
    (h0 : P.eval 0=0) (j : ℤ)
    (hj : j=0 ∨ j≤-(p : ℤ) ∨ (p : ℤ)≤j) (_hp : 0<p) :
    P.toLaurent.coeff j=0 := by
  rcases hj with hj | hj | hj
  · subst j
    change P.toLaurent.coeff ((0 : ℕ) : ℤ)=0
    rw [toLaurent_coeff_nat,coeff_zero_eq_eval_zero]
    exact h0
  · exact toLaurent_coeff_outside P j (Or.inl (by omega))
  · exact toLaurent_coeff_outside P j (Or.inr (by omega))

theorem originalHsym_hole_band (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (j : ℤ) (hj : j=0 ∨ j≤-(p : ℤ) ∨ (p : ℤ)≤j) :
    (originalHsym p : K[T;T⁻¹]).coeff j=0 := by
  have hdeg := originalH_degree (K:=K) p hp
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hjneg : -j=0 ∨ -j≤-(p : ℤ) ∨ (p : ℤ)≤-j := by
    rcases hj with hj | hj | hj <;> omega
  have hx0 : (originalHx p : K[X]).eval 0=0 :=
    WPFiniteProductTail.unitPrimitiveP_zero p _ _
  have ha0 : (originalHa p : K[X]).eval 0=0 :=
    WPFiniteProductTail.unitPrimitiveP_zero p _ _
  have hb0 : (originalHb p : K[X]).eval 0=0 :=
    WPFiniteProductTail.unitPrimitiveP_zero p _ _
  have hm0 : (originalHm p : K[X]).eval 0=0 :=
    WPFiniteProductTail.unitPrimitiveP_zero p _ _
  have hx := zero_origin_low_coeff p (originalHx p) (by omega) hx0 j hj hp0
  have ha := zero_origin_low_coeff p (originalHa p) (by omega) ha0 j hj hp0
  have hb := zero_origin_low_coeff p (originalHb p) (by omega) hb0 j hj hp0
  have hm := zero_origin_low_coeff p (originalHm p) (by omega) hm0 j hj hp0
  have hxi := zero_origin_low_coeff p (originalHx p) (by omega) hx0 (-j) hjneg hp0
  have hai := zero_origin_low_coeff p (originalHa p) (by omega) ha0 (-j) hjneg hp0
  have hbi := zero_origin_low_coeff p (originalHb p) (by omega) hb0 (-j) hjneg hp0
  have hmi := zero_origin_low_coeff p (originalHm p) (by omega) hm0 (-j) hjneg hp0
  simp only [originalHsym,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply,Finsupp.sub_apply,constant_mul_coeff,invert_apply,
    hx,ha,hb,hm,hxi,hai,hbi,hmi,mul_zero,add_zero,sub_zero]

theorem originalK0Hsym_holes (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (j : ℤ) (hj : j=0 ∨ j=(p : ℤ) ∨ j=-(p : ℤ)) :
    (originalK0 p*originalHsym p : K[T;T⁻¹]).coeff j=0 := by
  have h (k : ℤ) (hk : k=0 ∨ k≤-(p : ℤ) ∨ (p : ℤ)≤k) :
      (originalHsym p : K[T;T⁻¹]).coeff k=0 := originalHsym_hole_band p hp k hk
  have h0 := h j (by rcases hj with hj | hj | hj <;> omega)
  have hplus := h (j+(p : ℤ)) (by rcases hj with hj | hj | hj <;> omega)
  have hminus := h (j-(p : ℤ)) (by rcases hj with hj | hj | hj <;> omega)
  simp only [originalK0,sub_mul,add_mul,mul_assoc,AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_add,Finsupp.sub_apply,Finsupp.add_apply,
    constant_mul_coeff,shift_mul_coeff,sub_neg_eq_add,h0,hplus,hminus,
    mul_zero,add_zero,sub_zero]

theorem scaledLog_coeff_outside (p : ℕ) (c : K) (j : ℤ)
    (hj : j≤0 ∨ (p : ℤ)≤j) : (scaledLog p c).coeff j=0 := by
  classical
  rw [scaledLog_full]
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  rw [←single_eq_C_mul_T,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,if_neg]
  rcases Finset.mem_Ico.mp hn with ⟨hn1,hnp⟩
  rcases hj with hj | hj <;> omega

theorem scaledDilog_coeff_outside (p : ℕ) (c : K) (j : ℤ)
    (hj : j≤0 ∨ (p : ℤ)≤j) : (scaledDilog p c).coeff j=0 := by
  classical
  rw [scaledDilog_full]
  simp only [AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  rw [←single_eq_C_mul_T,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,if_neg]
  rcases Finset.mem_Ico.mp hn with ⟨hn1,hnp⟩
  rcases hj with hj | hj <;> omega

theorem shifted_low_holes (p : ℕ) (F : K[T;T⁻¹]) (c : K)
    (hF : ∀ j : ℤ, j≤0 ∨ (p : ℤ)≤j → F.coeff j=0)
    (j : ℤ) (hj : j=0 ∨ j=(p : ℤ) ∨ j=-(p : ℤ)) :
    ((T (-(p : ℤ))-LaurentPolynomial.C c)*F).coeff j=0 := by
  have h0 := hF j (by rcases hj with hj | hj | hj <;> omega)
  have hplus := hF (j+(p : ℤ)) (by rcases hj with hj | hj | hj <;> omega)
  simp only [sub_mul,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    shift_mul_coeff,constant_mul_coeff,sub_neg_eq_add,h0,hplus,mul_zero,sub_zero]

theorem originalJab_holes (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j=0 ∨ j=(p : ℤ) ∨ j=-(p : ℤ)) :
    (originalJa p+originalJb p : K[T;T⁻¹]).coeff j=0 := by
  have ha := shifted_low_holes p (scaledLog p (4 : K))
    (1/4 : K) (scaledLog_coeff_outside p 4) j hj
  have hb := shifted_low_holes p (scaledLog p (1/4 : K))
    (4 : K) (scaledLog_coeff_outside p (1/4)) j hj
  simp only [originalJa,originalJb,mul_assoc,AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply,constant_mul_coeff,ha,hb,mul_zero,add_zero]

theorem originalJ2log_holes (p : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j=0 ∨ j=(p : ℤ) ∨ j=-(p : ℤ)) :
    (originalJ2log p : K[T;T⁻¹]).coeff j=0 := by
  have ha := shifted_low_holes p (scaledDilog p (4 : K))
    (1/4 : K) (scaledDilog_coeff_outside p 4) j hj
  have hb := shifted_low_holes p (scaledDilog p (1/4 : K))
    (4 : K) (scaledDilog_coeff_outside p (1/4)) j hj
  simp only [originalJ2log,constant_mul_coeff,AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply,ha,hb,mul_zero,sub_zero]

/-- The complete original Ucan already has the three specified holes. -/
theorem originalUcan_holes (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) (u : K) :
    (originalUcan p u).coeff 0=0 ∧ (originalUcan p u).coeff (p : ℤ)=0 ∧
      (originalUcan p u).coeff (-(p : ℤ))=0 := by
  have h (j : ℤ) (hj : j=0 ∨ j=(p : ℤ) ∨ j=-(p : ℤ)) :
      (originalUcan p u : K[T;T⁻¹]).coeff j=0 := by
    simp only [originalUcan,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
      constant_mul_coeff,originalK0Hsym_holes p hp j hj,
      originalJab_holes p j hj,originalJ2log_holes p j hj,mul_zero,sub_zero]
  exact ⟨h 0 (Or.inl rfl),h p (Or.inr (Or.inl rfl)),h (-p) (Or.inr (Or.inr rfl))⟩

theorem originalCan_Ucan (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) (u : K) :
    originalCan p (originalUcan p u)=originalUcan p u := by
  have h := originalUcan_holes p hp u
  simp only [originalCan,h.1,h.2.1,h.2.2,map_zero,zero_mul,sub_zero]

end WPFieldAssembly.SourceClosureUVCanonicalHoles
