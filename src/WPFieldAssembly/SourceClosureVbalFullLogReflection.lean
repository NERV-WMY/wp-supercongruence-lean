import WPFieldAssembly.SourceClosureVbalFullLogTail
import WPFieldAssembly.SourceClosureVbalFrobeniusNormalization
import WPFiniteKSource

open scoped BigOperators Polynomial
open Polynomial WPFiniteAffineLog WPFiniteProductTail WPFiniteKSource
  WPFieldAssembly.SourceClosureVbalFullLogTail
  WPFieldAssembly.SourceClosureVbalFrobeniusNormalization

namespace WPFieldAssembly.SourceClosureVbalFullLogReflection

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

private theorem unit_degree_primitive_unique (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hdeg : Q.natDegree<p) (hder : Q.derivative=0)
    (hz : Q.eval 0=0) : Q=0 := by
  ext j
  by_cases hj : j=0
  · subst j
    simpa only [coeff_zero_eq_eval_zero,eval_zero] using hz
  by_cases hjp : p≤j
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hjp)
  have hjs : j∈Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have he : Q.coeff j*(j : K)=0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (j-1)) hder
    simpa only [coeff_derivative,←Nat.cast_add_one,
      Nat.sub_add_cancel (by omega : 1≤j),coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p j hjs)

/-- Unit integration identifies the literal full D polynomial before evaluating it. -/
theorem actual_full_D_one_right (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (t : K) :
    WPFiniteLoop.D (p-1) t 1=WPFiniteField.R p (1-t) := by
  have hell1 : WPFiniteField.ell p (1 : K)=0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.ell_castHom,map_one,map_zero] using he
  have hR1 : WPFiniteField.R p (1 : K)=0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.R_castHom,map_one,map_zero] using he
  have hLP : (LP p : K[X]).natDegree<p := by have := LP_natDegree_le (K:=K) p; omega
  have h0 : (LP p : K[X]).coeff 0=0 := by
    have he := LP_scaled_coeff (K:=K) p (1 : K) 0
    simpa only [map_one,one_mul,comp_X,if_neg (by omega : ¬(1≤0 ∧ 0<p))] using he
  let U : K[X] := unitPrimitiveP p (LP p) 1
  let V : K[X] := (RP p).comp (1-X)
  have hU : (X-1)*U.derivative=LP p := by
    have he := unitPrimitiveP_source (K:=K) p (LP p) hLP h0 (1 : K)
    rw [LP_eval_eq,hell1,map_zero,sub_zero,map_one] at he
    exact he
  have hV : (X-1)*V.derivative=LP p := by
    have he := RP_comp_derivative (K:=K) p (1-X : K[X])
    rw [derivative_sub,derivative_one,derivative_X,zero_sub,LP_reflection p hp] at he
    dsimp only [V]
    linear_combination -he
  have hX : (X-1 : K[X])≠0 := by
    simpa only [map_one] using (sub_ne_zero.mpr (X_ne_C (1 : K)))
  have hder : (U-V).derivative=0 := by
    apply mul_left_cancel₀ hX
    rw [mul_zero,derivative_sub,mul_sub,hU,hV,sub_self]
  have hUdeg : U.natDegree≤p-1 := unitPrimitiveP_degree p (LP p) 1
  have hVdeg : V.natDegree≤p-1 := by
    have hlin : (1-X : K[X]).natDegree≤1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hd := natDegree_comp_le (p:=(RP p : K[X])) (q:=(1-X : K[X]))
    dsimp only [V]
    exact hd.trans ((Nat.mul_le_mul (RP_natDegree_le (K:=K) p) hlin).trans (by simp))
  have hz : (U-V).eval 0=0 := by
    dsimp only [U,V]
    rw [eval_sub,unitPrimitiveP_zero,eval_comp,eval_sub,eval_one,eval_X,sub_zero,
      RP_eval,hR1,sub_zero]
  have he := unit_degree_primitive_unique p (U-V)
    ((natDegree_sub_le _ _).trans_lt ((max_le hUdeg hVdeg).trans_lt (by omega))) hder hz
  have hu : U=V := sub_eq_zero.mp he
  have hv := congrArg (fun P : K[X] => P.eval t) hu
  dsimp only [U,V] at hv
  rw [unitPrimitiveP_eval,eval_comp,eval_sub,eval_one,eval_X,RP_eval] at hv
  have hp1 : 1≤p := (Fact.out : p.Prime).one_le
  have hD : unitPrimitive p (LP p : K[X]) 1 t=WPFiniteLoop.D (p-1) t 1 := by
    unfold unitPrimitive WPFiniteLoop.D
    rw [Nat.sub_add_cancel hp1]
    apply Finset.sum_congr rfl
    intro i hi
    have hc : (LP p : K[X]).coeff i=1/(i : K) := by
      have hi' := LP_scaled_coeff (K:=K) p (1 : K) i
      simpa only [map_one,one_mul,comp_X,if_pos (Finset.mem_Ico.mp hi),one_pow] using hi'
    rw [hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [one_pow,mul_one,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hD] at hv
  exact hv

/-- The full mixed low shuffle includes both of its dilogarithm diagonals. -/
theorem actual_full_D_one_left (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (t : K) :
    WPFiniteLoop.D (p-1) 1 t=2*WPFiniteField.R p t-2*WPFiniteField.R p (1-t) := by
  have he := full_D_one_left (K:=K) p hp t
  rw [actual_full_D_one_right p hp t] at he
  linear_combination he

/-- The p-th product row is the original diagonal omitted by the strict tail. -/
theorem full_log_product_boundary (p : ℕ) [Fact p.Prime] [CharP K p]
    (c d : K) (hd : d≠0) :
    (((LP p : K[X]).comp (Polynomial.C c*X))*
      (LP p).comp (Polynomial.C d*X)).coeff p=-d^p*WPFiniteField.R p (c/d) := by
  have hdeg : ((LP p : K[X]).comp (Polynomial.C c*X)).natDegree<p := by
    have hp : 0<p := (Fact.out : p.Prime).pos
    apply lt_of_le_of_lt _ (Nat.sub_lt hp (by omega : 0<1))
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [LP_scaled_coeff,if_neg (by omega)]
  have hz : ((LP p : K[X]).comp (Polynomial.C c*X)).coeff 0=0 := by
    rw [LP_scaled_coeff,if_neg (by omega)]
  rw [scaled_log_product_boundary p _ hdeg hz d hd,
    (scaled_log_unit_primitive (K:=K) p c d 0).2]

/-- Both full weight-two reflections at16 retain the same literal logarithm square. -/
theorem actual_full_log_sixteen_reflections (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    WPFiniteField.R p (1-(16 : K))=
      (16*WPFiniteField.R p (16 : K)+WPFiniteField.ell p (16 : K)^2/2)/15 ∧
    WPFiniteField.R p (1-(16 : K)⁻¹)=
      -(WPFiniteField.R p (16 : K)+WPFiniteField.ell p (16 : K)^2/2)/240 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h16 : (16 : K)≠0 := by rw [show (16 : K)=2^4 by ring]; exact pow_ne_zero _ h2
  have h240 : (240 : K)≠0 := by
    rw [show (240 : K)=16*15 by ring]
    exact mul_ne_zero h16 h15
  have h16p : (16 : K)^p=16 := WPFiniteField.natCast_pow_char p 16
  have he := WPFiniteField.R_weight_two_reflection (K:=K) p (by omega) (16 : K)
  have hei := WPFiniteField.R_weight_two_reflection (K:=K) p (by omega) (16 : K)⁻¹
  rw [sub_pow_char,one_pow,h16p] at he
  rw [sub_pow_char,one_pow,inv_pow,h16p,
    WPFiniteField.R_inversion p (16 : K) h16,h16p,
    WPFiniteField.ell_inversion p (16 : K) h16,h16p] at hei
  constructor
  · linear_combination (norm := (field_simp [h2,h15]; ring)) -he/15
  · linear_combination (norm := (field_simp [h2,h15,h16,h240]; ring)) (16/15 : K)*hei

private theorem full_R_origin (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPFiniteField.R p (0 : K)=0 := by
  unfold WPFiniteField.R
  apply Finset.sum_eq_zero
  intro j hj
  have hjpos := (Finset.mem_Ico.mp hj).1
  simp only [zero_pow (by omega : j≠0),zero_div]

/-- The four individual self-square projections use the same original ends. -/
theorem actual_full_log_self_square_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))^2)).eval (1/4)=0 ∧
    (strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))^2)).eval 4=
      (8*WPFiniteField.R p (16 : K)+4*WPFiniteField.ell p (16 : K)^2)/15 ∧
    (strictTail p (((LP p : K[X]).comp (Polynomial.C (1/4)*X))^2)).eval (1/4)=
      -(32*WPFiniteField.R p (16 : K)+WPFiniteField.ell p (16 : K)^2)/960 ∧
    (strictTail p (((LP p : K[X]).comp (Polynomial.C (1/4)*X))^2)).eval 4=0 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h16 : (16 : K)≠0 := by rw [show (16 : K)=2^4 by ring]; exact pow_ne_zero _ h2
  have h240 : (240 : K)≠0 := by rw [show (240 : K)=16*15 by ring]; exact mul_ne_zero h16 h15
  have h960 : (960 : K)≠0 := by rw [show (960 : K)=4*240 by ring]; exact mul_ne_zero h4 h240
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have h16p : (16 : K)^p=16 := WPFiniteField.natCast_pow_char p 16
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have ha4 : (1/4 : K)*4=1 := by field_simp [h4]
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  have haa : (1/4 : K)*(1/4)=(16 : K)⁻¹ := by field_simp [h4,h16]; ring
  have h44 : (4 : K)*4=16 := by ring
  have hR1 : WPFiniteField.R p (1 : K)=0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.R_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.R_castHom,map_one,map_zero] using he
  have hD1 : WPFiniteLoop.D (p-1) (1 : K) 1=0 := by
    rw [actual_full_D_one_right p hp 1,sub_self,full_R_origin]
  have hDa := actual_full_D_one_left (K:=K) p hp (16 : K)⁻¹
  have hDb := actual_full_D_one_left (K:=K) p hp (16 : K)
  rw [WPFiniteField.R_inversion p (16 : K) h16,h16p,
    (actual_full_log_sixteen_reflections p hp).2] at hDa
  rw [(actual_full_log_sixteen_reflections p hp).1] at hDb
  refine ⟨?_,?_,?_,?_⟩
  · rw [full_log_square_strict_tail p 4 (1/4) h4,h4p,h4a,hD1,hR1]
    ring
  · rw [full_log_square_strict_tail p 4 4 h4,h4p,h44,hR1]
    linear_combination (norm := (field_simp [h2,h15]; ring)) -4*hDb
  · rw [full_log_square_strict_tail p (1/4) (1/4) (one_div_ne_zero h4),hap,haa,hR1]
    linear_combination (norm := (field_simp [h2,h4,h15,h16,h240,h960]; ring)) -hDa/4
  · rw [full_log_square_strict_tail p (1/4) 4 (one_div_ne_zero h4),hap,ha4,hD1,hR1]
    ring

/-- The mixed projections retain their reflected proper source and separate p row. -/
theorem actual_full_log_mixed_product_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))*
      (LP p).comp (Polynomial.C (1/4)*X))).eval (1/4)=
      -(2*WPFiniteField.R p (16 : K)+WPFiniteField.ell p (16 : K)^2)/120 ∧
    (strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))*
      (LP p).comp (Polynomial.C (1/4)*X))).eval 4=
      (32*WPFiniteField.R p (16 : K)+WPFiniteField.ell p (16 : K)^2)/120 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h16 : (16 : K)≠0 := by rw [show (16 : K)=2^4 by ring]; exact pow_ne_zero _ h2
  have h120 : (120 : K)≠0 := by
    rw [show (120 : K)=2^3*15 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) h15
  have h240 : (240 : K)≠0 := by rw [show (240 : K)=16*15 by ring]; exact mul_ne_zero h16 h15
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have h16p : (16 : K)^p=16 := WPFiniteField.natCast_pow_char p 16
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have h4a : (4 : K)*(1/4)=1 := by field_simp [h4]
  have h44 : (4 : K)*4=16 := by ring
  have hda : (4 : K)/(1/4)=16 := by field_simp [h4]; ring
  constructor
  · rw [full_log_product_strict_tail p 4 (1/4) (1/4) (one_div_ne_zero h4),hap,h4a,hda,
      actual_full_D_one_right p hp 16,(actual_full_log_sixteen_reflections p hp).1]
    field_simp [h2,h4,h15,h120]
    ring
  · rw [full_log_product_strict_tail p 4 (1/4) 4 (one_div_ne_zero h4),hap,h44,hda,
      WPFiniteDReciprocity.D_reciprocity p (16 : K) 16 h16,h16p,div_self h16,
      actual_full_D_one_right p hp (16 : K)⁻¹,
      (actual_full_log_sixteen_reflections p hp).2]
    field_simp [h2,h4,h15,h16,h120,h240]
    ring

/-- The original three-window coefficients collect the same individual strict ends. -/
theorem actual_full_log_weighted_tail_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    -13*((strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))^2)).eval (1/4)+
      2*(strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))^2)).eval 4)/600+
    64*((strictTail p (((LP p : K[X]).comp (Polynomial.C (1/4)*X))^2)).eval (1/4)+
      2*(strictTail p (((LP p : K[X]).comp (Polynomial.C (1/4)*X))^2)).eval 4)/75+
    22*((strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))*
      (LP p).comp (Polynomial.C (1/4)*X))).eval (1/4)+
      2*(strictTail p (((LP p : K[X]).comp (Polynomial.C 4*X))*
      (LP p).comp (Polynomial.C (1/4)*X))).eval 4)/75=
      WPFiniteField.R p (16 : K)/10-WPFiniteField.ell p (16 : K)^2/100 := by
  have hs := actual_full_log_self_square_ends (K:=K) p hp
  have hm := actual_full_log_mixed_product_ends (K:=K) p hp
  rw [hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,hm.1,hm.2]
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := by rw [show (10 : K)=2*5 by ring]; exact mul_ne_zero h2 h5
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h75 : (75 : K)≠0 := by
    rw [show (75 : K)=3*5^2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  have h100 : (100 : K)≠0 := by
    rw [show (100 : K)=2^2*5^2 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5)
  have h120 : (120 : K)≠0 := by
    rw [show (120 : K)=2^3*3*5 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) h5
  have h600 : (600 : K)≠0 := by
    rw [show (600 : K)=2^3*3*5^2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) (pow_ne_zero _ h5)
  have h960 : (960 : K)≠0 := by
    rw [show (960 : K)=2^6*3*5 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) h5
  field_simp [h10,h15,h75,h100,h120,h600,h960]
  ring

end WPFieldAssembly.SourceClosureVbalFullLogReflection
