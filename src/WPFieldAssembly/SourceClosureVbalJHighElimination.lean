import WPFieldAssembly.SourceClosureVbalFrobeniusNormalization
import WPFiniteJWeightedResidue

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteABSourceTail WPFiniteWSource WPFinitePSource
  WPFiniteJSource WPFiniteJHighCoefficient WPFiniteJNormalization
  WPFiniteFifthSourceContraction WPFiniteProductTail WPFiniteZSupport

namespace WPFieldAssembly.SourceClosureVbalJHighElimination

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

private theorem original_square_phases (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    (WPFiniteZSource.P p u ^ 2 : K[T;T⁻¹]) =
      LaurentPolynomial.C (1 : K)*LaurentPolynomial.T (2*(p : ℤ))*
        ((A p (W p) u)^2).toLaurent+
      LaurentPolynomial.C (2 : K)*LaurentPolynomial.T (p : ℤ)*
        (A p (W p) u*B0 p (W p) u).toLaurent+
      ((B0 p (W p) u)^2+2*A p (W p) u*Cminus p u).toLaurent+
      LaurentPolynomial.C (2 : K)*LaurentPolynomial.T (-(p : ℤ))*
        (B0 p (W p) u*Cminus p u).toLaurent+
      LaurentPolynomial.C (1 : K)*LaurentPolynomial.T (-(2*(p : ℤ)))*
        ((Cminus p u)^2).toLaurent := by
  have ht : (LaurentPolynomial.T (p : ℤ)*LaurentPolynomial.T (-(p : ℤ)) :
      K[T;T⁻¹])=1 := by
    rw [←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero]
  have ht2 : (LaurentPolynomial.T (p : ℤ)*LaurentPolynomial.T (p : ℤ) :
      K[T;T⁻¹])=LaurentPolynomial.T (2*(p : ℤ)) := by
    rw [←LaurentPolynomial.T_add]
    congr 1
    ring
  have htm2 : (LaurentPolynomial.T (-(p : ℤ))*LaurentPolynomial.T (-(p : ℤ)) :
      K[T;T⁻¹])=LaurentPolynomial.T (-(2*(p : ℤ))) := by
    rw [←LaurentPolynomial.T_add]
    congr 1
    ring
  simp only [WPFiniteZSource.P,map_add,map_mul,map_pow,map_ofNat,map_one,one_mul]
  linear_combination (A p (W p) u).toLaurent^2*ht2+
    (Cminus p u).toLaurent^2*htm2+
      2*(A p (W p) u).toLaurent*(Cminus p u).toLaurent*ht

/-- Every strictly higher Z coefficient is used; the original 2p coefficient is excluded. -/
theorem actual_J_strict_high_row (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (j : ℕ) (hj : 0<j) :
    -((A p (W p) u : K[X])^2).coeff j/2-
      (A p (W p) u*B0 p (W p) u : K[X]).coeff (p+j)-
      4*(HJP p : K[X]).coeff (p+j)/45=0 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h45 : (45 : K)≠0 := by
    rw [show (45 : K)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have hA := A_degree (K:=K) p hp u
  have hB := (WPFiniteLVSharp.original_phase_degrees (K:=K) p hp u).1
  have hC := (WPFiniteLVSharp.original_phase_degrees (K:=K) p hp u).2
  have hH := HJP_natDegree_le (K:=K) p hp
  have hBB : ((B0 p (W p) u : K[X])^2).natDegree≤2*p-2 :=
    (natDegree_pow_le_of_le 2 hB).trans (by omega)
  have hCC : ((Cminus p u : K[X])^2).natDegree≤2*p-2 :=
    (natDegree_pow_le_of_le 2 hC).trans (by omega)
  have hBC : (B0 p (W p) u*Cminus p u : K[X]).natDegree≤2*p-2 :=
    natDegree_mul_le.trans ((Nat.add_le_add hB hC).trans (by omega))
  have hAC : (A p (W p) u*Cminus p u : K[X]).natDegree≤2*p-2 :=
    natDegree_mul_le.trans ((Nat.add_le_add hA hC).trans (by omega))
  have hrow : ((B0 p (W p) u : K[X])^2+2*A p (W p) u*Cminus p u).natDegree≤
      2*p-2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le hBB
    rw [mul_assoc]
    change (Polynomial.C (2 : K)*(A p (W p) u*Cminus p u)).natDegree≤_
    exact (natDegree_C_mul_le _ _).trans hAC
  have hout (Q : K[X]) (hQ : Q.natDegree≤2*p-2) (m : ℤ) (hm : 2*p≤m) :
      Q.toLaurent.coeff m=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside Q m (Or.inr (by omega))
  have hsq := congrArg (fun F : K[T;T⁻¹] => F.coeff (2*(p : ℤ)+j))
    (original_square_phases (K:=K) p u)
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    WPFiniteJCarrier.shifted_coeff,one_mul] at hsq
  rw [show 2*(p : ℤ)+j-2*p=(j : ℤ) by ring,
    show 2*(p : ℤ)+j-p=((p+j : ℕ) : ℤ) by push_cast; ring,
    show 2*(p : ℤ)+j- -p=3*p+j by ring,
    show 2*(p : ℤ)+j- -(2*p)=4*p+j by ring,
    WPFiniteJCarrier.toLaurent_coeff_nat,WPFiniteJCarrier.toLaurent_coeff_nat,
    hout _ hrow _ (by omega),hout _ hBC _ (by omega),
    hout _ hCC _ (by omega)] at hsq
  have hJ := WPFiniteJCarrier.GJ_coefficient (K:=K) p (2*(p : ℤ)+j)
  have hHp : (HJP p : K[X]).toLaurent.coeff (2*(p : ℤ)+j)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hHm : (HJP p : K[X]).toLaurent.coeff (-(2*(p : ℤ)+j))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hH3p : (HJP p : K[X]).toLaurent.coeff (3*(p : ℤ)+j)=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hH3m : (HJP p : K[X]).toLaurent.coeff (-(3*(p : ℤ)+j))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hHnm : (HJP p : K[X]).toLaurent.coeff (-((p+j : ℕ) : ℤ))=0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  rw [show 2*(p : ℤ)+j-p=((p+j : ℕ) : ℤ) by push_cast; ring,
    show 2*(p : ℤ)+j+p=3*p+j by ring,hHp,hHm,hH3p,hH3m,hHnm,
    WPFiniteJCarrier.toLaurent_coeff_nat] at hJ
  have hz := (actual_finite_whole_support (K:=K) p hp u hu).1
    (2*(p : ℤ)+j) (by omega)
  rw [WPFiniteZSource.Z,neg_mul,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    AddMonoidAlgebra.coeff_neg,Finsupp.neg_apply] at hz
  have hc := WPFiniteJCarrier.shifted_coeff (1/2 : K) 0 (2*(p : ℤ)+j)
    (WPFiniteZSource.P p u^2 : K[T;T⁻¹])
  simp only [LaurentPolynomial.T_zero,mul_one,sub_zero] at hc
  rw [hc,hsq,hJ] at hz
  field_simp [h2,h45] at hz ⊢
  linear_combination hz

/-- NC116 removes the full third J band while keeping its derivative-invisible p slot. -/
theorem actual_J_strict_high_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (strictHigh p : K[X])=
      -(Polynomial.C (45/8 : K)*((A p (W p) u)^2-Polynomial.C (uSlot p u)^2))-
        Polynomial.C (45/4 : K)*strictTail p (A p (W p) u*B0 p (W p) u) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h8 : (8 : K)≠0 := by rw [show (8 : K)=2^3 by ring]; exact pow_ne_zero _ h2
  have h45 : (45 : K)≠0 := by
    rw [show (45 : K)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have hA := A_degree (K:=K) p hp u
  have hAsq : ((A p (W p) u : K[X])^2).natDegree<p := by
    have hd := natDegree_pow_le_of_le 2 hA
    omega
  have hAzero : (A p (W p) u : K[X]).coeff 0=uSlot p u := by
    rw [A,coeff_sub,coeff_C_zero,coeff_C_mul,W_origin,mul_zero,sub_zero]
  have hAsq0 : ((A p (W p) u : K[X])^2).coeff 0=uSlot p u^2 := by
    rw [coeff_zero_eq_eval_zero,eval_pow,←coeff_zero_eq_eval_zero,hAzero]
  ext j
  rw [strictHigh_coeff p hp j,coeff_sub,coeff_neg,coeff_C_mul,
    coeff_sub,←Polynomial.C_pow,coeff_C,coeff_C_mul,strictTail_coeff p (by omega)]
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true,hAsq0,sub_self,mul_zero,neg_zero]
  · rw [if_neg hj0,if_neg hj0,if_neg hj0,sub_zero]
    by_cases hjp : j<p
    · rw [if_pos hjp,if_pos hjp]
      have he := actual_J_strict_high_row (K:=K) p hp u hu j (by omega)
      linear_combination (norm := (field_simp [h2,h4,h8,h45]; ring)) -(45/4 : K)*he
    · rw [if_neg hjp,if_neg hjp,coeff_eq_zero_of_natDegree_lt (by omega :
        ((A p (W p) u : K[X])^2).natDegree<j)]
      ring

/-- Both strict high endpoints become the genuine fixed unit primitives, including diagonals. -/
theorem actual_J_strict_high_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) (z : K) :
    (strictHigh p : K[X]).eval z=
      -45*((A p (W p) u).eval z^2-uSlot p u^2)/8+
        3*(JdifferenceP p (W p)).eval z/epsilon p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h4 : (4 : K)≠0 := by rw [show (4 : K)=2^2 by ring]; exact pow_ne_zero _ h2
  have h8 : (8 : K)≠0 := by rw [show (8 : K)=2^3 by ring]; exact pow_ne_zero _ h2
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  rw [actual_J_strict_high_polynomial p hp u hu,
    actual_AB0_tail p hp (W p) (W_degree p hp) (W_origin p) u]
  simp only [eval_sub,eval_neg,eval_mul,eval_C,eval_pow]
  field_simp [h4,h8,h15,heps]
  ring

private theorem deltaE_original_half_row (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (z : K) :
    (deltaE p : K[X]).eval z=
      (WPFiniteLoop.L ((p-1)/2) (4*z)-WPFiniteLoop.L ((p-1)/2) z)/2 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  simp only [deltaE,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,WPFiniteLoop.L]
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp : j∈Finset.Ico 1 p := by
    have := Finset.mem_Ico.mp hj
    exact Finset.mem_Ico.mpr (by omega)
  have hj0 : (j : K)≠0 := WPFiniteField.denominator_ne_zero p j hjp
  rw [mul_pow]
  field_simp [h2,hj0]

/-- The two original high-phase ends follow from the complete finite logarithm row. -/
theorem actual_J_high_phase_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (A p (W p) u : K[X]).eval (1/4)=4*WPFiniteNC122.q p/15-r p/5 ∧
      (A p (W p) u : K[X]).eval 4=-2*(4*WPFiniteNC122.q p/15-r p/5) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have hs1 : (squaredCoordinate : K[X]).eval 4=1 := by
    simp only [squaredCoordinate,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h5]
    ring
  have hsa : (squaredCoordinate : K[X]).eval (1/4)=1/4 := by
    simp only [squaredCoordinate,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h4,h5]
    ring
  have he := WPFiniteLoop.L_rational_ends (K:=K) p hp
  have hd1 := deltaE_original_half_row (K:=K) p hp (1 : K)
  have hda := deltaE_original_half_row (K:=K) p hp (1/4 : K)
  rw [mul_one,he.2.1,he.1] at hd1
  rw [mul_one_div_cancel h4,he.1,he.2.2] at hda
  rw [A_literal_even_difference p hp u hu]
  simp only [eval_mul,eval_C,eval_add,eval_comp,hsa,hs1,hda,hd1]
  dsimp only [WPFiniteNC122.q,r]
  constructor <;> field_simp [h2,h5,h15] <;> ring

/-- The normalized J trace retains its actual phase ends before their arithmetic evaluation. -/
theorem actual_J_full_fifth_functional (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (JfullFunctional p : K)=11*U_J p u/15-22*V_J p u/15-
      2*(A p (W p) u).eval (1/4)^2-(A p (W p) u).eval 4^2+
      3*uSlot p u^2+8*(2*(JdifferenceP p (W p)).eval (1/4)+
        (JdifferenceP p (W p)).eval 4)/(15*epsilon p) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : K)≠0 := by rw [show (8 : K)=2^3 by ring]; exact pow_ne_zero _ h2
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h45 : (45 : K)≠0 := by
    rw [show (45 : K)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  unfold JfullFunctional JendpointFunctional
  rw [actual_J_origin_split p hp u hu,actual_J_high_coefficient p hp u hu,
    actual_J_strict_high_value p hp u hu (1/4),actual_J_strict_high_value p hp u hu 4]
  field_simp [h2,h3,h5,h8,h15,h45,heps]
  ring

/-- JT6c uses the actual endpoint and full cubic alphabet, with no unassigned HJP coefficient. -/
theorem actual_J_closed_fifth_functional (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (JfullFunctional p : K)=11*U_J p u/15-22*V_J p u/15-
      6*(4*WPFiniteNC122.q p/15-r p/5)^2+3*uSlot p u^2+
      8*(2*(JdifferenceP p (W p)).eval (1/4)+
        (JdifferenceP p (W p)).eval 4)/(15*epsilon p) := by
  rw [actual_J_full_fifth_functional p hp u hu,
    (actual_J_high_phase_ends p hp u hu).1,(actual_J_high_phase_ends p hp u hu).2]
  ring

end WPFieldAssembly.SourceClosureVbalJHighElimination
