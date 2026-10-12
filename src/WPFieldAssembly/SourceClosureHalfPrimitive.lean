import WPFinitePrimitiveTransport
import WPFiniteWSource

open scoped BigOperators Polynomial
open Polynomial WPFiniteProductTail

namespace WPFieldAssembly.SourceClosureHalfPrimitive

/- STATEMENT_FIDELITY: UW17a's full D_N finite primitives, N=(p-1)/2,
   with squared coordinate (X+1)/5 and zero origin at X=0. The proof
   uses every 1<=k<=j<=N term, including the diagonal. There is no
   generated finite manifest, actual VS attachment or assigned scalar. -/

variable {K : Type*} [Field K]

noncomputable def halfLogP (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 ((p-1)/2+1), C ((j : K)⁻¹)*X^j

noncomputable def halfDP (p : ℕ) (z : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 ((p-1)/2+1), C ((j : K)⁻¹)*integratedGeometric j z

theorem halfLogP_eval (p : ℕ) (x : K) :
    (halfLogP p).eval x=WPFiniteLoop.L ((p-1)/2) x := by
  simp only [halfLogP,WPFiniteLoop.L,eval_finsetSum,eval_mul,eval_C,
    eval_pow,eval_X,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem halfDP_eval (p : ℕ) (x z : K) :
    (halfDP p z).eval x=WPFiniteLoop.D ((p-1)/2) x z := by
  simp only [halfDP,integratedGeometric,WPFiniteLoop.D,eval_finsetSum,
    eval_mul,eval_C,eval_pow,eval_X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem halfDP_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (z : K) :
    (X-C z)*(halfDP p z).derivative=halfLogP p-C ((halfLogP p).eval z) := by
  simp only [halfDP,derivative_sum,derivative_C_mul,Finset.mul_sum]
  have he : (∑ j ∈ Finset.Ico 1 ((p-1)/2+1),
      (X-C z)*(C ((j : K)⁻¹)*(integratedGeometric j z).derivative))=
      ∑ j ∈ Finset.Ico 1 ((p-1)/2+1), C ((j : K)⁻¹)*(X^j-C (z^j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    rw [mul_left_comm,integratedGeometric_source p j (by omega) z]
  rw [he]
  simp only [halfLogP,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    map_sum,map_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem halfDP_degree (p : ℕ) (z : K) : (halfDP p z).natDegree≤(p-1)/2 := by
  unfold halfDP
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  apply (natDegree_C_mul_le _ _).trans
  unfold integratedGeometric
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)

theorem deltaE_halfLog (p : ℕ) :
    (WPFiniteWSource.deltaE p : K[X])=
      C (1/2 : K)*((halfLogP p).comp (4*X)-halfLogP p) := by
  simp only [WPFiniteWSource.deltaE,halfLogP,sum_comp,mul_comp,
    C_comp,pow_comp,X_comp,mul_pow,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (4 : K[X])=C (4 : K) from rfl,←C_pow]
  simp only [div_eq_mul_inv,mul_inv_rev,map_mul,map_sub,map_one]
  ring

noncomputable def finitePrimitive (p : ℕ) (c : K) : K[X] :=
  C (WPFiniteABSourceTail.epsilon p/15 : K)*
    ((halfDP p (4*((1+c)/5))).comp (4*WPFiniteWSource.squaredCoordinate)-
      (halfDP p ((1+c)/5)).comp WPFiniteWSource.squaredCoordinate-
      C ((halfDP p (4*((1+c)/5))).eval (4/5)-
        (halfDP p ((1+c)/5)).eval (1/5)))

theorem finitePrimitive_origin (p : ℕ) (c : K) :
    (finitePrimitive p c).eval 0=0 := by
  simp only [finitePrimitive,eval_mul,eval_C,eval_sub,eval_comp,
    WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one,eval_ofNat,zero_add,
    one_div,mul_one]
  ring

theorem finitePrimitive_degree (p : ℕ) (c : K) :
    (finitePrimitive p c).natDegree≤(p-1)/2 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree≤1 := by
    unfold WPFiniteWSource.squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hs4 : (4*WPFiniteWSource.squaredCoordinate : K[X]).natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans hs
  have h4 := (natDegree_comp_le (p := halfDP p (4*((1+c)/5)))
    (q := 4*WPFiniteWSource.squaredCoordinate)).trans
      (Nat.mul_le_mul (halfDP_degree p _) hs4)
  have h1 := (natDegree_comp_le (p := halfDP p ((1+c)/5))
    (q := WPFiniteWSource.squaredCoordinate)).trans
      (Nat.mul_le_mul (halfDP_degree p _) hs)
  simp only [Nat.mul_one] at h4 h1
  unfold finitePrimitive
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  exact max_le ((natDegree_sub_le _ _).trans (max_le h4 h1)) (by simp)

end WPFieldAssembly.SourceClosureHalfPrimitive
