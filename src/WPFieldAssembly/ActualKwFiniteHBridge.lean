import WPFieldAssembly.ActualKwPhaseTrace
import WPFiniteWSource
import Mathlib.Algebra.Polynomial.Derivative

open scoped Polynomial BigOperators
open Polynomial

namespace WPFieldAssembly.ActualKwFiniteHBridge

open ActualKwWeightedTrace

set_option maxHeartbeats 2400000

/- The actual moving even source is deltaE composed with (X+1)/5.
Its entire degree-N coefficient range is retained. The primitive is identified
with the four original finite D_N values by its cleared derivative, degree <p
and value at the origin; neither y=0 nor v=y is excluded. -/

section Primitive
variable {K : Type*} [Field K]

noncomputable def rowPrimitive (n : ℕ) (y : K) : K[X] :=
  ∑ k∈Finset.Ico 1 (n+1), C (y^(n-k)/(k : K))*X^k

noncomputable def sourcePolynomial (N : ℕ) (e : ℕ → K) : K[X] :=
  ∑ n∈Finset.range (N+1), C (e n)*X^n

noncomputable def HPrimitive (N : ℕ) (e : ℕ → K) (y : K) : K[X] :=
  ∑ n∈Finset.range (N+1), C (e n)*rowPrimitive n y

theorem rowPrimitive_eval (n : ℕ) (y v : K) :
    (rowPrimitive n y).eval v=triangle n y v := by
  simp only [rowPrimitive,triangle,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem rowPrimitive_eval_zero (n : ℕ) (y : K) : (rowPrimitive n y).eval 0=0 := by
  rw [rowPrimitive,eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : k≠0 := by have := (Finset.mem_Ico.mp hk).1; omega
  simp only [eval_mul,eval_C,eval_pow,eval_X,zero_pow hk0,mul_zero]

theorem rowPrimitive_degree (n : ℕ) (y : K) : (rowPrimitive n y).natDegree≤n := by
  unfold rowPrimitive
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk1 := (Finset.mem_Ico.mp hk).2
  exact (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X_pow]; omega)

theorem sourcePolynomial_eq (N : ℕ) (P : K[X]) (hP : P.natDegree≤N) :
    sourcePolynomial N (fun n => P.coeff n)=P := by
  have hsub : P.support ⊆ Finset.range (N+1) := by
    intro n hn
    have hd := le_natDegree_of_ne_zero (mem_support_iff.mp hn)
    exact Finset.mem_range.mpr (by omega)
  have hs := sum_C_mul_X_pow_eq P
  rw [Polynomial.sum_def] at hs
  unfold sourcePolynomial
  calc
    _ = ∑ n∈P.support, C (P.coeff n)*X^n := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnot
      have hcn : P.coeff n=0 := by
        by_contra hc
        exact hnot (mem_support_iff.mpr hc)
      rw [hcn,map_zero,zero_mul]
    _ = P := hs

theorem HPrimitive_eval (N : ℕ) (e : ℕ → K) (y v : K) :
    (HPrimitive N e y).eval v=finiteH N e y v := by
  simp only [HPrimitive,finiteH,eval_finsetSum,eval_mul,eval_C,rowPrimitive_eval]

theorem HPrimitive_eval_zero (N : ℕ) (e : ℕ → K) (y : K) :
    (HPrimitive N e y).eval 0=0 := by
  simp only [HPrimitive,eval_finsetSum,eval_mul,eval_C,rowPrimitive_eval_zero,mul_zero,Finset.sum_const_zero]

theorem HPrimitive_degree (N : ℕ) (e : ℕ → K) (y : K) :
    (HPrimitive N e y).natDegree≤N := by
  unfold HPrimitive
  apply natDegree_sum_le_of_forall_le
  intro n hn
  have hn1 := Finset.mem_range.mp hn
  exact (natDegree_C_mul_le _ _).trans ((rowPrimitive_degree n y).trans (by omega))

theorem geometric_row (n : ℕ) (y : K) :
    (X-C y)*(∑ k∈Finset.Ico 1 (n+1), C (y^(n-k))*X^(k-1))=X^n-C (y^n) := by
  have he : (∑ k∈Finset.Ico 1 (n+1), C (y^(n-k))*(X : K[X])^(k-1))=
      ∑ r∈Finset.range n, X^r*(C y)^(n-1-r) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro r hr
    rw [show 1+r-1=r by omega,show n-(1+r)=n-1-r by omega,map_pow]
    ring
  rw [he,map_pow]
  exact (Commute.all (X : K[X]) (C y)).mul_geom_sum₂ n

theorem rowPrimitive_cleared_derivative (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hn : n<p) (y : K) :
    (X-C y)*(rowPrimitive n y).derivative=X^n-C (y^n) := by
  have hd : (rowPrimitive n y).derivative=
      ∑ k∈Finset.Ico 1 (n+1), C (y^(n-k))*X^(k-1) := by
    rw [rowPrimitive,derivative_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    have hkd : (k : K)≠0 := WPFiniteField.denominator_ne_zero p k
      (Finset.mem_Ico.mpr (by omega))
    rw [derivative_C_mul_X_pow,div_mul_cancel₀ _ hkd]
  rw [hd,geometric_row]

theorem HPrimitive_cleared_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (e : ℕ → K) (y : K) :
    (X-C y)*(HPrimitive N e y).derivative=
      sourcePolynomial N e-C (sourceValue N e y) := by
  rw [HPrimitive,derivative_sum,Finset.mul_sum]
  simp only [derivative_C_mul]
  calc
    _ = ∑ n∈Finset.range (N+1),
        C (e n)*(X^n-C (y^n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [show (X-C y)*(C (e n)*(rowPrimitive n y).derivative)=
          C (e n)*((X-C y)*(rowPrimitive n y).derivative) by ring,
        rowPrimitive_cleared_derivative p n (by have := Finset.mem_range.mp hn; omega)]
    _ = _ := by
      simp only [sourcePolynomial,sourceValue,mul_sub,Finset.sum_sub_distrib,map_sum,map_mul,map_pow]

theorem HPrimitive_polynomial_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (P : K[X]) (hP : P.natDegree≤N) (y : K) :
    (X-C y)*(HPrimitive N (fun n => P.coeff n) y).derivative=P-C (P.eval y) := by
  have he : sourceValue N (fun n => P.coeff n) y=P.eval y := by
    have hs := congrArg (fun Q : K[X] => Q.eval y) (sourcePolynomial_eq N P hP)
    simpa only [sourcePolynomial,sourceValue,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] using hs
  rw [HPrimitive_cleared_derivative p N hN,sourcePolynomial_eq N P hP,he]

noncomputable def LPolynomial (N : ℕ) : K[X] :=
  ∑ j∈Finset.Ico 1 (N+1), C ((j : K)⁻¹)*X^j

noncomputable def DPrimitive (N : ℕ) (y : K) : K[X] :=
  ∑ j∈Finset.Ico 1 (N+1), C ((j : K)⁻¹)*rowPrimitive j y

theorem LPolynomial_eval (N : ℕ) (v : K) :
    (LPolynomial N : K[X]).eval v=WPFiniteLoop.L N v := by
  simp only [LPolynomial,WPFiniteLoop.L,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem LPolynomial_degree (N : ℕ) : (LPolynomial N : K[X]).natDegree≤N := by
  unfold LPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj1 := (Finset.mem_Ico.mp hj).2
  exact (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X_pow]; omega)

theorem DPrimitive_eval (N : ℕ) (y v : K) :
    (DPrimitive N y).eval v=WPFiniteLoop.D N v y := by
  simp only [DPrimitive,WPFiniteLoop.D,eval_finsetSum,eval_mul,eval_C,rowPrimitive_eval,triangle,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem DPrimitive_eval_zero (N : ℕ) (y : K) : (DPrimitive N y).eval 0=0 := by
  simp only [DPrimitive,eval_finsetSum,eval_mul,eval_C,rowPrimitive_eval_zero,mul_zero,Finset.sum_const_zero]

theorem DPrimitive_degree (N : ℕ) (y : K) : (DPrimitive N y).natDegree≤N := by
  unfold DPrimitive
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hj1 := (Finset.mem_Ico.mp hj).2
  exact (natDegree_C_mul_le _ _).trans ((rowPrimitive_degree j y).trans (by omega))

theorem DPrimitive_cleared_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (y : K) :
    (X-C y)*(DPrimitive N y).derivative=LPolynomial N-C (WPFiniteLoop.L N y) := by
  rw [DPrimitive,derivative_sum,Finset.mul_sum]
  simp only [derivative_C_mul]
  calc
    _ = ∑ j∈Finset.Ico 1 (N+1), C ((j : K)⁻¹)*(X^j-C (y^j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (X-C y)*(C ((j : K)⁻¹)*(rowPrimitive j y).derivative)=
          C ((j : K)⁻¹)*((X-C y)*(rowPrimitive j y).derivative) by ring,
        rowPrimitive_cleared_derivative p j (by have := (Finset.mem_Ico.mp hj).2; omega)]
    _ = _ := by
      simp only [LPolynomial,WPFiniteLoop.L,mul_sub,Finset.sum_sub_distrib,map_sum,map_mul,div_eq_mul_inv]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]

noncomputable def affineArgument (a : K) : K[X] := C a*(X+1)

noncomputable def affineDPrimitive (N : ℕ) (a y : K) : K[X] :=
  (DPrimitive N (a*(1+y))).comp (affineArgument a)-
    C ((DPrimitive N (a*(1+y))).eval a)

theorem affineArgument_eval (a v : K) : (affineArgument a).eval v=a*(1+v) := by
  simp only [affineArgument,eval_mul,eval_C,eval_add,eval_X,eval_one]
  ring

theorem affineDPrimitive_eval (N : ℕ) (a y v : K) :
    (affineDPrimitive N a y).eval v=
      WPFiniteLoop.D N (a*(1+v)) (a*(1+y))-WPFiniteLoop.D N a (a*(1+y)) := by
  rw [affineDPrimitive,eval_sub,eval_comp,eval_C,affineArgument_eval,DPrimitive_eval,DPrimitive_eval]

theorem affineDPrimitive_eval_zero (N : ℕ) (a y : K) :
    (affineDPrimitive N a y).eval 0=0 := by
  rw [affineDPrimitive_eval]
  simp

theorem affineDPrimitive_degree (N : ℕ) (a y : K) :
    (affineDPrimitive N a y).natDegree≤N := by
  have ha : (affineArgument a).natDegree≤1 := by
    unfold affineArgument
    exact (natDegree_C_mul_le _ _).trans (by
      simpa only [natDegree_X,natDegree_one,Nat.max_zero] using
        natDegree_add_le (X : K[X]) 1)
  have hd := natDegree_comp_le.trans (Nat.mul_le_mul (DPrimitive_degree N (a*(1+y))) ha)
  unfold affineDPrimitive
  simpa only [Nat.max_zero] using natDegree_sub_le_of_le
    (by simpa only [Nat.mul_one] using hd) (le_of_eq (natDegree_C _))

theorem affineDPrimitive_cleared_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (a y : K) :
    (X-C y)*(affineDPrimitive N a y).derivative=
      (LPolynomial N : K[X]).comp (affineArgument a)-C (WPFiniteLoop.L N (a*(1+y))) := by
  have hD : (affineArgument a).derivative=C a := by simp [affineArgument]
  have hA : affineArgument a-C (a*(1+y))=(X-C y)*C a := by
    simp only [affineArgument,map_mul,map_add,map_one]
    ring
  have hs := congrArg (fun Q : K[X] => Q.comp (affineArgument a))
    (DPrimitive_cleared_derivative p N hN (a*(1+y)))
  simp only [mul_comp,sub_comp,X_comp,C_comp] at hs
  rw [affineDPrimitive,derivative_sub,derivative_C,sub_zero,derivative_comp,hD]
  calc
    _ = (affineArgument a-C (a*(1+y)))*
        (DPrimitive N (a*(1+y))).derivative.comp (affineArgument a) := by rw [hA]; ring
    _ = _ := hs

noncomputable def evenAffinePolynomial (N : ℕ) : K[X] :=
  C (1/2 : K)*((LPolynomial N : K[X]).comp (affineArgument (4/5 : K))-
    (LPolynomial N : K[X]).comp (affineArgument (1/5 : K)))

noncomputable def evenAffinePrimitive (N : ℕ) (y : K) : K[X] :=
  C (1/2 : K)*(affineDPrimitive N (4/5 : K) y-affineDPrimitive N (1/5 : K) y)

theorem evenAffinePolynomial_degree (N : ℕ) : (evenAffinePolynomial N : K[X]).natDegree≤N := by
  have ha (a : K) : (affineArgument a).natDegree≤1 := by
    unfold affineArgument
    exact (natDegree_C_mul_le _ _).trans (by
      simpa only [natDegree_X,natDegree_one,Nat.max_zero] using
        natDegree_add_le (X : K[X]) 1)
  have hd (a : K) : ((LPolynomial N : K[X]).comp (affineArgument a)).natDegree≤N := by
    simpa only [Nat.mul_one] using natDegree_comp_le.trans (Nat.mul_le_mul (LPolynomial_degree N) (ha a))
  exact (natDegree_C_mul_le _ _).trans (by
    simpa only [max_self] using natDegree_sub_le_of_le (hd _) (hd _))

theorem evenAffinePrimitive_degree (N : ℕ) (y : K) :
    (evenAffinePrimitive N y).natDegree≤N :=
  (natDegree_C_mul_le _ _).trans (by simpa only [max_self] using
    (natDegree_sub_le_of_le
      (affineDPrimitive_degree N _ y) (affineDPrimitive_degree N _ y)))

theorem evenAffinePrimitive_eval_zero (N : ℕ) (y : K) :
    (evenAffinePrimitive N y).eval 0=0 := by
  simp only [evenAffinePrimitive,eval_mul,eval_C,eval_sub,affineDPrimitive_eval_zero,sub_self,mul_zero]

theorem evenAffinePrimitive_cleared_derivative (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (y : K) :
    (X-C y)*(evenAffinePrimitive N y).derivative=
      evenAffinePolynomial N-C ((evenAffinePolynomial N : K[X]).eval y) := by
  rw [evenAffinePrimitive,derivative_C_mul,derivative_sub]
  calc
    _ = C (1/2 : K)*((X-C y)*(affineDPrimitive N (4/5 : K) y).derivative-
        (X-C y)*(affineDPrimitive N (1/5 : K) y).derivative) := by ring
    _ = _ := by
      rw [affineDPrimitive_cleared_derivative p N hN,
        affineDPrimitive_cleared_derivative p N hN]
      simp only [evenAffinePolynomial,eval_mul,eval_C,eval_sub,eval_comp,
        affineArgument_eval,LPolynomial_eval,map_mul,map_sub]
      ring

theorem zero_of_derivative_small (p : ℕ) [Fact p.Prime] [CharP K p]
    (Q : K[X]) (hQ : Q.natDegree<p) (hD : Q.derivative=0) (h0 : Q.eval 0=0) : Q=0 := by
  ext n
  by_cases hn : n=0
  · subst n
    simpa only [coeff_zero_eq_eval_zero,eval_zero] using h0
  by_cases hnp : p≤n
  · exact coeff_eq_zero_of_natDegree_lt (hQ.trans_le hnp)
  have hnsmall : n∈Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have he : Q.coeff n*(n : K)=0 := by
    have hc := congrArg (fun P : K[X] => P.coeff (n-1)) hD
    simpa only [coeff_derivative,←Nat.cast_add_one,Nat.sub_add_cancel (by omega : 1≤n),coeff_zero] using hc
  exact (mul_eq_zero.mp he).resolve_right (WPFiniteField.denominator_ne_zero p n hnsmall)

theorem HPrimitive_evenAffine (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (y : K) :
    HPrimitive N (fun n => (evenAffinePolynomial N : K[X]).coeff n) y=evenAffinePrimitive N y := by
  let H := HPrimitive N (fun n => (evenAffinePolynomial N : K[X]).coeff n) y
  let F := evenAffinePrimitive N y
  have hdH := HPrimitive_polynomial_derivative p N hN
    (evenAffinePolynomial N : K[X]) (evenAffinePolynomial_degree N) y
  have hdF := evenAffinePrimitive_cleared_derivative p N hN y
  have hfactor : (X-C y : K[X])≠0 := sub_ne_zero.mpr (X_ne_C y)
  have hD : (H-F).derivative=0 := by
    apply (mul_eq_zero.mp (show (X-C y)*(H-F).derivative=0 by
      rw [derivative_sub,mul_sub,hdH,hdF,sub_self])).resolve_left hfactor
  have hdeg : (H-F).natDegree<p :=
    (show (H-F).natDegree≤N by simpa only [max_self] using
      (natDegree_sub_le_of_le (HPrimitive_degree N _ y)
        (evenAffinePrimitive_degree N y))).trans_lt hN
  have hzero : (H-F).eval 0=0 := by
    rw [eval_sub,HPrimitive_eval_zero,evenAffinePrimitive_eval_zero,sub_self]
  exact sub_eq_zero.mp (zero_of_derivative_small p (H-F) hdeg hD hzero)

theorem finiteH_evenAffine_D (p N : ℕ) [Fact p.Prime] [CharP K p]
    (hN : N<p) (y v : K) :
    finiteH N (fun n => (evenAffinePolynomial N : K[X]).coeff n) y v=
      (WPFiniteLoop.D N ((4/5 : K)*(1+v)) ((4/5 : K)*(1+y))-
        WPFiniteLoop.D N (4/5 : K) ((4/5 : K)*(1+y))-
          WPFiniteLoop.D N ((1/5 : K)*(1+v)) ((1/5 : K)*(1+y))+
            WPFiniteLoop.D N (1/5 : K) ((1/5 : K)*(1+y)))/2 := by
  rw [←HPrimitive_eval,HPrimitive_evenAffine p N hN,
    evenAffinePrimitive,eval_mul,eval_C,eval_sub,affineDPrimitive_eval,affineDPrimitive_eval]
  ring

theorem movingEven_affine_identity (p : ℕ) :
    (WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate=
      evenAffinePolynomial ((p-1)/2) := by
  unfold WPFiniteWSource.deltaE evenAffinePolynomial LPolynomial
  rw [sum_comp,sum_comp,sum_comp]
  simp only [mul_comp,C_comp,pow_comp,X_comp,WPFiniteWSource.squaredCoordinate,affineArgument]
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hc : (((4 : K)^j-1)/(2*(j : K)))*((5 : K)⁻¹)^j=
      (1/2 : K)*((j : K)⁻¹*(4/5 : K)^j-(j : K)⁻¹*(1/5 : K)^j) := by
    simp only [div_eq_mul_inv,mul_inv_rev,mul_pow,one_pow]
    ring
  calc
    _ = C ((((4 : K)^j-1)/(2*(j : K)))*((5 : K)⁻¹)^j)*(X+1)^j := by
      rw [mul_pow,map_mul,map_pow]
      ring
    _ = C ((1/2 : K)*((j : K)⁻¹*(4/5 : K)^j-(j : K)⁻¹*(1/5 : K)^j))*(X+1)^j := by rw [hc]
    _ = _ := by
      simp only [map_mul,map_sub,mul_pow,map_pow]
      ring

/-- The literal moving even source has the original full four-D_N primitive. -/
theorem finiteH_movingEven_D (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (y v : K) :
    finiteH ((p-1)/2)
      (fun n => ((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate).coeff n) y v=
      (WPFiniteLoop.D ((p-1)/2) ((4/5 : K)*(1+v)) ((4/5 : K)*(1+y))-
        WPFiniteLoop.D ((p-1)/2) (4/5 : K) ((4/5 : K)*(1+y))-
          WPFiniteLoop.D ((p-1)/2) ((1/5 : K)*(1+v)) ((1/5 : K)*(1+y))+
            WPFiniteLoop.D ((p-1)/2) (1/5 : K) ((1/5 : K)*(1+y)))/2 := by
  rw [movingEven_affine_identity,finiteH_evenAffine_D p ((p-1)/2) (by omega)]

noncomputable def movingValue (p : ℕ) (v : K) : K :=
  (WPFiniteLoop.L ((p-1)/2) ((4/5 : K)*(1+v))-
    WPFiniteLoop.L ((p-1)/2) ((1/5 : K)*(1+v)))/2

noncomputable def movingH (p : ℕ) (y v : K) : K :=
  (WPFiniteLoop.D ((p-1)/2) ((4/5 : K)*(1+v)) ((4/5 : K)*(1+y))-
    WPFiniteLoop.D ((p-1)/2) (4/5 : K) ((4/5 : K)*(1+y))-
      WPFiniteLoop.D ((p-1)/2) ((1/5 : K)*(1+v)) ((1/5 : K)*(1+y))+
        WPFiniteLoop.D ((p-1)/2) (1/5 : K) ((1/5 : K)*(1+y)))/2

theorem movingEven_degree (p : ℕ) :
    ((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate).natDegree≤(p-1)/2 := by
  rw [movingEven_affine_identity]
  exact evenAffinePolynomial_degree _

theorem movingEven_eval (p : ℕ) (v : K) :
    ((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate).eval v=movingValue p v := by
  rw [movingEven_affine_identity]
  simp only [evenAffinePolynomial,eval_mul,eval_C,eval_sub,eval_comp,
    affineArgument_eval,LPolynomial_eval,movingValue]
  ring

theorem sourceValue_movingEven (p : ℕ) (v : K) :
    sourceValue ((p-1)/2)
      (fun n => ((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate).coeff n) v=
        movingValue p v := by
  have hs := congrArg (fun P : K[X] => P.eval v)
    (sourcePolynomial_eq ((p-1)/2)
      ((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate) (movingEven_degree p))
  simpa only [sourcePolynomial,sourceValue,eval_finsetSum,eval_mul,eval_C,eval_pow,
    eval_X,movingEven_eval] using hs

noncomputable def movingMinus (p : ℕ) (a b z : K) : K :=
  -2*movingH p b z-movingH p a z+3*movingH p 0 z

noncomputable def movingPlus (p : ℕ) (a b z : K) : K :=
  -2*(movingValue p b+movingValue p b⁻¹)*finiteLogValue p (b*z)-
    (movingValue p a+movingValue p a⁻¹)*finiteLogValue p (a*z)+
      2*movingH p b⁻¹ z+movingH p a⁻¹ z

/-- The full F1 toric trace for the literal moving source uses only the original D_N and L_N. -/
theorem literalF1_movingEven_D (p : ℕ) [Fact p.Prime] (hp : 19≤p) (d : ZMod p) :
    (-3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
      (ActualKwPhaseTrace.literalF1Laurent p*
        (LaurentPolynomial.C (1/15 : ZMod p)*(17-4*LaurentPolynomial.T (p : ℤ)-
          4*LaurentPolynomial.T (-(p : ℤ)))*
          (((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent+
            LaurentPolynomial.invert
              ((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent)+
          LaurentPolynomial.C d))=
      -2*movingMinus p (1/4 : ZMod p) 4 (1/4)+movingMinus p (1/4 : ZMod p) 4 4-
        (4/5 : ZMod p)*
          ((1/4 : ZMod p)*movingPlus p (1/4 : ZMod p) 4 (1/4 : ZMod p)⁻¹+
            (4 : ZMod p)*movingPlus p (1/4 : ZMod p) 4 (4 : ZMod p)⁻¹-
              (11/4 : ZMod p)*movingPlus p (1/4 : ZMod p) 4 (11/4 : ZMod p)⁻¹) := by
  let P : (ZMod p)[X] := (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate
  let e : ℕ → ZMod p := fun n => P.coeff n
  have he : finiteSource ((p-1)/2) e=P.toLaurent :=
    ActualKwPhaseTrace.finiteSource_polynomial ((p-1)/2) P (movingEven_degree p)
  have hH (y v : ZMod p) : finiteH ((p-1)/2) e y v=movingH p y v :=
    finiteH_movingEven_D p hp y v
  have hE (v : ZMod p) : sourceValue ((p-1)/2) e v=movingValue p v :=
    sourceValue_movingEven p v
  have hr := ActualKwPhaseTrace.literalF1_kernel_weight_two p ((p-1)/2) hp (by omega) e d
  rw [he] at hr
  simpa only [ActualKwPhaseTrace.minusH,ActualKwPhaseTrace.plusH,hH,hE,
    movingMinus,movingPlus] using hr

noncomputable def movingDend (p : ℕ) : K :=
  (WPFiniteLoop.L ((p-1)/2) (1/4 : K)-WPFiniteLoop.L ((p-1)/2) (4 : K))/2

noncomputable def movingRplus (p : ℕ) (z : K) : K :=
  movingDend p*(2*finiteLogValue p (4/z)+finiteLogValue p ((1/4)/z))+
    2*movingH p (1/4) z⁻¹+movingH p 4 z⁻¹

theorem movingDend_fermat (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    movingDend (K:=K) p=(WPFiniteInversion.integerFermatQuotient p 2 : K)+
      3*(WPFiniteInversion.integerFermatQuotient p 3 : K)/4 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  rcases WPFiniteLoop.L_rational_ends (K:=K) p hp with ⟨h1,hb,ha⟩
  unfold movingDend
  rw [ha,hb]
  field_simp [h2,h4]
  ring

theorem movingEndpoint_sum (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    movingValue p (1/4 : K)+movingValue p (4 : K)=-movingDend (K:=K) p := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h41 : (4/5 : K)*(1+1/4)=1 := by field_simp [h4,h5]; ring
  have h11 : (1/5 : K)*(1+1/4)=1/4 := by field_simp [h4,h5]; ring
  have h44 : (4/5 : K)*(1+4)=4 := by field_simp [h5]; ring
  have h14 : (1/5 : K)*(1+4)=1 := by field_simp [h5]; ring
  unfold movingValue movingDend
  rw [h41,h11,h44,h14]
  ring

theorem movingPlus_reciprocal (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (z : K) : movingPlus p (1/4 : K) 4 z⁻¹=movingRplus p z := by
  have ha : ((1/4 : K)⁻¹)=4 := by simp only [one_div,inv_inv]
  have hb : ((4 : K)⁻¹)=1/4 := by simp only [one_div]
  have he := movingEndpoint_sum (K:=K) p hp
  unfold movingPlus movingRplus
  rw [ha,hb,he,add_comm (movingValue p (4 : K)) (movingValue p (1/4 : K)),he]
  simp only [div_eq_mul_inv]
  ring

/-- The original SB102b end formula, with Dend retained as its exact finite-log difference. -/
theorem literalF1_movingEven_Tw (p : ℕ) [Fact p.Prime] (hp : 19≤p) (d : ZMod p) :
    (-3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
      (ActualKwPhaseTrace.literalF1Laurent p*
        (LaurentPolynomial.C (1/15 : ZMod p)*(17-4*LaurentPolynomial.T (p : ℤ)-
          4*LaurentPolynomial.T (-(p : ℤ)))*
          (((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent+
            LaurentPolynomial.invert
              ((WPFiniteWSource.deltaE p : (ZMod p)[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent)+
          LaurentPolynomial.C d))=
      -2*movingMinus p (1/4 : ZMod p) 4 (1/4)+movingMinus p (1/4 : ZMod p) 4 4-
        (4/5 : ZMod p)*
          ((1/4 : ZMod p)*movingRplus p (1/4 : ZMod p)+
            (4 : ZMod p)*movingRplus p (4 : ZMod p)-
              (11/4 : ZMod p)*movingRplus p (11/4 : ZMod p)) := by
  rw [literalF1_movingEven_D p hp d,movingPlus_reciprocal p hp,
    movingPlus_reciprocal p hp,movingPlus_reciprocal p hp]

end Primitive

end WPFieldAssembly.ActualKwFiniteHBridge
