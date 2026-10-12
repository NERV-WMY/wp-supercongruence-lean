import WPFieldAssembly.GreenLaurentOperators

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualSimplePoleResidue

variable {K : Type*} [Field K]

set_option maxHeartbeats 1200000

/-- The literal residue at zero of F/Abar, using the two retained divided differences. -/
noncomputable def originPole (F : K[T;T⁻¹]) : K :=
  ((DD (1/4 : K) 4 F-DD 4 (1/4 : K) F).coeff (-1))/15

theorem originPole_add (F G : K[T;T⁻¹]) :
    originPole (F+G)=originPole F+originPole G := by
  simp only [originPole,map_add,AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_add,Finsupp.sub_apply,Finsupp.add_apply]
  ring

theorem originPole_sub (F G : K[T;T⁻¹]) :
    originPole (F-G)=originPole F-originPole G := by
  simp only [originPole,map_sub,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply]
  ring

theorem originPole_C_mul (c : K) (F : K[T;T⁻¹]) :
    originPole (LaurentPolynomial.C c*F)=c*originPole F := by
  have ha : DD (1/4 : K) 4 (LaurentPolynomial.C c*F)=
      LaurentPolynomial.C c*DD (1/4 : K) 4 F := by
    simpa only [LaurentPolynomial.smul_eq_C_mul] using (DD (1/4 : K) 4).map_smul c F
  have hb : DD (4 : K) (1/4) (LaurentPolynomial.C c*F)=
      LaurentPolynomial.C c*DD (4 : K) (1/4) F := by
    simpa only [LaurentPolynomial.smul_eq_C_mul] using (DD (4 : K) (1/4)).map_smul c F
  rw [originPole,ha,hb,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
    C_mul_coeff,C_mul_coeff]
  unfold originPole
  rw [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply]
  ring

private theorem DD_origin_single (a ai c : K) (n : ℤ) :
    (DD a ai (LaurentPolynomial.C c*T n)).coeff (-1)=
      if n<0 then -c*ai^(-n).toNat else 0 := by
  rw [DD_monomial,C_mul_coeff]
  cases n with
  | ofNat n =>
    rw [monQ,forward_coeff]
    change c*(if 0≤(-1 : ℤ) ∧ -1<(n : ℤ) then
      a^((n : ℤ)-1-(-1)).toNat else 0)=
        if (n : ℤ)<0 then -c*ai^(-(n : ℤ)).toNat else 0
    simp only [show ¬(0≤(-1 : ℤ) ∧ -1<(n : ℤ)) by omega,
      if_false,mul_zero,show ¬((n : ℤ)<0) by omega]
  | negSucc n =>
    rw [monQ,←map_neg (LaurentPolynomial.C : K →+* K[T;T⁻¹]),
      shift_coeff,forward_coeff]
    have hk : (-1 : ℤ)-(-(n+1 : ℤ))=(n : ℤ) := by omega
    rw [hk,if_pos (by omega : 0≤(n : ℤ) ∧ (n : ℤ)<((n+1 : ℕ) : ℤ))]
    simp only [show (((n+1 : ℕ) : ℤ)-1-(n : ℤ)).toNat=0 by omega,
      pow_zero,mul_one,show Int.negSucc n<0 by omega,if_true]
    have ht : (-(Int.negSucc n)).toNat=n+1 := by omega
    rw [ht]
    ring

/-- Every negative Laurent coefficient is retained; nonnegative terms have zero residue. -/
theorem originPole_trunc_inverse (F : K[T;T⁻¹]) :
    originPole F=
      ((LaurentPolynomial.trunc (invert F)).eval (1/4)-
        (LaurentPolynomial.trunc (invert F)).eval 4)/15 := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    rw [originPole_add,hF,hG]
    simp only [map_add,eval_add]
    ring
  | C_mul_T n c =>
    rw [originPole,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,
      DD_origin_single,DD_origin_single,map_mul,invert_C,invert_T,
      LaurentPolynomial.trunc_C_mul_T]
    by_cases hn : n<0
    · simp only [if_pos hn,if_pos (by omega : 0≤-n),eval_monomial]
      ring
    · simp only [if_neg hn]
      by_cases hz : n=0
      · subst n
        simp only [neg_zero,le_refl,if_true,Int.toNat_zero,eval_monomial,pow_zero,mul_one]
        ring
      · rw [if_neg (by omega : ¬0≤-n)]
        simp

theorem originPole_polynomial (P : K[X]) : originPole P.toLaurent=0 := by
  rw [originPole_trunc_inverse,WPFiniteJWeightedResidue.trunc_invert]
  simp only [eval_C,sub_self,zero_div]

private theorem linear_factor_nonzero (a : K) :
    (T 1-LaurentPolynomial.C a : K[T;T⁻¹])≠0 := by
  intro h
  have hc := congrArg (fun F : K[T;T⁻¹] => F.coeff 1) h
  simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,T_apply,
    LaurentPolynomial.C_apply,if_neg (by omega : (1 : ℤ)≠0),sub_zero,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
  exact one_ne_zero hc

/-- Clearing the actual quadratic denominator gives its literal residue coefficient. -/
theorem originPole_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (F : K[T;T⁻¹]) :
    originPole ((WPFiniteZSource.Abar : K[X]).toLaurent*F)=F.coeff (-1) := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := div_ne_zero one_ne_zero h4
  let A : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  have hunit : (4 : K[T;T⁻¹])*LaurentPolynomial.C (1/4 : K)=1 := by
    change LaurentPolynomial.C (4 : K)*LaurentPolynomial.C (1/4 : K)=
      LaurentPolynomial.C (1 : K)
    rw [←map_mul,mul_one_div_cancel h4,map_one]
  have hA : A= -4*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4) := by
    dsimp only [A]
    simp only [WPFiniteZSource.Abar,map_mul,map_sub,map_ofNat,map_one,
      Polynomial.toLaurent_X]
    linear_combination (4-T 1)*hunit
  have hva : ev (1/4 : K) ha (A*F)=0 := by
    rw [hA]
    simp [ev,map_mul]
  have hvb : ev (4 : K) h4 (A*F)=0 := by
    rw [hA]
    simp [ev,map_mul,map_ofNat]
  have hda := DD_identity (1/4 : K) ha (A*F)
  have hdb := DD_identity (4 : K) h4 (A*F)
  rw [hva,map_zero,sub_zero] at hda
  rw [hvb,map_zero,sub_zero] at hdb
  have hia : (1/4 : K)⁻¹=4 := by simp
  have hib : (4 : K)⁻¹=1/4 := by simp
  rw [hia] at hda
  rw [hib] at hdb
  have hda' : DD (1/4 : K) 4 (A*F)= -4*(T 1-4)*F := by
    apply mul_left_cancel₀ (linear_factor_nonzero (1/4 : K))
    rw [hda,hA]
    ring
  have hdb' : DD (4 : K) (1/4) (A*F)=
      -4*(T 1-LaurentPolynomial.C (1/4 : K))*F := by
    apply mul_left_cancel₀ (linear_factor_nonzero (4 : K))
    rw [hdb,hA]
    simp only [map_ofNat]
    ring
  have hd : DD (1/4 : K) 4 (A*F)-DD (4 : K) (1/4) (A*F)=
      LaurentPolynomial.C (15 : K)*F := by
    rw [hda',hdb']
    simp only [map_ofNat]
    linear_combination -F*hunit
  change ((DD (1/4 : K) 4 (A*F)-DD (4 : K) (1/4) (A*F)).coeff (-1))/15=_
  rw [hd,C_mul_coeff,mul_div_cancel_left₀ _ h15]

end WPFieldAssembly.ActualSimplePoleResidue
