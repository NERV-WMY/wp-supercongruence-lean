import WPFieldAssembly.SourceClosureVbalNativePrimitive
import WPFieldAssembly.NativeIR28
import WPFiniteJSource

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoComparison
  WPActualRankTwoProper WPActualRankTwoResidueSource WPActualRankTwoFiniteLegendre
  WPActualGaussBottom WPFieldAssembly.NativeIR28

namespace WPFieldAssembly.SourceClosureVbalNativePrimitive

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/- The original conic carrier loses its first three branch jets before normalization.
The fourth conic derivative retains the coefficient 300 of the second native jet. -/
omit [Fact p.Prime] in
theorem conic_carrier_three_branch_jets {K : Type*} [Field K] [CharP K p]
    (hp : 19≤p) (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h5 : (5 : K)≠0)
    (carrier H : K[X]) (c : K)
    (hconic : carrier.comp (5*X^2-1)=C c*X^p*H) :
    carrier.eval (-1)=0 ∧ carrier.derivative.eval (-1)=0 ∧
      carrier.derivative.derivative.eval (-1)=0 := by
  let Q : K[X] := 5*X^2-1
  have hQ0 : Q.eval 0=-1 := by norm_num [Q]
  have hQ1 : Q.derivative=10*X := by
    norm_num [Q,derivative_sub,derivative_mul,derivative_pow,C_ofNat]
    ring
  have hQ2 : Q.derivative.derivative=10 := by
    rw [hQ1]
    norm_num [derivative_mul]
  have hprod2 (P R : K[X]) :
      (P*R).derivative.derivative.eval 0=
        P.derivative.derivative.eval 0*R.eval 0+
          2*P.derivative.eval 0*R.derivative.eval 0+
            P.eval 0*R.derivative.derivative.eval 0 := by
    rw [derivative_mul,derivative_add,derivative_mul,derivative_mul]
    simp only [eval_add,eval_mul]
    ring
  have hsecond (P : K[X]) :
      (P.comp Q).derivative.derivative=
        P.derivative.derivative.comp Q*(10*X)^2+P.derivative.comp Q*10 := by
    rw [derivative_comp,derivative_mul,derivative_comp,hQ2,hQ1]
    ring
  have hsecond_eval (P : K[X]) :
      (P.comp Q).derivative.derivative.eval 0=10*P.derivative.eval (-1) := by
    rw [hsecond]
    simp only [eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_comp,hQ0,
      mul_zero,zero_pow (by norm_num : (2 : ℕ)≠0),zero_add]
    ring
  have hw0 : ((10*X)^2 : K[X]).eval 0=0 := by norm_num
  have hw1 : ((10*X)^2 : K[X]).derivative.eval 0=0 := by
    norm_num [derivative_sq,derivative_mul,C_ofNat]
  have hw2 : ((10*X)^2 : K[X]).derivative.derivative.eval 0=200 := by
    norm_num [derivative_sq,derivative_mul,C_ofNat]
  have hfourth (P : K[X]) :
      (P.comp Q).derivative.derivative.derivative.derivative.eval 0=
        300*P.derivative.derivative.eval (-1) := by
    rw [hsecond]
    simp only [derivative_add,eval_add]
    rw [hprod2,hprod2]
    simp only [hw0,hw1,hw2,eval_comp,hQ0,hsecond_eval,eval_ofNat,
      derivative_ofNat,derivative_zero,eval_zero,mul_zero,add_zero,zero_add]
    ring
  have hXp : (X^p : K[X]).derivative=0 := by
    rw [derivative_X_pow,CharP.cast_eq_zero K p,C_0,zero_mul]
  have hp0 : p≠0 := by omega
  have hphaseD (R : K[X]) : (C c*X^p*R).derivative=C c*X^p*R.derivative := by
    rw [derivative_mul,derivative_mul,derivative_C,hXp]
    simp only [zero_mul,mul_zero,zero_add]
  have hphase0 (R : K[X]) : (C c*X^p*R).eval 0=0 := by
    simp only [eval_mul,eval_pow,eval_X,zero_pow hp0,mul_zero,zero_mul]
  have hright0 : (C c*X^p*H).eval 0=0 := hphase0 H
  have hright2 : (C c*X^p*H).derivative.derivative.eval 0=0 := by
    rw [hphaseD,hphaseD]
    exact hphase0 _
  have hright4 : (C c*X^p*H).derivative.derivative.derivative.derivative.eval 0=0 := by
    rw [hphaseD,hphaseD,hphaseD,hphaseD]
    exact hphase0 _
  have h10 : (10 : K)≠0 := by
    rw [show (10 : K)=2*5 by ring]
    exact mul_ne_zero h2 h5
  have h300 : (300 : K)≠0 := by
    rw [show (300 : K)=2^2*3*5^2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) (pow_ne_zero _ h5)
  change carrier.comp Q=C c*X^p*H at hconic
  have hzero := congrArg (fun P : K[X] => P.eval 0) hconic
  rw [eval_comp,hQ0,hright0] at hzero
  have hfirst := congrArg (fun P : K[X] => P.derivative.derivative.eval 0) hconic
  rw [hsecond_eval,hright2] at hfirst
  have hlast := congrArg (fun P : K[X] =>
    P.derivative.derivative.derivative.derivative.eval 0) hconic
  rw [hfourth,hright4] at hlast
  exact ⟨hzero,(mul_eq_zero.mp hfirst).resolve_left h10,
    (mul_eq_zero.mp hlast).resolve_left h300⟩

theorem actual_JLP_odd :
    (WPFiniteKSource.JLP p : (ZMod p)[X]).comp (-X)=-WPFiniteKSource.JLP p := by
  have hAP : (WPFiniteKSource.AP : (ZMod p)[X]).comp (-X)=WPFiniteKSource.BP := by
    simp only [WPFiniteKSource.AP,WPFiniteKSource.BP,mul_comp,C_comp,add_comp,
      one_comp,X_comp]
    ring
  have hBP : (WPFiniteKSource.BP : (ZMod p)[X]).comp (-X)=WPFiniteKSource.AP := by
    simp only [WPFiniteKSource.AP,WPFiniteKSource.BP,mul_comp,C_comp,sub_comp,
      one_comp,X_comp]
    ring
  simp only [WPFiniteKSource.JLP,mul_comp,C_comp,sub_comp,comp_assoc,hAP,hBP]
  ring

/-- The actual proper primitive has its original odd reflection, including the high phase. -/
theorem actual_native_proper_primitive_odd (hp : 19≤p) :
    (actualNativeProperPrimitive p hp).comp (-X)=-actualNativeProperPrimitive p hp := by
  let s : ZMod p := (-1)^(p/6)
  have hs : s^2=1 := by
    dsimp only [s]
    rw [←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have hsp : (C s : (ZMod p)[X])^2=1 := by rw [←C_pow,hs,C_1]
  have hY : (actualLegendreJacobi p).comp (-X)=C s*actualLegendreJacobi p :=
    legendreField_reflect p (p/6) (by omega)
  have hn := actual_proper_legendre_reflect p hp
  have hR := actual_rank_divided_reflect p hp
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hXp : (-X : (ZMod p)[X])^p=-X^p := hpodd.neg_pow X
  simp only [actualNativeProperPrimitive,add_comp,mul_comp,C_comp,pow_comp,
    X_comp,hY,hn,hR,hXp,actual_JLP_odd p]
  linear_combination -(properLegendreJacobi p*actualRankDividedField p (by omega)+
    C (1/2 : ZMod p)*X^p*properLegendreJacobi p^2+
      actualLegendreJacobi p^2*WPFiniteKSource.JLP p)*hsp

/-- The complete proper primitive retains the full p+2d-2 degree bound. -/
theorem actual_native_proper_primitive_degree (hp : 19≤p) :
    (actualNativeProperPrimitive p hp).natDegree≤p+2*(p/6)-2 := by
  let d := p/6
  have hd : 1≤d := by dsimp only [d]; omega
  have hn : (properLegendreJacobi p).natDegree≤d-1 := by
    have ht := properLegendreJacobi_degree p (by omega)
    dsimp only [d] at *
    omega
  have hR := actualRankDividedField_degree p (by omega : 7≤p)
  have hlow : (properLegendreJacobi p*actualRankDividedField p (by omega)).natDegree≤
      p+2*d-2 := by
    have ht := natDegree_mul_le_of_le hn hR
    dsimp only [d] at *
    omega
  have hnsq : (properLegendreJacobi p^2).natDegree≤2*d-2 := by
    rw [natDegree_pow]
    have := Nat.mul_le_mul_left 2 hn
    omega
  have hXp : (C (1/2 : ZMod p)*X^p : (ZMod p)[X]).natDegree≤p :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hphase : (C (1/2 : ZMod p)*X^p*properLegendreJacobi p^2).natDegree≤
      p+2*d-2 := (natDegree_mul_le_of_le hXp hnsq).trans (by omega)
  have hF : (actualLegendreJacobi p^2).natDegree≤2*d := by
    rw [natDegree_pow]
    exact Nat.mul_le_mul_left 2 (actualLegendreJacobi_degree p)
  have hJ : (WPFiniteKSource.JLP p : (ZMod p)[X]).natDegree≤p-2 := by
    rw [WPFiniteJSource.JLP_eq_harmonic p hp]
    exact WPFiniteJSource.JHP_natDegree_le p hp
  have hlog : (actualLegendreJacobi p^2*WPFiniteKSource.JLP p).natDegree≤
      p+2*d-2 := (natDegree_mul_le_of_le hF hJ).trans (by omega)
  unfold actualNativeProperPrimitive
  simpa only [max_self] using
    natDegree_add_le_of_le (natDegree_add_le_of_le hlow hphase) hlog

private theorem actual_JLP_end_one (hp : 19≤p) :
    (WPFiniteKSource.JLP p : (ZMod p)[X]).eval 1=0 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have ha : ((1 : ZMod p)+1)/2=1 := by
    rw [show (1 : ZMod p)+1=2 by ring,div_self h2]
  have hR : WPFiniteField.R p (1 : ZMod p)=0 :=
    WPFiniteInversion.R_one_eq_zero p (by omega)
  have hR0 : WPFiniteField.R p (0 : ZMod p)=0 := by
    unfold WPFiniteField.R
    apply Finset.sum_eq_zero
    intro j hj
    have hjpos : 0<j := (Finset.mem_Ico.mp hj).1
    simp only [zero_pow (by omega : j≠0),zero_div]
  rw [WPFiniteKSource.JLP_eval,WPFiniteNC122.J_L,ha,sub_self,zero_div,
    hR0,hR]
  ring

/-- The actual two proper ends retain the literal half harmonic square with opposite signs. -/
theorem actual_native_proper_primitive_ends (hp : 19≤p) :
    (actualNativeProperPrimitive p hp).eval 1=(fieldHarmonic p (p/6))^2/2 ∧
    (actualNativeProperPrimitive p hp).eval (-1)=-(fieldHarmonic p (p/6))^2/2 := by
  have h1 : (actualNativeProperPrimitive p hp).eval 1=(fieldHarmonic p (p/6))^2/2 := by
    simp only [actualNativeProperPrimitive,eval_add,eval_mul,eval_C,eval_pow,eval_X,
      properLegendreJacobi_endpoint_one,actualRankDividedField_endpoint_one,
      actualLegendreJacobi_endpoint_one,actual_JLP_end_one p hp,one_pow,mul_zero,
      zero_add,add_zero]
    ring
  have hm := congrArg (fun P : (ZMod p)[X] => P.eval 1)
    (actual_native_proper_primitive_odd p hp)
  simp only [eval_comp,eval_neg,eval_X,h1] at hm
  exact ⟨h1,by linear_combination hm⟩

/-- The literal t^p/5 pullback is even and therefore has the prescribed contract2 carrier. -/
theorem actual_native_proper_carrier_even (hp : 19≤p) :
    (C (1/5 : ZMod p)*X^p*(actualNativeProperPrimitive p hp).comp
      (4*X^3-3*X)).comp (-X)=
      C (1/5 : ZMod p)*X^p*(actualNativeProperPrimitive p hp).comp (4*X^3-3*X) := by
  let Tc : (ZMod p)[X] := 4*X^3-3*X
  have ht : Tc.comp (-X)=-Tc := by
    simp only [Tc,sub_comp,mul_comp,ofNat_comp,pow_comp,X_comp]
    ring
  have he := congrArg (fun P : (ZMod p)[X] => P.comp Tc)
    (actual_native_proper_primitive_odd p hp)
  simp only [comp_assoc,neg_comp,X_comp] at he
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hXp : (-X : (ZMod p)[X])^p=-X^p := hpodd.neg_pow X
  change (C (1/5 : ZMod p)*X^p*(actualNativeProperPrimitive p hp).comp Tc).comp (-X)=_
  simp only [mul_comp,C_comp,pow_comp,X_comp,comp_assoc,ht,he,hXp]
  ring

end WPFieldAssembly.SourceClosureVbalNativePrimitive
