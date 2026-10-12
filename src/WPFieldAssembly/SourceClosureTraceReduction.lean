import WPFieldAssembly.SourceClosureTraceOrigin
import WPFieldAssembly.ActualKwFieldTrace
import WPFieldAssembly.ActualSimplePoleResidue

open scoped LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualSimplePoleResidue
  WPFieldAssembly.SourceClosureTraceOrigin

namespace WPFieldAssembly.SourceClosureTraceReduction

set_option maxHeartbeats 1200000

theorem fieldWeight_derivative (p m : ℕ) [Fact p.Prime] (hp : 19≤p) (n : ℤ) :
    (n : ZMod p)*LaurentPoleField.fieldWeight p m (n-1)=
      (m : ZMod p)*(-8*LaurentPoleField.fieldWeight p (m+1) (n+1)+
        17*LaurentPoleField.fieldWeight p (m+1) n) := by
  have hq : (n : WPPIntegralReduction.integralRationals p)*
      LaurentPoleField.integralWeight p m hp (n-1)=
        (m : WPPIntegralReduction.integralRationals p)*
          (-8*LaurentPoleField.integralWeight p (m+1) hp (n+1)+
            17*LaurentPoleField.integralWeight p (m+1) hp n) := by
    apply Subtype.ext
    change (n : ℚ)*LaurentPoleTrace.weight m (n-1)=
      (m : ℚ)*(-8*LaurentPoleTrace.weight (m+1) (n+1)+
        17*LaurentPoleTrace.weight (m+1) n)
    exact LaurentPoleTrace.weight_derivative m n
  have h := congrArg (WPPIntegralReduction.residueHom p) hq
  simpa only [map_mul,map_add,map_neg,map_ofNat,map_intCast,map_natCast,
    LaurentPoleField.integralWeight_residue] using h

/-- The exact rational derivative relation is transported on every Laurent coefficient. -/
theorem fieldTrace_D (p m : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p m (D F)=
      (m : ZMod p)*LaurentPoleField.fieldTrace p (m+1) (F*dA) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add,add_mul,hF,hG]
    ring
  | C_mul_T n a =>
    have ht : (T n : (ZMod p)[T;T⁻¹])*T 1=T (n+1) := by rw [←T_add]
    have he : (LaurentPolynomial.C a*T n : (ZMod p)[T;T⁻¹])*dA=
        LaurentPolynomial.C (-8*a)*T (n+1)+LaurentPolynomial.C (17*a)*T n := by
      unfold dA
      simp only [map_mul,map_neg,map_ofNat]
      linear_combination -8*LaurentPolynomial.C a*ht
    rw [D_monomial,he,map_add,LaurentPoleField.fieldTrace_monomial,
      LaurentPoleField.fieldTrace_monomial,LaurentPoleField.fieldTrace_monomial]
    linear_combination a*fieldWeight_derivative p m hp n

theorem derivative_dA (p : ℕ) [Fact p.Prime] : D (dA : (ZMod p)[T;T⁻¹])=-8 := by
  have ht : D (T 1 : (ZMod p)[T;T⁻¹])=1 := by simpa using D_monomial (1 : ZMod p) 1
  change D (-LaurentPolynomial.C 8*T 1+LaurentPolynomial.C 17 :
    (ZMod p)[T;T⁻¹])=-8
  rw [neg_mul,map_add,map_neg,D_C_mul,D_C,ht]
  simp only [map_ofNat,mul_one,add_zero]

theorem quadratic_discriminant {K : Type*} [CommRing K] :
    (dA : K[T;T⁻¹])^2+16*A=225 := by unfold dA A; ring

noncomputable def doublePoleReduction (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (1/225 : ZMod p)*(8*F+dA*D F)

/-- The double pole reduces by the literal quadratic discriminant, including its derivative. -/
theorem fieldTrace_double_reduction (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p 2 F=
      LaurentPoleField.fieldTrace p 1 (doublePoleReduction p F) := by
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h225 : (225 : ZMod p)≠0 := by
    rw [show (225 : ZMod p)=15*15 by ring]
    exact mul_ne_zero h15 h15
  have hc (c : ZMod p) (m : ℕ) (G : (ZMod p)[T;T⁻¹]) :
      LaurentPoleField.fieldTrace p m (LaurentPolynomial.C c*G)=
        c*LaurentPoleField.fieldTrace p m G := by
    simpa only [smul_eq_C_mul,smul_eq_mul] using
      (LaurentPoleField.fieldTrace p m).map_smul c G
  have hb : (LaurentPolynomial.C (225 : ZMod p))*F=
      16*((LaurentPoleField.fieldAbar p).toLaurent*F)+(dA*F)*dA := by
    rw [map_ofNat]
    rw [←field_A]
    linear_combination -F*quadratic_discriminant (K:=ZMod p)
  have hbt := congrArg (LaurentPoleField.fieldTrace p 2) hb
  have hd := fieldTrace_D p 1 hp (dA*F)
  simp only [Nat.cast_one,one_mul] at hd
  have hd' : D (dA*F : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (-8 : ZMod p)*F+dA*D F := by
    rw [D_mul,derivative_dA]
    simp only [map_neg,map_ofNat]
  rw [hd',map_add,hc] at hd
  have h16 : (16 : (ZMod p)[T;T⁻¹])=LaurentPolynomial.C (16 : ZMod p) :=
    (map_ofNat (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) 16).symm
  rw [map_add,h16,hc,hc,LaurentPoleField.fieldTrace_cleared p 1 hp,←hd] at hbt
  rw [doublePoleReduction,hc,map_add,
    show (8 : (ZMod p)[T;T⁻¹])=LaurentPolynomial.C (8 : ZMod p) from
      (map_ofNat (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) 8).symm,hc]
  field_simp [h225]
  linear_combination hbt

/-- The full p+1 pole becomes a double pole under exact differential Cartier selection. -/
theorem fieldTrace_successor_cartier (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p (p+1) F=
      LaurentPoleField.fieldTrace p 2
        (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
          ((LaurentPoleField.fieldAbar p).toLaurent^(p-1)*F)) := by
  have h := LaurentPoleField.fieldTrace_cleared_pow p (p+1) (p-1) hp F
  rw [show p+1+(p-1)=p*2 by omega,LaurentPoleField.trace_frobenius_cartier p 2 hp] at h
  exact h.symm

noncomputable def successorPoleReduction (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) : (ZMod p)[T;T⁻¹] :=
  doublePoleReduction p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
    ((LaurentPoleField.fieldAbar p).toLaurent^(p-1)*F))

/-- This retains the complete high pole and both signed Cartier windows. -/
theorem fieldTrace_successor_reduction (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p (p+1) F=
      LaurentPoleField.fieldTrace p 1 (successorPoleReduction p F) := by
  rw [fieldTrace_successor_cartier p hp,fieldTrace_double_reduction p hp]
  rfl

theorem originTrace_one_literal (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) : originTrace p 1 F=originPole F := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => rw [map_add,originPole_add,hF,hG]
  | C_mul_T n a =>
    rw [originTrace_monomial,originWeight,originPole_trunc_inverse,map_mul,invert_C,invert_T,
      LaurentPolynomial.trunc_C_mul_T]
    cases n with
    | ofNat n =>
      rw [LaurentPoleField.fieldZcoeff,if_neg (by
        change ¬0≤-(n : ℤ)-1
        omega : ¬0≤-Int.ofNat n-1)]
      simp only [pow_one]
      by_cases hn : n=0
      · subst n
        simp
      · rw [if_neg (by
          change ¬0≤-(n : ℤ)
          omega : ¬0≤-Int.ofNat n)]
        simp
    | negSucc n =>
      rw [LaurentPoleField.fieldZcoeff,if_pos (by omega : 0≤-(Int.negSucc n)-1)]
      rw [show (-(Int.negSucc n)-1).toNat=n by omega,
        if_pos (by omega : 0≤-(Int.negSucc n)),
        show (-(Int.negSucc n)).toNat=n+1 by omega]
      simp only [Polynomial.eval_monomial,pow_one,LaurentPoleField.fieldReciprocal,
        PowerSeries.coeff_mk]
      have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
        (Finset.mem_Ico.mpr (by omega))
      have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
        (Finset.mem_Ico.mpr (by omega))
      field_simp [h4,h15]
      ring

/-- The original infinity convention gives minus the native simple-pole origin. -/
theorem fieldTrace_one_native_origin (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p 1 F=-originPole (invert F) := by
  rw [fieldTrace_origin]
  norm_num only [Nat.cast_one,mul_one,sub_self,T_zero,one_mul]
  rw [originTrace_one_literal p hp]

theorem fieldTrace_successor_native_origin (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    LaurentPoleField.fieldTrace p (p+1) F=
      -originPole (invert (successorPoleReduction p F)) := by
  rw [fieldTrace_successor_reduction p hp,fieldTrace_one_native_origin p hp]

theorem originPole_transport {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (F : K[T;T⁻¹]) :
    f (originPole F)=originPole (WPActualChiSource.coefficientMap f F) := by
  unfold originPole
  rw [map_div₀,←WPActualChiSource.coefficientMap_coeff]
  simp only [map_sub,GreenLaurentOperators.DD_map,map_div₀,map_one,map_ofNat]

end WPFieldAssembly.SourceClosureTraceReduction
