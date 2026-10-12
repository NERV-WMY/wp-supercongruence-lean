import WPFieldAssembly.ActualKwWeightedTrace
import Mathlib.Algebra.CharP.Algebra

open scoped Polynomial LaurentPolynomial PowerSeries
open LaurentPolynomial WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualKwWeightedTrace

namespace WPFieldAssembly.SourceClosureUVPhaseTrace

set_option maxHeartbeats 1400000

/- The actual canonical p-hole contributes 99/4 under the original
   rational Frobenius weight. Its endpoint contribution is retained
   separately until the original joint consumer is formed. -/

theorem reciprocal_first_band (p k : ℕ) [Fact p.Prime] (hp : 19≤p) (hk : k<p) :
    PowerSeries.coeff k (LaurentPoleField.fieldReciprocal p^(p+1))=
      PowerSeries.coeff k (LaurentPoleField.fieldReciprocal p) := by
  have hsplit := LaurentPoleField.reciprocal_frobenius_split p 1 1 hp
  simp only [Nat.mul_one,pow_one] at hsplit
  rw [hsplit]
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single 0]
  · simp only [PowerSeries.coeff_expand,dvd_zero,if_true,Nat.zero_div,Nat.sub_zero]
    have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
    have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
      (Finset.mem_Ico.mpr (by omega))
    have hzero : PowerSeries.coeff 0 (LaurentPoleField.fieldReciprocal p)=1 := by
      simp only [LaurentPoleField.fieldReciprocal,PowerSeries.coeff_mk]
      field_simp [h4,h15]
      linear_combination -(mul_inv_cancel₀ h4)
    rw [hzero,one_mul]
  · intro j hj hj0
    have hjp : j<p := by have := Finset.mem_range.mp hj; omega
    have hnot : ¬p∣j := by
      intro h
      have := Nat.le_of_dvd (by omega : 0<j) h
      omega
    rw [PowerSeries.coeff_expand_of_not_dvd p (by omega) _ hnot,zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem weight_below_cutoff (p m : ℕ) [Fact p.Prime] (j : ℤ)
    (hj : j<2*(m : ℤ)-1) : LaurentPoleField.fieldWeight p m j=0 := by
  rw [LaurentPoleField.fieldWeight,LaurentPoleField.fieldZcoeff,
    if_neg (by omega)]
  simp only [LinearMap.zero_apply,mul_zero]

/-- Both top weights are derived from the original reciprocal, with no fitted value. -/
theorem original_top_weights (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPoleField.fieldWeight p (p+1) (3*(p : ℤ)-1)=0 ∧
      LaurentPoleField.fieldWeight p (p+1) (3*(p : ℤ))=-(1/16 : ZMod p) := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h4end := ZMod.pow_card_sub_one_eq_one h4
  have haend := ZMod.pow_card_sub_one_eq_one (one_div_ne_zero h4)
  have hlow : PowerSeries.coeff (p-2) (LaurentPoleField.fieldReciprocal p)=0 := by
    simp only [LaurentPoleField.fieldReciprocal,PowerSeries.coeff_mk]
    rw [show p-2+1=p-1 by omega,h4end,haend,sub_self,mul_zero]
  have hhigh : PowerSeries.coeff (p-1) (LaurentPoleField.fieldReciprocal p)=1 := by
    simp only [LaurentPoleField.fieldReciprocal,PowerSeries.coeff_mk]
    rw [show p-1+1=p by omega,ZMod.pow_card,ZMod.pow_card]
    field_simp [h4,h15]
    ring
  have hscale : (-1/4 : ZMod p)^(p+1)=1/16 := by
    rw [pow_succ,ZMod.pow_card]
    have h16 : (16 : ZMod p)≠0 := by
      rw [show (16 : ZMod p)=4*4 by ring]
      exact mul_ne_zero h4 h4
    field_simp [h4,h16]
    ring
  constructor
  · rw [LaurentPoleField.fieldWeight,
      show 3*(p : ℤ)-1-(2*((p+1 : ℕ) : ℤ)-1)=((p-2 : ℕ) : ℤ) by omega]
    simp only [LaurentPoleField.fieldZcoeff,Int.natCast_nonneg,if_pos,Int.toNat_natCast]
    rw [reciprocal_first_band p (p-2) hp (by omega),hlow,mul_zero]
  · rw [LaurentPoleField.fieldWeight,
      show 3*(p : ℤ)-(2*((p+1 : ℕ) : ℤ)-1)=((p-1 : ℕ) : ℤ) by omega]
    simp only [LaurentPoleField.fieldZcoeff,Int.natCast_nonneg,if_pos,Int.toNat_natCast]
    rw [reciprocal_first_band p (p-1) hp (by omega),hhigh,mul_one,hscale]

noncomputable def originalPhi (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  T (p : ℤ)+T (-(p : ℤ))-LaurentPolynomial.C (17/4 : ZMod p)

theorem original_R_power (p : ℕ) [Fact p.Prime] :
    (R : (ZMod p)[T;T⁻¹])^p=4*T (2*(p : ℤ))-11*T (p : ℤ) := by
  have hC : Function.Injective (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) := by
    intro a b hab
    have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff 0) hab
    simpa only [LaurentPolynomial.C_apply,if_true] using he
  have : CharP (ZMod p)[T;T⁻¹] p :=
    charP_of_injective_ringHom (f:=LaurentPolynomial.C) hC p
  change (T 1*(LaurentPolynomial.C (4 : ZMod p)*T 1-
    LaurentPolynomial.C (11 : ZMod p)))^p=_
  rw [mul_pow,sub_pow_char (p:=p),mul_pow,←map_pow,←map_pow,
    ZMod.pow_card,ZMod.pow_card]
  simp only [T_pow,mul_one,map_ofNat]
  have ht : (T (p : ℤ)*T (p : ℤ) : (ZMod p)[T;T⁻¹])=T (2*(p : ℤ)) := by
    rw [←T_add]
    congr 1
    ring
  linear_combination 4*ht

/-- Every lower phase is still present in the numerator before tracing. -/
theorem original_phase_numerator (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    3*(R : (ZMod p)[T;T⁻¹])^p*originalPhi p=
      12*T (3*(p : ℤ))-84*T (2*(p : ℤ))+
        LaurentPolynomial.C (609/4 : ZMod p)*T (p : ℤ)-33 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  let U : (ZMod p)[T;T⁻¹] := T (p : ℤ)
  let V : (ZMod p)[T;T⁻¹] := T (-(p : ℤ))
  let g : (ZMod p)[T;T⁻¹] := LaurentPolynomial.C (17/4 : ZMod p)
  have hUV : U*V=1 := by dsimp only [U,V]; rw [←T_add]; simp
  have h2 : T (2*(p : ℤ))=U^2 := by dsimp only [U]; rw [T_pow]; norm_num
  have h3 : T (3*(p : ℤ))=U^3 := by dsimp only [U]; rw [T_pow]; norm_num
  have h51 : 12*g=51 := by
    have hs : 12*(17/4 : ZMod p)=51 := by field_simp [h4]; ring
    have h := congrArg LaurentPolynomial.C hs
    simpa only [map_mul,map_ofNat,g] using h
  have h609 : LaurentPolynomial.C (609/4 : ZMod p)=12+33*g := by
    have hs : (609/4 : ZMod p)=12+33*(17/4) := by field_simp [h4]; ring
    have h := congrArg LaurentPolynomial.C hs
    simpa only [map_add,map_mul,map_ofNat,g] using h
  rw [original_R_power,originalPhi,h2,h3,h609]
  change 3*(4*U^2-11*U)*(U+V-g)=12*U^3-84*U^2+(12+33*g)*U-33
  linear_combination (12*U-33)*hUV-U^2*h51

noncomputable def originalWeightedFieldTrace (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[T;T⁻¹]) : ZMod p :=
  LaurentPoleField.fieldTrace p (p+1)
    (3*(R : (ZMod p)[T;T⁻¹])^p*(3*T (-1)*(4-11*T 1))*F)

/-- The actual p-hole weight is 99/4; its coupled endpoint correction is not discarded. -/
theorem originalPhi_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (originalPhi p)=99/4 := by
  have htop := original_top_weights p hp
  have hl (n : ℤ) (hn : n≤2*(p : ℤ)) (c : ZMod p) :
      LaurentPoleField.fieldTrace p (p+1)
        (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))=0 := by
    rw [literal_density_monomial,map_sub,LaurentPoleField.fieldTrace_monomial,
      LaurentPoleField.fieldTrace_monomial,
      weight_below_cutoff p (p+1) (n-1) (by omega),
      weight_below_cutoff p (p+1) n (by omega)]
    ring
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4*4 by ring]
    exact mul_ne_zero h4 h4
  unfold originalWeightedFieldTrace
  rw [show (3*(R : (ZMod p)[T;T⁻¹])^p*(3*T (-1)*(4-11*T 1)))*originalPhi p=
      (3*T (-1)*(4-11*T 1))*(3*R^p*originalPhi p) by ring,
    original_phase_numerator p hp]
  suffices LaurentPoleField.fieldTrace p (p+1)
    ((3*T (-1)*(4-11*T 1))*(LaurentPolynomial.C 12*T (3*(p : ℤ))-
      LaurentPolynomial.C 84*T (2*(p : ℤ))+
      LaurentPolynomial.C (609/4 : ZMod p)*T (p : ℤ)-LaurentPolynomial.C 33*T 0))=99/4 by
    simpa only [map_ofNat,T_zero,mul_one] using this
  rw [mul_sub,mul_add,mul_sub,map_sub,map_add,map_sub,
    hl (2*(p : ℤ)) (by omega) 84,hl (p : ℤ) (by omega) (609/4),hl 0 (by omega) 33,
    literal_density_monomial,map_sub,LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,htop.1,htop.2]
  field_simp [h4,h16]
  ring

end WPFieldAssembly.SourceClosureUVPhaseTrace
