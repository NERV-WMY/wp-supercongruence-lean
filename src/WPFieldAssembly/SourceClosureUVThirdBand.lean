import WPFieldAssembly.SourceClosureUVWeightedBands

open scoped Polynomial LaurentPolynomial PowerSeries BigOperators
open LaurentPolynomial WPFiniteLaurentDifferential WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedBands

namespace WPFieldAssembly.SourceClosureUVThirdBand

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

theorem original_reciprocal_first_coefficients (hp : 19≤p) :
    PowerSeries.coeff 0 (LaurentPoleField.fieldReciprocal p)=1 ∧
      PowerSeries.coeff 1 (LaurentPoleField.fieldReciprocal p)=17/4 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  simp only [LaurentPoleField.fieldReciprocal,PowerSeries.coeff_mk]
  constructor
  · norm_num only [Nat.reduceAdd,pow_one]
    field_simp [h4,h15]
    ring
  · norm_num only [Nat.reduceAdd,pow_two]
    field_simp [h4,h15]
    ring

/-- The second reciprocal band includes its exact p-boundary coefficient. -/
theorem original_reciprocal_two_bands (hp : 19≤p) (k : ℕ) (hk : k<2*p) :
    PowerSeries.coeff k (LaurentPoleField.fieldReciprocal p^(p+1))=
      PowerSeries.coeff k (LaurentPoleField.fieldReciprocal p)+
        if p≤k then (17/4 : ZMod p)*
          PowerSeries.coeff (k-p) (LaurentPoleField.fieldReciprocal p) else 0 := by
  classical
  by_cases hpk : p≤k
  · let F := LaurentPoleField.fieldReciprocal p
    have hfirst : PowerSeries.coeff 0 F=1 ∧ PowerSeries.coeff 1 F=17/4 :=
      original_reciprocal_first_coefficients p hp
    have hterm (j : ℕ) (hj : j∈Finset.range (k+1)) :
        PowerSeries.coeff j (PowerSeries.expand p (by omega) F)*
            PowerSeries.coeff (k-j) F=
          (if j=0 then PowerSeries.coeff k F else 0)+
          (if j=p then (17/4 : ZMod p)*PowerSeries.coeff (k-p) F else 0) := by
      by_cases hj0 : j=0
      · subst j
        simp only [PowerSeries.coeff_expand,dvd_zero,if_true,Nat.zero_div,
          Nat.sub_zero,hfirst.1,one_mul,if_neg (by omega : ¬0=p),add_zero]
      by_cases hjp : j=p
      · subst j
        simp only [PowerSeries.coeff_expand,dvd_refl,if_true,Nat.div_self (by omega : 0<p),
          hfirst.2,if_neg (by omega : ¬p=0),zero_add]
      · have hnot : ¬p∣j := by
          intro hd
          obtain ⟨q,hq⟩ := hd
          have hjlt : j<2*p := by have := Finset.mem_range.mp hj; omega
          have hq2 : q<2 := by
            by_contra hq2
            have hmul : p*2≤p*q := Nat.mul_le_mul_left p (by omega)
            omega
          have hq01 : q=0 ∨ q=1 := by omega
          rcases hq01 with hzero | hone
          · exact hj0 (by simpa only [hzero,mul_zero] using hq)
          · exact hjp (by simpa only [hone,mul_one] using hq)
        rw [PowerSeries.coeff_expand_of_not_dvd p (by omega) _ hnot]
        simp only [zero_mul,if_neg hj0,if_neg hjp,add_zero]
    have hsplit := LaurentPoleField.reciprocal_frobenius_split p 1 1 hp
    simp only [Nat.mul_one,pow_one] at hsplit
    rw [hsplit,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    change (∑ j∈Finset.range (k+1), PowerSeries.coeff j
      (PowerSeries.expand p (by omega) F)*PowerSeries.coeff (k-j) F)=_
    rw [Finset.sum_congr rfl hterm]
    simp only [F,Finset.sum_add_distrib,Finset.sum_ite_eq',
      Finset.mem_range,if_pos (by omega : 0<k+1),if_pos (by omega : p<k+1),if_pos hpk]
  · rw [reciprocal_first_band p k hp (by omega),if_neg hpk,add_zero]

/-- Signed coefficient extraction retains the whole original two reciprocal bands. -/
theorem original_signed_reciprocal_two_bands (hp : 19≤p) (k : ℤ)
    (hk : k<2*(p : ℤ)) :
    LaurentPoleField.fieldZcoeff p k (LaurentPoleField.fieldReciprocal p^(p+1))=
      LaurentPoleField.fieldZcoeff p k (LaurentPoleField.fieldReciprocal p)+
      (17/4 : ZMod p)*LaurentPoleField.fieldZcoeff p (k-(p : ℤ))
        (LaurentPoleField.fieldReciprocal p) := by
  by_cases h0 : 0≤k
  · have hkNat : k.toNat<2*p := by have := Int.toNat_of_nonneg h0; omega
    rw [LaurentPoleField.fieldZcoeff,if_pos h0,
      original_reciprocal_two_bands p hp k.toNat hkNat]
    by_cases hpk : (p : ℤ)≤k
    · have hpkNat : p≤k.toNat := by have := Int.toNat_of_nonneg h0; omega
      have hsub : (k-(p : ℤ)).toNat=k.toNat-p := by
        have := Int.toNat_of_nonneg h0
        have := Int.toNat_of_nonneg (by omega : 0≤k-(p : ℤ))
        omega
      simp only [if_pos hpkNat,LaurentPoleField.fieldZcoeff,
        if_pos (by omega : 0≤k-(p : ℤ)),hsub]
    · have hpkNat : ¬p≤k.toNat := by have := Int.toNat_of_nonneg h0; omega
      simp only [if_neg hpkNat,LaurentPoleField.fieldZcoeff,
        if_neg (by omega : ¬0≤k-(p : ℤ)),LinearMap.zero_apply,mul_zero]
  · simp only [LaurentPoleField.fieldZcoeff,if_neg h0,
      if_neg (by omega : ¬0≤k-(p : ℤ)),LinearMap.zero_apply,mul_zero,add_zero]

/-- The original high-pole weight has the additional reciprocal band needed by P squared. -/
theorem original_weight_two_bands (hp : 19≤p) (n : ℤ) (hn : n<4*(p : ℤ)+1) :
    LaurentPoleField.fieldWeight p (p+1) n=
      -(1/4 : ZMod p)*LaurentPoleField.fieldWeight p 1 (n-2*(p : ℤ))-
      (17/16 : ZMod p)*LaurentPoleField.fieldWeight p 1 (n-3*(p : ℤ)) := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have hscale : (-1/4 : ZMod p)^(p+1)=1/16 := by
    rw [pow_succ,ZMod.pow_card]
    field_simp [h4,h16]
    ring
  simp only [LaurentPoleField.fieldWeight,pow_one]
  rw [hscale,show n-(2*((p+1 : ℕ) : ℤ)-1)=n-2*(p : ℤ)-1 by omega,
    original_signed_reciprocal_two_bands p hp _ (by omega)]
  rw [show n-2*(p : ℤ)-1-(p : ℤ)=n-3*(p : ℤ)-1 by ring]
  field_simp [h4,h16]
  ring

theorem original_dlog_two_bands (hp : 19≤p) (n : ℤ) (hn : n<4*(p : ℤ)+1)
    (c : ZMod p) :
    LaurentPoleField.fieldTrace p (p+1)
      (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))=
      -(1/4 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-2*(p : ℤ)))-
      (17/16 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-3*(p : ℤ))) := by
  change _= -(1/4 : ZMod p)*LaurentPoleField.fieldTrace p 1
    (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T (n-2*(p : ℤ))))-
    (17/16 : ZMod p)*LaurentPoleField.fieldTrace p 1
      (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T (n-3*(p : ℤ))))
  rw [literal_density_monomial,literal_density_monomial,literal_density_monomial,
    map_sub,map_sub,map_sub,LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,
    original_weight_two_bands p hp (n-1) (by omega),original_weight_two_bands p hp n hn]
  rw [show n-1-2*(p : ℤ)=n-2*(p : ℤ)-1 by ring,
    show n-1-3*(p : ℤ)=n-3*(p : ℤ)-1 by ring]
  ring

/-- All three positive windows are necessary for the original P-square carrier. -/
theorem original_weight_third_band (hp : 19≤p) (n : ℤ) (hn : n<3*(p : ℤ))
    (c : ZMod p) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c*T n)=
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (LaurentPolynomial.C c*T n)-
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (LaurentPolynomial.C c*T (n-(p : ℤ)))-
      (129/8 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (LaurentPolynomial.C c*T (n-2*(p : ℤ))) := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have hshift : (T (p : ℤ) : (ZMod p)[T;T⁻¹])*(LaurentPolynomial.C c*T n)=
      LaurentPolynomial.C c*T (n+(p : ℤ)) := by
    rw [mul_comm (T (p : ℤ)),mul_assoc,←T_add]
  have hclear := LaurentPoleField.fieldTrace_cleared_pow p 1 p hp
    (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))
  rw [show 1+p=p+1 by omega] at hclear
  have hz : fieldDlogQ p (LaurentPolynomial.C c*T (n-3*(p : ℤ)))=0 := by
    rw [fieldDlogQ_monomial p hp,endpointWeight,if_neg (by omega),mul_zero]
  unfold originalWeightedFieldTrace
  rw [original_weight_numerator_split]
  rw [show ((-3*(LaurentPoleField.fieldAbar p).toLaurent^p+18*T (p : ℤ)-12)*
      (3*T (-1)*(4-11*T 1)))*(LaurentPolynomial.C c*T n)=
      LaurentPolynomial.C (-3 : ZMod p)*
        ((LaurentPoleField.fieldAbar p).toLaurent^p*
          (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n)))+
      LaurentPolynomial.C (18 : ZMod p)*
        (3*T (-1)*(4-11*T 1)*(T (p : ℤ)*(LaurentPolynomial.C c*T n)))-
      LaurentPolynomial.C (12 : ZMod p)*
        (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n)) by
      simp only [map_neg,map_ofNat]
      ring]
  rw [map_sub,map_add,fieldTrace_C_mul,fieldTrace_C_mul,fieldTrace_C_mul,
    hclear,hshift,original_dlog_two_bands p hp (n+(p : ℤ)) (by omega) c,
    original_dlog_two_bands p hp n (by omega) c]
  rw [show n+(p : ℤ)-2*(p : ℤ)=n-(p : ℤ) by ring,
    show n+(p : ℤ)-3*(p : ℤ)=n-2*(p : ℤ) by ring,hz]
  change -(3 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T n)+
    18*(-(1/4 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-(p : ℤ)))-
      (17/16 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-2*(p : ℤ))))-
    12*(-(1/4 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-2*(p : ℤ)))-
      (17/16 : ZMod p)*0)=_
  rw [fieldDlogQ_endpoint p hp,fieldDlogQ_endpoint p hp,fieldDlogQ_endpoint p hp]
  field_simp [h2,h4,h8,h16]
  ring

/-- Coefficient reconstruction preserves every negative exponent and the third positive window. -/
theorem original_weight_above_third_band (hp : 19≤p) (F : (ZMod p)[T;T⁻¹])
    (hF : Above F (3*(p : ℤ)-1)) :
    originalWeightedFieldTrace p F=
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 F-
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*F)-
      (129/8 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-2*(p : ℤ))*F) := by
  classical
  have hs : (∑ n∈F.coeff.support, LaurentPolynomial.C (F.coeff n)*T n)=F := by
    simpa only [Finsupp.sum,single_eq_C_mul_T] using AddMonoidAlgebra.sum_coeff_single F
  have hshift (s n : ℤ) : (T s : (ZMod p)[T;T⁻¹])*
      (LaurentPolynomial.C (F.coeff n)*T n)=LaurentPolynomial.C (F.coeff n)*T (n+s) := by
    rw [mul_comm (T s),mul_assoc,←T_add]
  rw [←hs]
  simp only [originalWeightedFieldTrace,Finset.mul_sum,map_sum,hshift,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnonzero : F.coeff n≠0 := Finsupp.mem_support_iff.mp hn
  have hlt : n<3*(p : ℤ) := by
    by_contra hnot
    exact hnonzero (hF n (by omega))
  simpa only [originalWeightedFieldTrace,sub_eq_add_neg,neg_mul] using
    original_weight_third_band p hp n hlt (F.coeff n)

end WPFieldAssembly.SourceClosureUVThirdBand
