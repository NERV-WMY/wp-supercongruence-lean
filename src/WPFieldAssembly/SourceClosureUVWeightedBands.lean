import WPFieldAssembly.SourceClosureUVPhaseTrace

open scoped LaurentPolynomial PowerSeries
open LaurentPolynomial WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace

namespace WPFieldAssembly.SourceClosureUVWeightedBands

open WPFiniteLaurentDifferential

set_option maxHeartbeats 1600000

/- UW18a is derived from the original quadratic denominator. The bound
   applies to the largest Laurent exponent; all negative exponents remain. -/

theorem original_A_power (p : ℕ) [Fact p.Prime] :
    (A : (ZMod p)[T;T⁻¹])^p = -4*T (2*(p : ℤ))+17*T (p : ℤ)-4 := by
    have hC : Function.Injective (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) := by
      intro a b hab
      have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff 0) hab
      simpa only [LaurentPolynomial.C_apply,if_true] using he
    have : CharP (ZMod p)[T;T⁻¹] p :=
      charP_of_injective_ringHom (f:=LaurentPolynomial.C) hC p
    change ((LaurentPolynomial.C (4 : ZMod p)*T 1-1)*
      (LaurentPolynomial.C (4 : ZMod p)-T 1))^p = _
    rw [mul_pow, sub_pow_char (p:=p), sub_pow_char (p:=p), mul_pow,
      ←map_pow, ZMod.pow_card, one_pow]
    simp only [T_pow, mul_one, map_ofNat]
    have ht : (T (p : ℤ) : (ZMod p)[T;T⁻¹])^2=T (2*(p : ℤ)) := by
      rw [T_pow]
      norm_num
    rw [←ht]
    ring

theorem original_weight_numerator_split (p : ℕ) [Fact p.Prime] :
    3*(R : (ZMod p)[T;T⁻¹])^p =
      -3*(LaurentPoleField.fieldAbar p).toLaurent^p+18*T (p : ℤ)-12 := by
  rw [original_R_power, ←field_A, original_A_power]
  ring

theorem original_weight_shift (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n<2*(p : ℤ)) :
    LaurentPoleField.fieldWeight p (p+1) (n+(p : ℤ)) =
      -(1/4 : ZMod p)*LaurentPoleField.fieldWeight p 1 (n-(p : ℤ)) := by
  have he : n+(p : ℤ)-(2*((p+1 : ℕ) : ℤ)-1)=n-(p : ℤ)-1 := by omega
  have he' : n-(p : ℤ)-(2*((1 : ℕ) : ℤ)-1)=n-(p : ℤ)-1 := by omega
  rw [LaurentPoleField.fieldWeight, LaurentPoleField.fieldWeight, he, he']
  have hscale : (-1/4 : ZMod p)^(p+1)=(-1/4 : ZMod p)*(-1/4) := by
    rw [pow_succ, ZMod.pow_card]
  rw [hscale]
  by_cases h0 : 0≤n-(p : ℤ)-1
  · simp only [LaurentPoleField.fieldZcoeff, if_pos h0, pow_one]
    rw [reciprocal_first_band p (n-(p : ℤ)-1).toNat hp (by
      have ht := Int.toNat_of_nonneg h0
      omega)]
    ring
  · simp only [LaurentPoleField.fieldZcoeff, if_neg h0, LinearMap.zero_apply, mul_zero]

theorem dlog_high_pole_vanish (p : ℕ) [Fact p.Prime]
    (n : ℤ) (hn : n≤2*(p : ℤ)) (c : ZMod p) :
    LaurentPoleField.fieldTrace p (p+1)
      (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))=0 := by
  rw [literal_density_monomial, map_sub, LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,
    weight_below_cutoff p (p+1) (n-1) (by omega),
    weight_below_cutoff p (p+1) n (by omega)]
  ring

theorem dlog_shift_high_pole (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n<2*(p : ℤ)) (c : ZMod p) :
    LaurentPoleField.fieldTrace p (p+1)
      (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T (n+(p : ℤ)))) =
      -(1/4 : ZMod p)*fieldDlogQ p
        (LaurentPolynomial.C c*T (n-(p : ℤ))) := by
  change _ = -(1/4 : ZMod p)*LaurentPoleField.fieldTrace p 1
    (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T (n-(p : ℤ))))
  rw [literal_density_monomial, literal_density_monomial,
    map_sub, map_sub, LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial, LaurentPoleField.fieldTrace_monomial,
    LaurentPoleField.fieldTrace_monomial,
    show n+(p : ℤ)-1=(n-1)+(p : ℤ) by omega,
    original_weight_shift p hp (n-1) (by omega),
    original_weight_shift p hp n hn]
  rw [show n-1-(p : ℤ)=n-(p : ℤ)-1 by omega]
  ring

/-- The entire original Frobenius weight acts on both positive windows. -/
theorem original_weight_monomial (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (n : ℤ) (hn : n<2*(p : ℤ)) (c : ZMod p) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c*T n) =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (LaurentPolynomial.C c*T n) -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (LaurentPolynomial.C c*T (n-(p : ℤ))) := by
  have hshift : (T (p : ℤ) : (ZMod p)[T;T⁻¹])*
      (LaurentPolynomial.C c*T n) = LaurentPolynomial.C c*T (n+(p : ℤ)) := by
    rw [mul_comm (T (p : ℤ)), mul_assoc, ←T_add]
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hclear : LaurentPoleField.fieldTrace p (p+1)
      ((LaurentPoleField.fieldAbar p).toLaurent^p*
        (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))) =
      LaurentPoleField.fieldTrace p 1
        (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n)) := by
    simpa only [Nat.add_comm] using LaurentPoleField.fieldTrace_cleared_pow p 1 p hp
      (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))
  unfold originalWeightedFieldTrace
  rw [original_weight_numerator_split]
  rw [show ((-3*(LaurentPoleField.fieldAbar p).toLaurent^p+18*T (p : ℤ)-12)*
      (3*T (-1)*(4-11*T 1)))*(LaurentPolynomial.C c*T n) =
      LaurentPolynomial.C (-3 : ZMod p)*
        ((LaurentPoleField.fieldAbar p).toLaurent^p*
          (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n))) +
      LaurentPolynomial.C (18 : ZMod p)*
        (3*T (-1)*(4-11*T 1)*(T (p : ℤ)*(LaurentPolynomial.C c*T n))) -
      LaurentPolynomial.C (12 : ZMod p)*
        (3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C c*T n)) by
        simp only [map_neg, map_ofNat]
        ring]
  rw [map_sub, map_add, fieldTrace_C_mul, fieldTrace_C_mul, fieldTrace_C_mul,
    hclear, hshift,
    dlog_shift_high_pole p hp n hn c, dlog_high_pole_vanish p n (by omega) c]
  change -(3 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T n) +
    18*(-(1/4 : ZMod p)*fieldDlogQ p (LaurentPolynomial.C c*T (n-(p : ℤ))))-
    12*0 = _
  rw [fieldDlogQ_endpoint p hp, fieldDlogQ_endpoint p hp]
  field_simp [h2,h4]
  ring

/-- No lower Laurent cutoff is imposed or silently inferred. -/
theorem original_weight_full_band (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (I : Finset ℤ) (e : ℤ → ZMod p) (hI : ∀ n∈I, n<2*(p : ℤ)) :
    originalWeightedFieldTrace p (∑ n∈I, LaurentPolynomial.C (e n)*T n) =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (∑ n∈I, LaurentPolynomial.C (e n)*T n) -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4
        (T (-(p : ℤ))*(∑ n∈I, LaurentPolynomial.C (e n)*T n)) := by
  have hshift (n : ℤ) : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*
      (LaurentPolynomial.C (e n)*T n) = LaurentPolynomial.C (e n)*T (n-(p : ℤ)) := by
    rw [mul_comm (T (-(p : ℤ))), mul_assoc, ←T_add]
    congr 1
  simp only [originalWeightedFieldTrace, Finset.mul_sum, map_sum, hshift,
    Finset.mul_sum, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact original_weight_monomial p hp n (hI n hn) (e n)

/-- Coefficient reconstruction applies the same whole window to an actual Laurent carrier. -/
theorem original_weight_above (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) (hF : Above F (2*(p : ℤ)-1)) :
    originalWeightedFieldTrace p F =
      -(3 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 F -
      (9/2 : ZMod p)*endpointTrace (1/4 : ZMod p) 4 (T (-(p : ℤ))*F) := by
  have hs : (∑ n∈F.coeff.support, LaurentPolynomial.C (F.coeff n)*T n)=F := by
    simpa only [Finsupp.sum,single_eq_C_mul_T] using
      AddMonoidAlgebra.sum_coeff_single F
  have hI : ∀ n∈F.coeff.support, n<2*(p : ℤ) := by
    intro n hn
    by_contra he
    exact (Finsupp.mem_support_iff.mp hn) (hF n (by omega))
  simpa only [hs] using original_weight_full_band p hp F.coeff.support F.coeff hI

end WPFieldAssembly.SourceClosureUVWeightedBands
