import WPFieldAssembly.LaurentPoleIntegral
import Mathlib.RingTheory.PowerSeries.Expand

open scoped Polynomial LaurentPolynomial PowerSeries BigOperators
open WPPIntegralReduction

namespace WPFieldAssembly.LaurentPoleField

noncomputable def fieldReciprocal (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ :=
  PowerSeries.mk fun k => (4/15 : ZMod p)*(4^(k+1)-(1/4 : ZMod p)^(k+1))

noncomputable def reciprocalIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)⟦X⟧ :=
  PowerSeries.mk fun k =>
    ⟨(4/15 : ℚ)*(4^(k+1)-(1/4 : ℚ)^(k+1)),
      LaurentPoleIntegral.literal_reciprocal_integral p k hp⟩

theorem cast_quarter (p : ℕ) [Fact p.Prime] :
    ((1/4 : ℚ) : ZMod p) = (1/4 : ZMod p) := by
  norm_num [Rat.cast_def]

theorem cast_four_fifteenths (p : ℕ) [Fact p.Prime] :
    ((4/15 : ℚ) : ZMod p) = (4/15 : ZMod p) := by
  norm_num [Rat.cast_def]

theorem literal_reciprocal_reduce (p k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (((4/15 : ℚ)*(4^(k+1)-(1/4 : ℚ)^(k+1)) : ℚ) : ZMod p) =
      (4/15 : ZMod p)*(4^(k+1)-(1/4 : ZMod p)^(k+1)) := by
  have h4 : (4 : ℚ)^(k+1) ∈ integralRationals p :=
    (integralRationals p).pow_mem (natCast_mem (integralRationals p) 4) (k+1)
  have hquarter := (integralRationals p).pow_mem
    (LaurentPoleIntegral.quarter_integral p hp) (k+1)
  rw [Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p _ (LaurentPoleIntegral.four_fifteenths_integral p hp))
    (integral_denominator_cast_ne_zero p _ ((integralRationals p).sub_mem h4 hquarter)),
    Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p _ h4)
      (integral_denominator_cast_ne_zero p _ hquarter),
    cast_four_fifteenths, Rat.cast_pow, Rat.cast_pow, cast_quarter, Rat.cast_ofNat]

theorem reciprocalIntegral_map_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.map (integralRationals p).subtype (reciprocalIntegral p hp) =
      LaurentPoleTrace.reciprocal := by
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map, reciprocalIntegral, LaurentPoleTrace.reciprocal,
    PowerSeries.coeff_mk, Subring.coe_subtype]

theorem reciprocalIntegral_map_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.map (residueHom p) (reciprocalIntegral p hp) = fieldReciprocal p := by
  apply PowerSeries.ext
  intro k
  simp only [PowerSeries.coeff_map, reciprocalIntegral, fieldReciprocal, PowerSeries.coeff_mk]
  exact literal_reciprocal_reduce p k hp

/-- Every power coefficient is reduced through the proved integral residue homomorphism. -/
theorem reciprocal_power_coeff_reduce (p m k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((PowerSeries.coeff k (LaurentPoleTrace.reciprocal^m) : ℚ) : ZMod p) =
      PowerSeries.coeff k (fieldReciprocal p^m) := by
  have hQ := congrArg (PowerSeries.coeff k)
    (show PowerSeries.map (integralRationals p).subtype (reciprocalIntegral p hp^m) =
      LaurentPoleTrace.reciprocal^m by rw [map_pow, reciprocalIntegral_map_rational])
  have hF := congrArg (PowerSeries.coeff k)
    (show PowerSeries.map (residueHom p) (reciprocalIntegral p hp^m) =
      fieldReciprocal p^m by rw [map_pow, reciprocalIntegral_map_residue])
  rw [PowerSeries.coeff_map] at hQ hF
  change ((PowerSeries.coeff k (reciprocalIntegral p hp^m)).val : ℚ) = _ at hQ
  change (((PowerSeries.coeff k (reciprocalIntegral p hp^m)).val : ℚ) : ZMod p) = _ at hF
  rw [hQ] at hF
  exact hF

noncomputable def fieldZcoeff (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (ZMod p)⟦X⟧ →ₗ[ZMod p] ZMod p :=
  if 0 ≤ n then PowerSeries.coeff n.toNat else 0

theorem zcoeff_power_reduce (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    ((LaurentPoleTrace.zcoeff n (LaurentPoleTrace.reciprocal^m) : ℚ) : ZMod p) =
      fieldZcoeff p n (fieldReciprocal p^m) := by
  by_cases hn : 0 ≤ n
  · simp only [LaurentPoleTrace.zcoeff, fieldZcoeff, if_pos hn]
    exact reciprocal_power_coeff_reduce p m n.toNat hp
  · simp [LaurentPoleTrace.zcoeff, fieldZcoeff, hn]

noncomputable def fieldWeight (p m : ℕ) [Fact p.Prime] (n : ℤ) : ZMod p :=
  -(-1/4 : ZMod p)^m * fieldZcoeff p (n-(2*(m : ℤ)-1)) (fieldReciprocal p^m)

theorem weight_reduce (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    ((LaurentPoleTrace.weight m n : ℚ) : ZMod p) = fieldWeight p m n := by
  have hquarter : (-1/4 : ℚ) ∈ integralRationals p := by
    rw [show (-1/4 : ℚ) = -(1/4 : ℚ) by ring]
    exact (integralRationals p).neg_mem (LaurentPoleIntegral.quarter_integral p hp)
  have hscalar := (integralRationals p).neg_mem ((integralRationals p).pow_mem hquarter m)
  rw [LaurentPoleTrace.weight, Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p _ hscalar)
    (integral_denominator_cast_ne_zero p _ (LaurentPoleIntegral.zcoeff_power_integral p m hp _)),
    Rat.cast_neg, Rat.cast_pow, zcoeff_power_reduce p m hp _]
  have hc : ((-1/4 : ℚ) : ZMod p) = (-1/4 : ZMod p) := by norm_num [Rat.cast_def]
  rw [hc]
  rfl

noncomputable def fieldTrace (p m : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (Finsupp.linearCombination (ZMod p) (fieldWeight p m)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem fieldTrace_eq_sum (p m : ℕ) [Fact p.Prime] (P : (ZMod p)[T;T⁻¹]) :
    fieldTrace p m P = P.coeff.sum (fun n a => a*fieldWeight p m n) := by
  change Finsupp.linearCombination (ZMod p) (fieldWeight p m) P.coeff = _
  rw [Finsupp.linearCombination_apply]
  simp only [smul_eq_mul]

@[simp] theorem fieldTrace_monomial (p m : ℕ) [Fact p.Prime] (a : ZMod p) (n : ℤ) :
    fieldTrace p m (LaurentPolynomial.C a * LaurentPolynomial.T n) = a*fieldWeight p m n := by
  rw [←LaurentPolynomial.single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem trace_reduce (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (L : ℚ[T;T⁻¹])
    (hL : L ∈ WPActualEtaIntegrality.integralLaurent p) :
    ((LaurentPoleTrace.trace m L : ℚ) : ZMod p) = fieldTrace p m (reduceLaurent p L) := by
  classical
  have hterm (n : ℤ) (_ : n ∈ L.coeff.support) :
      L.coeff n * LaurentPoleTrace.weight m n ∈ integralRationals p :=
    (integralRationals p).mul_mem (hL n) (LaurentPoleIntegral.weight_integral p m hp n)
  rw [LaurentPoleTrace.trace_eq_sum, fieldTrace_eq_sum]
  unfold Finsupp.sum
  rw [cast_sum_integral p L.coeff.support _ hterm]
  change _ = (L.coeff.mapRange (fun q : ℚ => (q : ZMod p)) Rat.cast_zero).sum
    (fun n a => a*fieldWeight p m n)
  rw [Finsupp.sum_mapRange_index (by intro n; simp)]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro n _
  rw [Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ (hL n))
    (integral_denominator_cast_ne_zero p _ (LaurentPoleIntegral.weight_integral p m hp n)),
    weight_reduce p m hp n]

/-- Over the prime field the full series Frobenius fixes every coefficient. -/
theorem series_frobenius (p : ℕ) [Fact p.Prime] (hp0 : p ≠ 0) (F : (ZMod p)⟦X⟧) :
    F^p = PowerSeries.expand p hp0 F := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod p) p hp0 (f := F)
  simpa only [ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply,
    PowerSeries.expand] using h.symm

theorem reciprocal_frobenius_split (p m r : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fieldReciprocal p^(p*m+r) =
      PowerSeries.expand p (by omega) (fieldReciprocal p^m) * fieldReciprocal p^r := by
  rw [pow_add, Nat.mul_comm p m, pow_mul, series_frobenius]

theorem reciprocal_finite_recurrence (p m k : ℕ) [Fact p.Prime] :
    PowerSeries.coeff k (fieldReciprocal p^(m+1)) =
      ∑ q ∈ Finset.antidiagonal k, PowerSeries.coeff q.1 (fieldReciprocal p^m) *
        ((4/15 : ZMod p)*(4^(q.2+1)-(1/4 : ZMod p)^(q.2+1))) := by
  rw [pow_succ, PowerSeries.coeff_mul]
  simp only [fieldReciprocal, PowerSeries.coeff_mk]

theorem reciprocal_frobenius_coeff (p m r k : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.coeff k (fieldReciprocal p^(p*m+r)) =
      ∑ q ∈ Finset.antidiagonal k,
        (if p ∣ q.1 then PowerSeries.coeff (q.1/p) (fieldReciprocal p^m) else 0) *
          PowerSeries.coeff q.2 (fieldReciprocal p^r) := by
  rw [reciprocal_frobenius_split p m r hp, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [PowerSeries.coeff_expand]

theorem fieldZcoeff_expand_selected (p : ℕ) [Fact p.Prime] (hp0 : p ≠ 0)
    (F : (ZMod p)⟦X⟧) (k : ℤ) :
    fieldZcoeff p ((p : ℤ)*k) (PowerSeries.expand p hp0 F) = fieldZcoeff p k F := by
  by_cases hk : 0 ≤ k
  · have hpk : 0 ≤ (p : ℤ)*k := mul_nonneg (Int.natCast_nonneg p) hk
    have hc : (((p : ℤ)*k).toNat : ℤ) = ((p*k.toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpk, Nat.cast_mul, Int.toNat_of_nonneg hk]
    have he : ((p : ℤ)*k).toNat = p*k.toNat := by exact_mod_cast hc
    simp only [fieldZcoeff, if_pos hpk, if_pos hk, he, PowerSeries.coeff_expand_mul]
  · have hpk : (p : ℤ)*k < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast (Fact.out : p.Prime).pos) (by omega)
    simp [fieldZcoeff, hk, not_le.mpr hpk]

theorem fieldZcoeff_expand_unselected (p : ℕ) [Fact p.Prime] (hp0 : p ≠ 0)
    (F : (ZMod p)⟦X⟧) (n : ℤ) (hn : ¬(p : ℤ) ∣ n) :
    fieldZcoeff p n (PowerSeries.expand p hp0 F) = 0 := by
  by_cases h0 : 0 ≤ n
  · have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h0
    have hnot : ¬p ∣ n.toNat := by
      intro h
      apply hn
      simpa only [he] using (show (p : ℤ) ∣ (n.toNat : ℤ) by exact_mod_cast h)
    simp only [fieldZcoeff, if_pos h0, PowerSeries.coeff_expand_of_not_dvd p hp0 F hnot]
  · simp [fieldZcoeff, h0]

theorem frobenius_normalization (p m : ℕ) [Fact p.Prime] :
    (-1/4 : ZMod p)^(p*m) = (-1/4 : ZMod p)^m := by
  rw [pow_mul, ZMod.pow_card]

/-- Differential selection is n=p*k+(p-1), with the original minus residue convention. -/
theorem fieldWeight_selected (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (k : ℤ) :
    fieldWeight p (p*m) ((p : ℤ)*(k+1)-1) = fieldWeight p m k := by
  have hF := reciprocal_frobenius_split p m 0 hp
  simp only [Nat.add_zero, pow_zero, mul_one] at hF
  have hn : (p : ℤ)*(k+1)-1-(2*((p*m : ℕ) : ℤ)-1) =
      (p : ℤ)*(k-(2*(m : ℤ)-1)) := by push_cast; ring
  rw [fieldWeight, fieldWeight, hn, hF, fieldZcoeff_expand_selected,
    frobenius_normalization]

theorem fieldWeight_unselected (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (n : ℤ) (hn : ¬(p : ℤ) ∣ n+1) : fieldWeight p (p*m) n = 0 := by
  have hF := reciprocal_frobenius_split p m 0 hp
  simp only [Nat.add_zero, pow_zero, mul_one] at hF
  have hnot : ¬(p : ℤ) ∣ n-(2*((p*m : ℕ) : ℤ)-1) := by
    rintro ⟨b, hb⟩
    apply hn
    refine ⟨b+2*(m : ℤ), ?_⟩
    push_cast at hb ⊢
    linear_combination hb
  rw [fieldWeight, hF, fieldZcoeff_expand_unselected p _ _ _ hnot, mul_zero]

theorem trace_frobenius_cartier (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[T;T⁻¹]) :
    fieldTrace p (p*m) P =
      fieldTrace p m (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [WPFiniteCartier.cartier_add, map_add, map_add, hP, hQ]
  | C_mul_T n a =>
    rw [fieldTrace_monomial]
    by_cases hn : (p : ℤ) ∣ n+1
    · let k := (n+1)/(p : ℤ)-1
      have he : n = (p : ℤ)*(k+1)-1 := by
        have h := Int.mul_ediv_cancel' hn
        dsimp only [k]
        linear_combination -h
      rw [he, WPFiniteCartier.cartier_selected_monomial, fieldTrace_monomial,
        fieldWeight_selected p m hp k]
    · rw [WPFiniteCartier.cartier_unselected_monomial p _ _ _ hn, map_zero,
        fieldWeight_unselected p m hp n hn, mul_zero]

noncomputable def integralWeight (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    integralRationals p :=
  ⟨LaurentPoleTrace.weight m n, LaurentPoleIntegral.weight_integral p m hp n⟩

theorem integralWeight_residue (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    residueHom p (integralWeight p m hp n) = fieldWeight p m n :=
  weight_reduce p m hp n

/-- Clearing the denominator is transported through the actual integral residue hom. -/
theorem fieldWeight_cleared (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (n : ℤ) :
    -4*fieldWeight p (m+1) (n+2)+17*fieldWeight p (m+1) (n+1)-
      4*fieldWeight p (m+1) n = fieldWeight p m n := by
  have hR : (-4 : integralRationals p)*integralWeight p (m+1) hp (n+2)+
      17*integralWeight p (m+1) hp (n+1)-4*integralWeight p (m+1) hp n =
        integralWeight p m hp n := by
    apply Subtype.ext
    change -4*LaurentPoleTrace.weight (m+1) (n+2)+
      17*LaurentPoleTrace.weight (m+1) (n+1)-4*LaurentPoleTrace.weight (m+1) n =
        LaurentPoleTrace.weight m n
    exact LaurentPoleTrace.weight_cleared m n
  have h := congrArg (residueHom p) hR
  simpa only [map_sub, map_add, map_mul, map_neg, map_ofNat,
    integralWeight_residue] using h

noncomputable def fieldAbar (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (4*Polynomial.X-1)*(4-Polynomial.X)

theorem fieldAbar_laurent (p : ℕ) [Fact p.Prime] :
    (fieldAbar p).toLaurent = -4*LaurentPolynomial.T 2+17*LaurentPolynomial.T 1-4 := by
  simp only [fieldAbar, map_mul, map_sub, map_ofNat, map_one, Polynomial.toLaurent_X]
  have h2 : (LaurentPolynomial.T 2 : (ZMod p)[T;T⁻¹])=LaurentPolynomial.T 1^2 := by
    rw [LaurentPolynomial.T_pow]
    norm_num
  rw [h2]
  ring

theorem fieldTrace_cleared (p m : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[T;T⁻¹]) :
    fieldTrace p (m+1) ((fieldAbar p).toLaurent*P) = fieldTrace p m P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
  | C_mul_T n a =>
    have h2 : (LaurentPolynomial.T 2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.T n =
        LaurentPolynomial.T (n+2) := by
      rw [←LaurentPolynomial.T_add]
      congr 1
      omega
    have h1 : (LaurentPolynomial.T 1 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.T n =
        LaurentPolynomial.T (n+1) := by
      rw [←LaurentPolynomial.T_add]
      congr 1
      omega
    have he : (fieldAbar p).toLaurent*(LaurentPolynomial.C a*LaurentPolynomial.T n) =
        LaurentPolynomial.C (-4*a)*LaurentPolynomial.T (n+2)+
          LaurentPolynomial.C (17*a)*LaurentPolynomial.T (n+1)+
          LaurentPolynomial.C (-4*a)*LaurentPolynomial.T n := by
      rw [fieldAbar_laurent]
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination -4*LaurentPolynomial.C a*h2+17*LaurentPolynomial.C a*h1
    rw [he, map_add, map_add, fieldTrace_monomial, fieldTrace_monomial,
      fieldTrace_monomial, fieldTrace_monomial]
    linear_combination a*fieldWeight_cleared p m hp n

theorem fieldTrace_cleared_pow (p m r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[T;T⁻¹]) :
    fieldTrace p (m+r) ((fieldAbar p).toLaurent^r*P) = fieldTrace p m P := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.add_succ,
      show (fieldAbar p).toLaurent^(r+1)*P =
        (fieldAbar p).toLaurent*((fieldAbar p).toLaurent^r*P) by ring,
      fieldTrace_cleared p (m+r) hp _, ih]

theorem fieldTrace_common_denominator (p a b : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P Q : (ZMod p)[T;T⁻¹])
    (h : (fieldAbar p).toLaurent^b*P = (fieldAbar p).toLaurent^a*Q) :
    fieldTrace p a P = fieldTrace p b Q := by
  calc
    fieldTrace p a P = fieldTrace p (a+b) ((fieldAbar p).toLaurent^b*P) :=
      (fieldTrace_cleared_pow p a b hp P).symm
    _ = fieldTrace p (a+b) ((fieldAbar p).toLaurent^a*Q) := congrArg (fieldTrace p (a+b)) h
    _ = fieldTrace p b Q := by
      rw [Nat.add_comm a b]
      exact fieldTrace_cleared_pow p b a hp Q

end WPFieldAssembly.LaurentPoleField
