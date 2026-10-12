import WPFieldAssembly.ActualEntropyEndpoints
import WPFieldAssembly.ActualCubicHarmonicCarry
import WPFieldAssembly.ActualHarmonicReflection

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry WPFieldAssembly.ActualEntropyEndpoints
  WPFieldAssembly.ActualCubicHarmonicCarry WPFieldAssembly.ActualHarmonicReflection

namespace WPFieldAssembly.ActualProperHarmonicCarry

set_option maxHeartbeats 1400000

theorem rationalHarmonic_Ico (n : ℕ) :
    rationalHarmonic n=∑ j ∈ Finset.Ico 1 (n+1), 1/(j : ℚ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, rationalHarmonic, Nat.add_comm]

noncomputable def reflectedCarryIntegral (p n : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ Finset.Ico 1 (n+1), smallIntegralInverse p j*smallIntegralInverse p (p-j)

noncomputable def oddBandCarryIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1),
    smallIntegralInverse p j*smallIntegralInverse p (p-2*j)

theorem reflectedCarryIntegral_value (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    (reflectedCarryIntegral p n).val=
      ∑ j ∈ Finset.Ico 1 (n+1), 1/((j : ℚ)*((p-j : ℕ) : ℚ)) := by
  change (integralRationals p).subtype (reflectedCarryIntegral p n)=_
  rw [reflectedCarryIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [map_mul]
  change (smallIntegralInverse p j).val*(smallIntegralInverse p (p-j)).val=_
  rw [smallIntegralInverse_value p j (by omega) (by omega),
    smallIntegralInverse_value p (p-j) (by omega) (by omega)]
  simp only [one_div, mul_inv_rev]
  ring

/-- The reflected finite suffix is expanded before the first p division. -/
theorem rationalHarmonic_reflection (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    rationalHarmonic (p-1-n)=rationalHarmonic (p-1)+rationalHarmonic n-
      (p : ℚ)*(reflectedCarryIntegral p n).val := by
  have hs := Finset.sum_Ico_consecutive (fun j => 1/(j : ℚ))
    (by omega : 1 ≤ p-n) (by omega : p-n ≤ p)
  have hr := Finset.sum_Ico_reflect (fun j => 1/(j : ℚ)) 1
    (m := n+1) (n := p) (by omega)
  rw [show p+1-(n+1)=p-n by omega, show p+1-1=p by omega] at hr
  have he : (∑ j ∈ Finset.Ico 1 (n+1), 1/((p-j : ℕ) : ℚ))=
      -rationalHarmonic n+(p : ℚ)*(reflectedCarryIntegral p n).val := by
    rw [rationalHarmonic_Ico, reflectedCarryIntegral_value p n hn,
      Finset.mul_sum, ←Finset.sum_neg_distrib, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have hr0 : ((p-j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : p-j ≠ 0)
    rw [Nat.cast_sub (by omega : j ≤ p)]
    rw [Nat.cast_sub (by omega : j ≤ p)] at hr0
    field_simp [hj0, hr0]
    ring
  rw [←hr, he] at hs
  have hK : (∑ j ∈ Finset.Ico 1 (p-n), 1/(j : ℚ))=rationalHarmonic (p-1-n) := by
    rw [rationalHarmonic_Ico, show p-1-n+1=p-n by omega]
  have hP : (∑ j ∈ Finset.Ico 1 p, 1/(j : ℚ))=rationalHarmonic (p-1) := by
    rw [rationalHarmonic_Ico, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [hK, hP] at hs
  linear_combination hs

theorem rationalHarmonic_full_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rationalHarmonic (p-1)=
      (p : ℚ)*(reflectedCarryIntegral p ((p-1)/2)).val := by
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have h := rationalHarmonic_reflection p ((p-1)/2) (by omega)
  rw [show p-1-(p-1)/2=(p-1)/2 by omega] at h
  linear_combination -h

private theorem rational_odd_harmonic (n : ℕ) :
    (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => ¬2 ∣ j), 1/(j : ℚ))=
      rationalHarmonic n-rationalHarmonic (n/2)/2 := by
  have he : (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => 2 ∣ j), 1/(j : ℚ))=
      rationalHarmonic (n/2)/2 := by
    rw [WPActualPartialHarmonic.even_filter_sum, rationalHarmonic_Ico, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hs : (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => 2 ∣ j), 1/(j : ℚ))+
      (∑ j ∈ (Finset.Ico 1 (n+1)).filter (fun j => ¬2 ∣ j), 1/(j : ℚ))=
        rationalHarmonic n := by
    rw [rationalHarmonic_Ico, Finset.sum_filter, Finset.sum_filter, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 2 ∣ j <;> simp only [h, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, add_zero, zero_add]
  rw [he] at hs
  linear_combination hs

theorem oddBandCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (oddBandCarryIntegral p).val=
      ∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1),
        1/((j : ℚ)*((p-2*j : ℕ) : ℚ)) := by
  change (integralRationals p).subtype (oddBandCarryIntegral p)=_
  rw [oddBandCarryIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  rw [map_mul]
  change (smallIntegralInverse p j).val*(smallIntegralInverse p (p-2*j)).val=_
  rw [smallIntegralInverse_value p j (by omega) (by omega),
    smallIntegralInverse_value p (p-2*j) (by omega) (by omega)]
  simp only [one_div, mul_inv_rev]
  ring

/-- This identity retains both reflected remainders and the entire odd band. -/
theorem rationalHarmonic_sixth_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rationalHarmonic (p/6)=rationalHarmonic ((p-1)/2)+rationalHarmonic (p/3)+
      2*rationalHarmonic (p-1)-(p : ℚ)*
        (2*(reflectedCarryIntegral p (p/3)).val+(oddBandCarryIntegral p).val) := by
  have hc := WPActualNativeParameter.prime_six_classes p (by omega)
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hi : Set.InjOn (fun j => p-2*j)
      (Finset.Ico (p/6+1) ((p-1)/2+1) : Set ℕ) := by
    intro j hj k hk he
    have hj' := Finset.mem_Ico.mp hj
    have hk' := Finset.mem_Ico.mp hk
    change p-2*j=p-2*k at he
    omega
  have he : (∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : ℚ))=
      -2*(rationalHarmonic (p-1-p/3)-rationalHarmonic (p/3)/2)+
        (p : ℚ)*(oddBandCarryIntegral p).val := by
    have hj : (∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : ℚ))=
        -2*(∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1),
          1/((p-2*j : ℕ) : ℚ))+(p : ℚ)*(oddBandCarryIntegral p).val := by
      rw [oddBandCarryIntegral_value p hp, Finset.mul_sum, Finset.mul_sum,
        ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hr0 : ((p-2*j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : p-2*j ≠ 0)
      rw [Nat.cast_sub (by omega : 2*j ≤ p), Nat.cast_mul, Nat.cast_ofNat]
      rw [Nat.cast_sub (by omega : 2*j ≤ p), Nat.cast_mul, Nat.cast_ofNat] at hr0
      have hrnorm : -((j : ℚ)*2)+(p : ℚ) ≠ 0 := by
        intro hz
        apply hr0
        linear_combination hz
      field_simp [hj0, hr0]
      linear_combination -(mul_inv_cancel₀ hrnorm)
    have him : (∑ r ∈ (Finset.Ico (p/6+1) ((p-1)/2+1)).image (fun j => p-2*j),
        1/(r : ℚ))=
          ∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/((p-2*j : ℕ) : ℚ) := by
      apply Finset.sum_image
      exact hi
    rw [hj, ←him, proper_odd_band_image p hp, rational_odd_harmonic,
      show (p-1-p/3)/2=p/3 by rcases hc with h | h <;> omega]
  have hs := Finset.sum_Ico_consecutive (fun j => 1/(j : ℚ))
    (by omega : 1 ≤ p/6+1) (by rcases hc with h | h <;> omega : p/6+1 ≤ (p-1)/2+1)
  rw [←rationalHarmonic_Ico, ←rationalHarmonic_Ico, he,
    rationalHarmonic_reflection p (p/3) (by omega)] at hs
  linear_combination hs

noncomputable def sixthHarmonicCarryIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  2*WPFiniteCarry.integralEvenLogEndpointCarry p hp+thirdHarmonicCarryIntegral p+
    2*reflectedCarryIntegral p ((p-1)/2)-2*reflectedCarryIntegral p (p/3)-
      oddBandCarryIntegral p

/-- The first division uses the actual rational harmonic numerator and integer quotients. -/
theorem sixthHarmonicCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (sixthHarmonicCarryIntegral p hp).val=
      (rationalHarmonic (p/6)+2*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)+
        (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ))/(p : ℚ) := by
  have hs := rationalHarmonic_sixth_source p hp
  rw [actual_half_harmonic_first_digit p hp, rationalHarmonic_full_firstTaylor p hp] at hs
  have ht := thirdHarmonicCarryIntegral_value p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ht' := (eq_div_iff hp0).mp ht
  change (integralRationals p).subtype (sixthHarmonicCarryIntegral p hp)=_
  rw [sixthHarmonicCarryIntegral, map_sub, map_sub, map_add, map_add,
    map_mul, map_mul, map_mul, map_ofNat]
  simp only [Subring.subtype_apply]
  apply (eq_div_iff hp0).2
  dsimp only [literalQuotientQ] at hs
  linear_combination -hs+ht'

theorem reflectedCarryIntegral_field (p n : ℕ) [Fact p.Prime] (hn : n < p) :
    residueHom p (reflectedCarryIntegral p n)=-harmonicTwo (K := ZMod p) n := by
  rw [reflectedCarryIntegral, map_sum, harmonicTwo, ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  rw [map_mul, smallIntegralInverse_field p j (by omega) (by omega),
    smallIntegralInverse_field p (p-j) (by omega) (by omega),
    WPFiniteField.reflected_denominator p j (Finset.mem_Ico.mpr (by omega)), inv_neg]
  simp only [one_div, pow_two]
  ring

/-- Reduction retains the whole proper-to-half band, then uses its exact image. -/
theorem oddBandCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (oddBandCarryIntegral p)=
      (5/2 : ZMod p)*harmonicTwo (K := ZMod p) (p/3) := by
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have he : residueHom p (oddBandCarryIntegral p)=
      -(1/2 : ZMod p)*(∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : ZMod p)^2) := by
    rw [oddBandCarryIntegral, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have h2 : (2 : ZMod p) ≠ 0 :=
      WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    rw [map_mul, smallIntegralInverse_field p j (by omega) (by omega),
      smallIntegralInverse_field p (p-2*j) (by omega) (by omega),
      Nat.cast_sub (by omega : 2*j ≤ p), Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_self, zero_sub, inv_neg, mul_inv_rev]
    simp only [one_div, pow_two]
    ring
  have hs := harmonicTwo_split (K := ZMod p) (p/6) ((p-1)/2) (by omega)
  rw [harmonicTwo_half_zero p hp, actual_sixth_second_harmonic p hp] at hs
  have hb : (∑ j ∈ Finset.Ico (p/6+1) ((p-1)/2+1), 1/(j : ZMod p)^2)=
      -5*harmonicTwo (K := ZMod p) (p/3) := by linear_combination -hs
  rw [he, hb]
  ring

/-- The canonical sixth-harmonic first carry, with no independently chosen digit. -/
theorem sixthHarmonicCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (sixthHarmonicCarryIntegral p hp)=
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
        (3/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2-
          (5/6 : ZMod p)*harmonicTwo (K := ZMod p) (p/3) := by
  have he := actual_entropy_endpoint_field p hp
  change residueHom p (WPFiniteCarry.integralEvenLogEndpointCarry p hp)=_ at he
  rw [sixthHarmonicCarryIntegral, map_sub, map_sub, map_add, map_add,
    map_mul, map_mul, map_mul, map_ofNat, he, thirdHarmonicCarryIntegral_field p hp,
    reflectedCarryIntegral_field p ((p-1)/2) (by omega), harmonicTwo_half_zero p hp,
    reflectedCarryIntegral_field p (p/3) (by omega), oddBandCarryIntegral_field p hp]
  change 2*((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2)+
      ((3/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2-
        harmonicTwo (K := ZMod p) (p/3)/3)+2*(-0)-2*(-harmonicTwo (K := ZMod p) (p/3))-
          (5/2 : ZMod p)*harmonicTwo (K := ZMod p) (p/3)=_
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  field_simp [h2, h3, h4, h6]
  ring

end WPFieldAssembly.ActualProperHarmonicCarry
