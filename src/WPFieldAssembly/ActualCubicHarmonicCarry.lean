import WPFieldAssembly.ActualFullBinomialCarry
import WPFieldAssembly.ActualCubicUnitCarry
import WPFieldAssembly.ActualCubicWeightTwoTrace

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry WPFieldAssembly.ActualFullBinomialCarry
  WPFieldAssembly.ActualCubicUnitCarry WPActualHarmonicCubicTrace
  WPActualHarmonicCubeFilter

namespace WPFieldAssembly.ActualCubicHarmonicCarry

set_option maxHeartbeats 1200000

noncomputable def cubicSignedSumIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), signedCoefficientIntegral p j

noncomputable def cubicBinomialCarryIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), signedCoefficientCarryIntegral p j

private theorem signed_original_quotient (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    (signedCoefficientIntegral p j).val=
      (((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : ℚ)*(-1 : ℚ)^j := by
  have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
    exact_mod_cast (Fact.out : p.Prime).dvd_choose_self (by omega : j ≠ 0) hjp
  have hi := congrArg (fun n : ℤ => (n : ℚ)) (Int.mul_ediv_cancel' hd)
  push_cast at hi
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : (((Nat.choose p j : ℤ)/(p : ℤ) : ℤ) : ℚ)=
      (Nat.choose p j : ℚ)/(p : ℚ) := by
    apply (eq_div_iff hp0).2
    linear_combination hi
  rw [signedCoefficientIntegral_value p j hj hjp, signedCoefficientQ, he]
  ring

/-- The integral model is the original integer cubic filter, rather than a new lift. -/
theorem cubicSignedSumIntegral_value (p : ℕ) [Fact p.Prime] :
    (cubicSignedSumIntegral p).val=(cubicQuotientSum p (-1) : ℚ) := by
  have hs : cubicQuotientSum p (-1)=
      ∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j),
        ((Nat.choose p j : ℤ)/(p : ℤ))* (-1 : ℤ)^j := by
    simp only [cubicQuotientSum, Finset.sum_filter]
  change (integralRationals p).subtype (cubicSignedSumIntegral p)=_
  rw [cubicSignedSumIntegral, map_sum, hs, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
  simp only [Subring.subtype_apply]
  rw [signed_original_quotient p j (by omega) hj'.2]
  push_cast
  rfl

private theorem cubic_reciprocal_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), smallIntegralInverse p j)=
      smallIntegralInverse p 3*fullHarmonicIntegral p (p/3) := by
  apply Subtype.ext
  change (integralRationals p).subtype
    (∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), smallIntegralInverse p j)=
      (integralRationals p).subtype
        (smallIntegralInverse p 3*fullHarmonicIntegral p (p/3))
  rw [map_sum, cubic_filter_sum p (by omega), map_mul]
  change (∑ r ∈ Finset.Ico 1 (p/3+1), (smallIntegralInverse p (3*r)).val)=
    (smallIntegralInverse p 3).val*(fullHarmonicIntegral p (p/3)).val
  rw [smallIntegralInverse_value p 3 (by omega) (by omega),
    fullHarmonicIntegral_value p (p/3) (by omega), fullHarmonicQ,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hc := WPActualNativeParameter.prime_six_classes p (by omega)
  have hkp : 3*(1+k)<p := by rcases hc with h | h <;> omega
  rw [smallIntegralInverse_value p (3*(1+k)) (by omega) hkp]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact full three-divisibility contraction, including the original p² row remainders. -/
theorem cubicSignedSumIntegral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    cubicSignedSumIntegral p=-smallIntegralInverse p 3*fullHarmonicIntegral p (p/3)+
      (p : integralRationals p)*cubicBinomialCarryIntegral p := by
  unfold cubicSignedSumIntegral cubicBinomialCarryIntegral
  simp_rw [signedCoefficientIntegral_firstTaylor]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ←Finset.mul_sum,
    cubic_reciprocal_source p hp]
  ring

noncomputable def thirdHarmonicCarryIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  3*(cubicBinomialCarryIntegral p-cubicUnitCarryIntegral p)

/-- The actual third-harmonic numerator is fixed before its first division. -/
theorem actual_third_harmonic_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fullHarmonicIntegral p (p/3)=
      -(3 : integralRationals p)*smallIntegralInverse p 2*
        (WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p)+
      (p : integralRationals p)*thirdHarmonicCarryIntegral p := by
  have hs := cubicSignedSumIntegral_source p hp
  have hS : cubicSignedSumIntegral p=(cubicQuotientSum p (-1) : integralRationals p) := by
    apply Subtype.ext
    exact cubicSignedSumIntegral_value p
  rw [hS] at hs
  have hu := actual_cubic_unit_firstTaylor p hp
  apply Subtype.ext
  have hsQ := congrArg (integralRationals p).subtype hs
  have huQ := congrArg (integralRationals p).subtype hu
  simp only [map_add, map_mul, map_neg, map_natCast,
    map_intCast, Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 3 (by omega) (by omega)] at hsQ huQ
  change (integralRationals p).subtype (fullHarmonicIntegral p (p/3))=
    (integralRationals p).subtype
      (-(3 : integralRationals p)*smallIntegralInverse p 2*
        (WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p)+
        (p : integralRationals p)*thirdHarmonicCarryIntegral p)
  rw [map_add, map_mul, map_mul, map_mul, map_neg, map_ofNat, map_natCast,
    map_intCast, thirdHarmonicCarryIntegral, map_mul, map_ofNat, map_sub]
  simp only [Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega)]
  linear_combination 3*hsQ-3*huQ

theorem thirdHarmonicCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (thirdHarmonicCarryIntegral p).val=
      (rationalHarmonic (p/3)+
        (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ))/(p : ℚ) := by
  have h := congrArg (integralRationals p).subtype
    (actual_third_harmonic_firstTaylor p hp)
  simp only [map_add, map_mul, map_neg, map_ofNat, map_natCast, map_intCast,
    Subring.subtype_apply, smallIntegralInverse_value p 2 (by omega) (by omega),
    fullHarmonicIntegral_value p (p/3) (by omega)] at h
  have hh : fullHarmonicQ (p/3)=rationalHarmonic (p/3) := rfl
  rw [hh] at h
  apply (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).2
  linear_combination -h

/-- The full finite weight-two trace remains explicit until its cubic contraction is proved. -/
theorem thirdHarmonicCarryIntegral_field_trace (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (thirdHarmonicCarryIntegral p)=
      3*(∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j),
        (∑ k ∈ Finset.range (j-1), ((k+1 : ℕ) : ZMod p)⁻¹)/(j : ZMod p))+
      (3/8 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2 := by
  have hA : residueHom p (cubicBinomialCarryIntegral p)=
      ∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j),
        (∑ k ∈ Finset.range (j-1), ((k+1 : ℕ) : ZMod p)⁻¹)/(j : ZMod p) := by
    rw [cubicBinomialCarryIntegral, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
    exact signedCoefficientCarryIntegral_field p j (by omega) hj'.2
  rw [thirdHarmonicCarryIntegral, map_mul, map_ofNat, map_sub, hA,
    cubicUnitCarryIntegral_field p hp]
  ring

/-- The actual rational third-harmonic carry, with the full second-harmonic term. -/
theorem thirdHarmonicCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (thirdHarmonicCarryIntegral p)=
      (3/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2-
        WPFieldAssembly.ActualCubicWeightTwoTrace.thirdHarmonicTwo (K := ZMod p) p/3 := by
  have hA : (∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j),
      (∑ k ∈ Finset.range (j-1), ((k+1 : ℕ) : ZMod p)⁻¹)/(j : ZMod p))=
      WPFieldAssembly.ActualCubicWeightTwoTrace.cubicA2 (K := ZMod p) p := by
    unfold WPFieldAssembly.ActualCubicWeightTwoTrace.cubicA2 WPFiniteJSource.H
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm]
  rw [thirdHarmonicCarryIntegral_field_trace p hp, hA,
    WPFieldAssembly.ActualCubicWeightTwoTrace.actual_cubic_weight_two_trace p hp]
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h8 : (8 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 8 (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 9 (by omega) (by omega)
  field_simp [h3, h4, h8, h9]
  ring

end WPFieldAssembly.ActualCubicHarmonicCarry
