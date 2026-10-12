import WPFieldAssembly.ActualFiniteEntropyCarry

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry

namespace WPFieldAssembly.ActualFullBinomialCarry

set_option maxHeartbeats 1000000

/-- The full signed binomial row used by the cubic trace, before division or reduction. -/
noncomputable def signedCoefficientQ (p j : ℕ) : ℚ :=
  (-1 : ℚ)^j*(p.choose j : ℚ)/(p : ℚ)

theorem signedCoefficient_product (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    signedCoefficientQ p j=-fullProductQ p (j-1)/(j : ℚ) := by
  have hn := Nat.add_one_mul_choose_eq (p-1) (j-1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    Nat.sub_add_cancel (by omega : 1 ≤ j)] at hn
  have hm := congrArg (fun n : ℕ => (n : ℚ)) hn
  push_cast at hm
  have hs := signed_pred_choose_product p (j-1) (by omega)
  have hsign : (-1 : ℚ)^j=(-1)^(j-1)*(-1) := by
    rw [←pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  unfold signedCoefficientQ
  rw [←hs, hsign]
  apply (div_eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)
    (by exact_mod_cast (by omega : j ≠ 0) : (j : ℚ) ≠ 0)).2
  linear_combination ((-1 : ℚ)^(j-1))*hm

/-- The exact second-order remainder is retained at every full-cutoff index. -/
theorem signedCoefficient_firstTaylor (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    signedCoefficientQ p j=-1/(j : ℚ)+
      (p : ℚ)*fullHarmonicQ (j-1)/(j : ℚ)-
      (p : ℚ)^2*(fullProductRemainder p (j-1)).val/(j : ℚ) := by
  rw [signedCoefficient_product p j hj hjp]
  have h := congrArg (integralRationals p).subtype
    (fullProductIntegral_firstTaylor p (j-1))
  simp only [map_add, map_sub, map_mul, map_one, map_natCast, map_pow,
    fullHarmonicIntegral_value p (j-1) (by omega),
    fullProductIntegral_value p (j-1) (by omega), Subring.subtype_apply] at h
  rw [h]
  ring

noncomputable def signedCoefficientIntegral (p j : ℕ) [Fact p.Prime] :
    integralRationals p :=
  -fullProductIntegral p (j-1)*smallIntegralInverse p j

noncomputable def signedCoefficientCarryIntegral (p j : ℕ) [Fact p.Prime] :
    integralRationals p :=
  (fullHarmonicIntegral p (j-1)-
    (p : integralRationals p)*fullProductRemainder p (j-1))*smallIntegralInverse p j

theorem signedCoefficientIntegral_value (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    (signedCoefficientIntegral p j).val=signedCoefficientQ p j := by
  change (integralRationals p).subtype (signedCoefficientIntegral p j)=_
  rw [signedCoefficientIntegral, map_mul, map_neg]
  simp only [Subring.subtype_apply]
  rw [fullProductIntegral_value p (j-1) (by omega),
    smallIntegralInverse_value p j hj hjp, signedCoefficient_product p j hj hjp]
  ring

theorem signedCoefficientIntegral_firstTaylor (p j : ℕ) [Fact p.Prime] :
    signedCoefficientIntegral p j=-smallIntegralInverse p j+
      (p : integralRationals p)*signedCoefficientCarryIntegral p j := by
  rw [signedCoefficientIntegral, fullProductIntegral_firstTaylor]
  unfold signedCoefficientCarryIntegral
  ring

/-- The prescribed actual rational numerator is divided before its residue map. -/
theorem signedCoefficientCarryIntegral_value (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    (signedCoefficientCarryIntegral p j).val=
      (signedCoefficientQ p j+1/(j : ℚ))/(p : ℚ) := by
  have h := congrArg (integralRationals p).subtype
    (signedCoefficientIntegral_firstTaylor p j)
  simp only [map_add, map_neg, map_mul, map_natCast, Subring.subtype_apply,
    signedCoefficientIntegral_value p j hj hjp,
    smallIntegralInverse_value p j hj hjp] at h
  apply (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).2
  linear_combination -h

theorem signedCoefficientCarryIntegral_field (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) :
    residueHom p (signedCoefficientCarryIntegral p j)=
      (∑ k ∈ Finset.range (j-1), ((k+1 : ℕ) : ZMod p)⁻¹)/(j : ZMod p) := by
  rw [signedCoefficientCarryIntegral, map_mul, map_sub, map_mul, map_natCast,
    ZMod.natCast_self, zero_mul, sub_zero, smallIntegralInverse_field p j hj hjp]
  congr 1
  rw [fullHarmonicIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr := Finset.mem_range.mp hk
  exact smallIntegralInverse_field p (k+1) (by omega) (by omega)

end WPFieldAssembly.ActualFullBinomialCarry
