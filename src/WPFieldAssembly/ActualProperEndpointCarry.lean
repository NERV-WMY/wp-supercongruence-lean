import WPFieldAssembly.ActualProperHarmonicCarry
import WPFieldAssembly.ActualProperProductTaylor

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualFiniteEntropyCarry WPFieldAssembly.ActualHarmonicReflection
  WPFieldAssembly.ActualProperHarmonicCarry WPFieldAssembly.ActualProperProductTaylor

namespace WPFieldAssembly.ActualProperEndpointCarry

set_option maxHeartbeats 1400000

noncomputable def endpointOriginIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -2*(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p)-
    3*smallIntegralInverse p 2*(WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p)

noncomputable def endpointCarryIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  sixthHarmonicCarryIntegral p hp-smallIntegralInverse p 3*properPairIntegral p (p/6)+
    (p : integralRationals p)*(smallIntegralInverse p 3)^2*properThirdIntegral p (p/6)

/-- h_* is the opposite of the literal divided Jacobi product. -/
noncomputable def literalHstarIntegral (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -properEndpointIntegral p (p/6)

noncomputable def literalHstarQ (p : ℕ) : ℚ := -properEndpointQ p (p/6)

theorem endpointOriginIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (endpointOriginIntegral p).val=
      -2*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)-
        (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ) := by
  change (integralRationals p).subtype (endpointOriginIntegral p)=_
  rw [endpointOriginIntegral, map_sub, map_mul, map_mul, map_mul, map_neg,
    map_ofNat, map_ofNat, map_intCast, map_intCast]
  change -2*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)-
    3*(smallIntegralInverse p 2).val*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ)=_
  rw [smallIntegralInverse_value p 2 (by omega) (by omega)]
  ring

theorem actual_sixth_harmonic_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    fullHarmonicIntegral p (p/6)=endpointOriginIntegral p+
      (p : integralRationals p)*sixthHarmonicCarryIntegral p hp := by
  apply Subtype.ext
  change (fullHarmonicIntegral p (p/6)).val=
    (integralRationals p).subtype (endpointOriginIntegral p+
      (p : integralRationals p)*sixthHarmonicCarryIntegral p hp)
  rw [fullHarmonicIntegral_value p (p/6) (by omega), map_add, map_mul, map_natCast]
  change fullHarmonicQ (p/6)=(endpointOriginIntegral p).val+
    (p : ℚ)*(sixthHarmonicCarryIntegral p hp).val
  rw [endpointOriginIntegral_value p hp]
  have h := sixthHarmonicCarryIntegral_value p hp
  have he := (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).mp h
  change rationalHarmonic (p/6)=_
  linear_combination -he

theorem literalHstarIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (literalHstarIntegral p).val=literalHstarQ p := by
  change (integralRationals p).subtype (-properEndpointIntegral p (p/6))=_
  rw [map_neg]
  change -(properEndpointIntegral p (p/6)).val=_
  rw [properEndpointIntegral_value p (p/6) hp (by omega)]
  rfl

/-- The source product fixes both the origin and the actual first carry. -/
theorem actual_literal_hstar_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    literalHstarIntegral p=endpointOriginIntegral p+
      (p : integralRationals p)*endpointCarryIntegral p hp := by
  rw [literalHstarIntegral, properEndpointIntegral_firstTaylor,
    actual_sixth_harmonic_firstTaylor p hp, endpointCarryIntegral]
  ring

theorem endpointCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (endpointCarryIntegral p hp).val=
      (literalHstarQ p+2*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)+
        (3/2 : ℚ)*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ))/(p : ℚ) := by
  have h := congrArg (integralRationals p).subtype (actual_literal_hstar_firstTaylor p hp)
  rw [map_add, map_mul, map_natCast] at h
  change (literalHstarIntegral p).val=(endpointOriginIntegral p).val+
    (p : ℚ)*(endpointCarryIntegral p hp).val at h
  rw [literalHstarIntegral_value p hp, endpointOriginIntegral_value p hp] at h
  apply (eq_div_iff
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ) ≠ 0)).2
  linear_combination -h

theorem endpointOriginIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (endpointOriginIntegral p)=
      -2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  rw [endpointOriginIntegral, map_sub, map_mul, map_mul, map_mul, map_neg,
    map_ofNat, map_ofNat, map_intCast, map_intCast,
    smallIntegralInverse_field p 2 (by omega) (by omega)]
  simp only [div_eq_mul_inv]
  ring

/-- The original product carry has the NC95 digit in both prime classes. -/
theorem endpointCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (endpointCarryIntegral p hp)=
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/3-
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
            (3/8 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2 := by
  have hH : residueHom p (fullHarmonicIntegral p (p/6))=
      -2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
    have h := congrArg (residueHom p) (actual_sixth_harmonic_firstTaylor p hp)
    rw [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
      endpointOriginIntegral_field p hp] at h
    exact h
  have hS : (∑ j ∈ Finset.range (p/6), (((j+1 : ℕ) : ZMod p)⁻¹)^2)=
      harmonicTwo (K := ZMod p) (p/6) := by
    rw [harmonicTwo, Finset.sum_Ico_eq_sum_range]
    rw [show p/6+1-1=p/6 by omega]
    simp only [Nat.add_comm, one_div, inv_pow]
  have hP := properPairIntegral_field p (p/6) (by omega)
  rw [hH, hS, actual_sixth_second_harmonic p hp] at hP
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hP' : residueHom p (properPairIntegral p (p/6))=
      ((-2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p))^2-
            5*harmonicTwo (K := ZMod p) (p/3))/2 := by
    apply (eq_div_iff h2).2
    linear_combination hP
  rw [endpointCarryIntegral, map_add, map_sub, map_mul, map_mul, map_mul,
    map_pow, map_natCast, ZMod.natCast_self, zero_mul, zero_mul, add_zero,
    sixthHarmonicCarryIntegral_field p hp, smallIntegralInverse_field p 3 (by omega) (by omega), hP']
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h8 : (8 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 8 (by omega) (by omega)
  field_simp [h2, h3, h4, h6, h8]
  ring

end WPFieldAssembly.ActualProperEndpointCarry
