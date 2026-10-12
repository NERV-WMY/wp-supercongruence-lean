import WPFieldAssembly.ActualEntropyLogAttachment
import WPFiniteCarry.EndpointHarmonic
import WPRationalWeightTwo

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift WPActualRankTwoLegendreField
  WPFieldAssembly.ActualEntropyPolynomial WPFieldAssembly.ActualEntropyLogAttachment

namespace WPFieldAssembly.ActualEntropyEndpoints

set_option maxHeartbeats 1200000

noncomputable def literalQuotientQ (p : ℕ) (a : ℤ) : ℚ :=
  WPFiniteInversion.integerFermatQuotient p a

/-- All quotient normalization occurs in the integers before reduction. -/
theorem literal_fermat_power (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a : ZMod p) ≠ 0) :
    (a : ℚ)^p = (a : ℚ) + (p : ℚ) * (a : ℚ) * literalQuotientQ p a := by
  unfold literalQuotientQ
  have hq : literalQuotientQ p a * (p : ℚ) = (a : ℚ)^(p-1)-1 := by
    change (WPFiniteInversion.integerFermatQuotient p a : ℚ) * (p : ℚ) = _
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p a ha
  have hpow : (a : ℚ)^p = (a : ℚ)^(p-1)*(a : ℚ) := by
    rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  rw [hpow]
  dsimp only [literalQuotientQ] at hq
  linear_combination -(a : ℚ) * hq

theorem actual_entropy_one (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (entropySumQ p).eval 1 = -literalQuotientQ p 2 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hpow := literal_fermat_power p 2 (by simpa using h2)
  norm_num only [Int.cast_ofNat] at hpow
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he := actual_entropy_powers p hp 1
  norm_num only [one_pow, sub_self, zero_pow (Fact.out : p.Prime).ne_zero,
    show (1+1 : ℚ)=2 by ring, sub_zero] at he
  rw [he]
  field_simp [hp0]
  linear_combination -hpow

theorem actual_entropy_two (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (entropySumQ p).eval 4 = -(3/2 : ℚ) * literalQuotientQ p 3 := by
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have hpow := literal_fermat_power p 3 (by simpa using h3)
  norm_num only [Int.cast_ofNat] at hpow
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have he := actual_entropy_powers p hp 2
  norm_num only [show (2 : ℚ)^2=4 by norm_num, show (1-2 : ℚ) = -1 by norm_num,
    show (1+2 : ℚ)=3 by norm_num, hodd.neg_one_pow] at he
  rw [he]
  field_simp [hp0]
  linear_combination -hpow

theorem actual_entropy_half (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (entropySumQ p).eval (1/4) =
      (literalQuotientQ p 2 - (3/4 : ℚ) * literalQuotientQ p 3) /
        (2 : ℚ)^(p-1) := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h3pow := literal_fermat_power p 3 (by simpa using h3)
  norm_num only [Int.cast_ofNat] at h3pow
  have hU : (2 : ℚ)^(p-1) = 1 + (p : ℚ)*literalQuotientQ p 2 := by
    have hq : literalQuotientQ p 2 * (p : ℚ) = (2 : ℚ)^(p-1)-1 := by
      change (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)*(p : ℚ) = _
      exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
    dsimp only [literalQuotientQ] at hq ⊢
    linear_combination -hq
  have h2pow : (2 : ℚ)^p = 2*(2 : ℚ)^(p-1) := by
    calc
      _ = (2 : ℚ)^(p-1)*2 := by
        rw [←pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
      _ = _ := by ring
  have hden : 1 + (p : ℚ)*literalQuotientQ p 2 ≠ 0 := by rw [←hU]; positivity
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he := actual_entropy_powers p hp (1/2)
  norm_num only [show (1/2 : ℚ)^2=1/4 by norm_num,
    show (1-1/2 : ℚ)=1/2 by norm_num, show (1+1/2 : ℚ)=3/2 by norm_num] at he
  rw [he, div_pow, one_pow, div_pow, h2pow, h3pow, hU]
  dsimp only [literalQuotientQ] at *
  field_simp [hp0, hden]
  all_goals ring

/-- The pre-existing actual endpoint carry is exactly the literal entropy carry. -/
theorem actual_entropy_endpoint_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (entropyCarryIntegral p).eval 1 = WPFiniteCarry.integralEvenLogEndpointCarry p hp := by
  apply Subtype.ext
  have he := actual_entropy_evaluation_carry p (1 : integralRationals p)
  have hl := congrArg (fun P : ℚ[X] => P.eval 1) (movingEvenQ_actual_pullback p hp)
  simp only [eval_comp, eval_pow, eval_X, one_pow] at hl
  simp only [OneMemClass.coe_one, actual_entropy_one p hp] at he
  rw [hl] at he
  change ((entropyCarryIntegral p).eval 1).val = WPFiniteCarry.actualEvenLogEndpointCarry p
  have hs := WPFiniteCarry.actualEvenLogEndpointCarry_source p
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hp0
  dsimp only [literalQuotientQ] at he
  linear_combination hs - he

theorem actual_entropy_endpoint_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteCarry.actualEvenLogEndpointField p hp =
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2 := by
  unfold WPFiniteCarry.actualEvenLogEndpointField
  rw [←actual_entropy_endpoint_integral p hp]
  have he := actual_entropy_carry_Aeven p hp (1 : integralRationals p)
  simp only [one_pow, map_one] at he
  rw [he]
  unfold WPFiniteNC122.Aeven
  have h0 : WPFiniteField.R p (0 : ZMod p) = 0 := by
    unfold WPFiniteField.R
    apply Finset.sum_eq_zero
    intro j hj
    have hjpos := (Finset.mem_Ico.mp hj).1
    simp only [zero_pow (by omega : j ≠ 0), zero_div]
  have h2 : WPFiniteField.R p (2 : ZMod p) =
      -(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2 :=
    WPFiniteInversion.R_two_eq_fermat p hp
  norm_num only [sub_self, show (1+1 : ZMod p)=2 by ring, h0, h2, zero_add]
  ring

/-- The actual half harmonic first digit is supplied by this same endpoint. -/
theorem actual_half_harmonic_first_digit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rationalHarmonic ((p-1)/2) =
      -2*literalQuotientQ p 2 +
        2*(p : ℚ)*(WPFiniteCarry.integralEvenLogEndpointCarry p hp).val := by
  have he := WPFiniteCarry.actualEvenLogEndpointCarry_source p
  rw [WPFiniteCarry.rationalEvenLog_endpoint_harmonic p (by omega)] at he
  change rationalHarmonic ((p-1)/2) =
    -2*literalQuotientQ p 2 + 2*(p : ℚ)*WPFiniteCarry.actualEvenLogEndpointCarry p
  dsimp only [literalQuotientQ]
  linear_combination 2*he

/-- SB102e's literal rational numerator is divided before the residue map. -/
noncomputable def literalR1Q (p : ℕ) : ℚ :=
  (-(movingEvenQ p).eval 4 + 2*(movingEvenQ p).eval (1/4) -
    rationalHarmonic ((p-1)/2)/2 - 3*literalQuotientQ p 2)/(p : ℚ)

noncomputable def literalR1Integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  -((entropyCarryIntegral p).eval 4) +
    2*((entropyCarryIntegral p).eval ((integralHalf p (by omega))^2)) -
    WPFiniteCarry.integralEvenLogEndpointCarry p hp -
    (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
      (2*(WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) -
        3*integralHalf p (by omega)*
          (WPFiniteInversion.integerFermatQuotient p 3 : integralRationals p)) *
      integralHalf p (by omega)^(p-1)

theorem literalR1Integral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (literalR1Integral p hp).val = literalR1Q p := by
  have h4 := actual_entropy_evaluation_carry p (4 : integralRationals p)
  have hh := actual_entropy_evaluation_carry p ((integralHalf p (by omega))^2)
  have hHalf : (integralHalf p (by omega : 7 ≤ p)).val = (1/2 : ℚ) := rfl
  change (movingEvenQ p).eval 4-(entropySumQ p).eval 4=
    (p : ℚ)*((entropyCarryIntegral p).eval 4).val at h4
  simp only [Subring.coe_pow, hHalf,
    show (1/2 : ℚ)^2=1/4 by norm_num] at hh
  rw [actual_entropy_two p hp] at h4
  rw [actual_entropy_half p hp] at hh
  have h4' : (movingEvenQ p).eval 4 = -(3/2 : ℚ)*literalQuotientQ p 3 +
      (p : ℚ)*((entropyCarryIntegral p).eval 4).val := by linear_combination h4
  have hh' : (movingEvenQ p).eval (1/4) =
      (literalQuotientQ p 2 - (3/4 : ℚ)*literalQuotientQ p 3)/(2 : ℚ)^(p-1) +
      (p : ℚ)*((entropyCarryIntegral p).eval ((integralHalf p (by omega))^2)).val := by
    linear_combination hh
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hU : (2 : ℚ)^(p-1) = 1 + (p : ℚ)*literalQuotientQ p 2 := by
    have hq : literalQuotientQ p 2*(p : ℚ) = (2 : ℚ)^(p-1)-1 := by
      change (WPFiniteInversion.integerFermatQuotient p 2 : ℚ)*(p : ℚ) = _
      exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
    dsimp only [literalQuotientQ] at hq ⊢
    linear_combination -hq
  have hden : 1+(p : ℚ)*literalQuotientQ p 2 ≠ 0 := by rw [←hU]; positivity
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change (integralRationals p).subtype (literalR1Integral p hp) = _
  rw [literalR1Integral, map_sub, map_sub, map_add, map_neg, map_mul, map_ofNat,
    map_mul, map_mul, map_sub, map_mul, map_ofNat, map_intCast, map_mul, map_mul,
    map_ofNat, map_intCast, map_pow]
  simp only [Subring.subtype_apply, hHalf]
  change -((entropyCarryIntegral p).eval 4).val +
      2*((entropyCarryIntegral p).eval ((integralHalf p (by omega))^2)).val -
      (WPFiniteCarry.integralEvenLogEndpointCarry p hp).val -
      literalQuotientQ p 2*(2*literalQuotientQ p 2-3*(1/2 : ℚ)*literalQuotientQ p 3)*
        (1/2 : ℚ)^(p-1) = _
  unfold literalR1Q
  rw [h4', hh', actual_half_harmonic_first_digit p hp, one_div_pow, hU]
  dsimp only [literalQuotientQ] at *
  field_simp [hp0, hden]
  have hcancel := mul_inv_cancel₀ hden
  linear_combination -(16*(WPFiniteInversion.integerFermatQuotient p 2 : ℚ)-
    12*(WPFiniteInversion.integerFermatQuotient p 3 : ℚ))*hcancel

private theorem integralHalf_power_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (integralHalf p (by omega)^(p-1)) = 1 := by
  rw [map_pow, integralHalf_field]
  apply ZMod.pow_card_sub_one_eq_one
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  simpa only [one_div] using inv_ne_zero h2

theorem literalR1Integral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (literalR1Integral p hp) =
      -WPFiniteNC122.Aeven p (2 : ZMod p) +
        2*WPFiniteNC122.Aeven p (1/2 : ZMod p) -
        (5/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2 +
        (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have h4 := actual_entropy_carry_Aeven p hp (2 : integralRationals p)
  have hh := actual_entropy_carry_Aeven p hp (integralHalf p (by omega))
  norm_num only [show (2 : integralRationals p)^2=4 by norm_num, map_ofNat] at h4
  rw [integralHalf_field] at hh
  rw [literalR1Integral, map_sub, map_sub, map_add, map_neg, map_mul, map_ofNat,
    h4, hh, map_mul, map_mul, map_intCast, map_sub, map_mul, map_ofNat,
    map_intCast, map_mul, map_mul, map_ofNat, integralHalf_field, map_intCast,
    integralHalf_power_field p hp]
  change -WPFiniteNC122.Aeven p (2 : ZMod p) +
    2*WPFiniteNC122.Aeven p (1/2 : ZMod p) -
    WPFiniteCarry.actualEvenLogEndpointField p hp -
    (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
      (2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        3*(1/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p))*1 = _
  rw [actual_entropy_endpoint_field p hp]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  field_simp [h2]
  ring

end WPFieldAssembly.ActualEntropyEndpoints

