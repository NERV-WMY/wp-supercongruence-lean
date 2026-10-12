import WPFiniteEntropy
import WPActualRankTwoHatLift
import WPFieldAssembly.ActualKwFieldTrace
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open scoped PowerSeries BigOperators
open PowerSeries WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualKwFirstCarry

set_option maxHeartbeats 1000000

section IntegralKernel
variable {K J : Type*} [CommRing K] [CommRing J]

noncomputable def linearFactor (a : K) : K⟦X⟧ := 1-C a*X
noncomputable def phaseFactor (p : ℕ) (a : K) : K⟦X⟧ := 1-C (a^p)*X^p

/-- The original signed integer divided-binomial row, before any field map. -/
noncomputable def binomialCarry (p : ℕ) (a : K) : K⟦X⟧ :=
  -(∑ j ∈ Finset.Ico 1 p,
    C ((((p.choose j : ℤ)/(p : ℤ)) : ℤ) : K)*(-C a*X)^j)

theorem binomialCarry_map (f : K →+* J) (p : ℕ) (a : K) :
    PowerSeries.map f (binomialCarry p a) = binomialCarry p (f a) := by
  simp only [binomialCarry, map_neg, map_sum, map_mul, map_pow, PowerSeries.map_C,
    map_intCast, PowerSeries.map_X]

theorem linearFactor_map (f : K →+* J) (a : K) :
    PowerSeries.map f (linearFactor a) = linearFactor (f a) := by
  simp only [linearFactor, map_sub, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X]

theorem phaseFactor_map (f : K →+* J) (p : ℕ) (a : K) :
    PowerSeries.map f (phaseFactor p a) = phaseFactor p (f a) := by
  simp only [phaseFactor, map_sub, map_one, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X]

theorem linearFactor_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : K) :
    linearFactor a^p = phaseFactor p a-(p : K⟦X⟧)*binomialCarry p a := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hbin := add_pow (-C a*X) (1 : K⟦X⟧) p
  simp only [one_pow, mul_one] at hbin
  rw [Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, Nat.choose_self] at hbin
  have hlast : (-C a*X : K⟦X⟧)^p = -C (a^p)*X^p := by
    rw [mul_pow, hodd.neg_pow, ← map_pow]
  have hsum : (∑ j ∈ Finset.Ico 1 p, (-C a*X)^j*(p.choose j : K⟦X⟧)) =
      (p : K⟦X⟧)*(∑ j ∈ Finset.Ico 1 p,
        C ((((p.choose j : ℤ)/(p : ℤ)) : ℤ) : K)*(-C a*X)^j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hd : (p : ℤ) ∣ (p.choose j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by omega) hj'.2
    have he := congrArg (fun z : ℤ => (z : K⟦X⟧)) (Int.mul_ediv_cancel' hd)
    push_cast at he
    have hC : C ((((p.choose j : ℤ)/(p : ℤ)) : ℤ) : K) =
        (((p.choose j : ℤ)/(p : ℤ)) : ℤ) := by simp
    rw [hC]
    linear_combination -(-C a*X)^j*he
  rw [hlast, hsum] at hbin
  unfold linearFactor phaseFactor binomialCarry
  linear_combination hbin

noncomputable def unitInverse (F : K⟦X⟧) : K⟦X⟧ := invOfUnit F 1

theorem unitInverse_right (F : K⟦X⟧) (hF : constantCoeff F = 1) :
    F*unitInverse F = 1 := by
  exact mul_invOfUnit F 1 (by simpa using hF)

theorem unitInverse_left (F : K⟦X⟧) (hF : constantCoeff F = 1) :
    unitInverse F*F = 1 := by
  exact invOfUnit_mul F 1 (by simpa using hF)

theorem unitInverse_map (f : K →+* J) (F : K⟦X⟧)
    (hF : constantCoeff F = 1) :
    PowerSeries.map f (unitInverse F) = unitInverse (PowerSeries.map f F) := by
  have hm : constantCoeff (PowerSeries.map f F) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, hF, map_one]
  have h1 := congrArg (PowerSeries.map f) (unitInverse_left F hF)
  rw [map_mul, map_one] at h1
  calc
    PowerSeries.map f (unitInverse F) =
        PowerSeries.map f (unitInverse F)*
          (PowerSeries.map f F*unitInverse (PowerSeries.map f F)) := by
      rw [unitInverse_right _ hm, mul_one]
    _ = (PowerSeries.map f (unitInverse F)*PowerSeries.map f F)*
          unitInverse (PowerSeries.map f F) := by ring
    _ = unitInverse (PowerSeries.map f F) := by rw [h1, one_mul]

theorem linearFactor_constant (a : K) : constantCoeff (linearFactor a) = 1 := by
  simp [linearFactor]

theorem phaseFactor_constant (p : ℕ) (hp : 0 < p) (a : K) :
    constantCoeff (phaseFactor p a) = 1 := by
  simp [phaseFactor, Nat.ne_of_gt hp]

noncomputable def actualUnit (p : ℕ) (a b c : K) : K⟦X⟧ :=
  linearFactor c^p*unitInverse (linearFactor a^p*linearFactor b^p)

noncomputable def frobeniusUnit (p : ℕ) (a b c : K) : K⟦X⟧ :=
  phaseFactor p c*unitInverse (phaseFactor p a*phaseFactor p b)

/-- The numerator of the whole rational first difference divided by p. -/
noncomputable def carryNumerator (p : ℕ) (a b c : K) : K⟦X⟧ :=
  phaseFactor p c*(binomialCarry p a*phaseFactor p b+
    binomialCarry p b*phaseFactor p a)-
  binomialCarry p c*phaseFactor p a*phaseFactor p b-
  (p : K⟦X⟧)*phaseFactor p c*binomialCarry p a*binomialCarry p b

noncomputable def actualUnitCarry (p : ℕ) (a b c : K) : K⟦X⟧ :=
  carryNumerator p a b c*
    unitInverse (linearFactor a^p*linearFactor b^p)*
    unitInverse (phaseFactor p a*phaseFactor p b)

theorem whole_difference_cleared (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a b c : K) :
    linearFactor c^p*(phaseFactor p a*phaseFactor p b)-
      phaseFactor p c*(linearFactor a^p*linearFactor b^p) =
        (p : K⟦X⟧)*carryNumerator p a b c := by
  rw [linearFactor_firstTaylor p hp a, linearFactor_firstTaylor p hp b,
    linearFactor_firstTaylor p hp c]
  unfold carryNumerator
  ring

theorem actualUnit_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a b c : K) :
    actualUnit p a b c = frobeniusUnit p a b c+(p : K⟦X⟧)*actualUnitCarry p a b c := by
  have hp0 : 0 < p := by omega
  have hD : constantCoeff (linearFactor a^p*linearFactor b^p) = 1 := by
    simp only [map_mul, map_pow, linearFactor_constant, one_pow, one_mul]
  have hB : constantCoeff (phaseFactor p a*phaseFactor p b) = 1 := by
    rw [map_mul, phaseFactor_constant p hp0, phaseFactor_constant p hp0, one_mul]
  have hfrac : actualUnit p a b c-frobeniusUnit p a b c =
      (linearFactor c^p*(phaseFactor p a*phaseFactor p b)-
        phaseFactor p c*(linearFactor a^p*linearFactor b^p))*
        unitInverse (linearFactor a^p*linearFactor b^p)*
        unitInverse (phaseFactor p a*phaseFactor p b) := by
    unfold actualUnit frobeniusUnit
    calc
      _ = linearFactor c^p*unitInverse (linearFactor a^p*linearFactor b^p)*
            ((phaseFactor p a*phaseFactor p b)*unitInverse (phaseFactor p a*phaseFactor p b))-
          phaseFactor p c*unitInverse (phaseFactor p a*phaseFactor p b)*
            ((linearFactor a^p*linearFactor b^p)*unitInverse (linearFactor a^p*linearFactor b^p)) := by
        rw [unitInverse_right _ hB, unitInverse_right _ hD, mul_one, mul_one]
      _ = _ := by ring
  rw [whole_difference_cleared p hp a b c] at hfrac
  unfold actualUnitCarry
  linear_combination hfrac

theorem actualUnit_map (f : K →+* J) (p : ℕ) (a b c : K) :
    PowerSeries.map f (actualUnit p a b c) = actualUnit p (f a) (f b) (f c) := by
  unfold actualUnit
  rw [map_mul, map_pow, linearFactor_map, unitInverse_map]
  · simp only [map_mul, map_pow, linearFactor_map]
  · simp only [map_mul, map_pow, linearFactor_constant, one_pow, one_mul]

theorem frobeniusUnit_map (f : K →+* J) (p : ℕ) (hp : 0 < p) (a b c : K) :
    PowerSeries.map f (frobeniusUnit p a b c) = frobeniusUnit p (f a) (f b) (f c) := by
  unfold frobeniusUnit
  rw [map_mul, phaseFactor_map, unitInverse_map]
  · simp only [map_mul, phaseFactor_map]
  · rw [map_mul, phaseFactor_constant p hp, phaseFactor_constant p hp, one_mul]

theorem actualUnitCarry_map (f : K →+* J) (p : ℕ) (hp : 0 < p) (a b c : K) :
    PowerSeries.map f (actualUnitCarry p a b c) =
      actualUnitCarry p (f a) (f b) (f c) := by
  unfold actualUnitCarry carryNumerator
  rw [map_mul, map_mul, unitInverse_map, unitInverse_map]
  · simp only [map_sub, map_mul, map_add, map_natCast, phaseFactor_map,
      binomialCarry_map, map_pow, linearFactor_map]
  · rw [map_mul, phaseFactor_constant p hp, phaseFactor_constant p hp, one_mul]
  · simp only [map_mul, map_pow, linearFactor_constant, one_pow, one_mul]

theorem unitInverse_pow (F : K⟦X⟧) (hF : constantCoeff F=1) (n : ℕ) :
    unitInverse (F^n)=unitInverse F^n := by
  have hn : constantCoeff (F^n)=1 := by rw [map_pow,hF,one_pow]
  have hu : F^n*unitInverse F^n=1 := by
    rw [←mul_pow,unitInverse_right F hF,one_pow]
  calc
    unitInverse (F^n) = unitInverse (F^n)*(F^n*unitInverse F^n) := by rw [hu,mul_one]
    _ = (unitInverse (F^n)*F^n)*unitInverse F^n := by ring
    _ = unitInverse F^n := by rw [unitInverse_left _ hn,one_mul]

theorem actualUnit_power (p : ℕ) (a b c : K) :
    actualUnit p a b c = (linearFactor c*unitInverse (linearFactor a*linearFactor b))^p := by
  have hD : constantCoeff (linearFactor a*linearFactor b)=1 := by
    rw [map_mul,linearFactor_constant,linearFactor_constant,one_mul]
  unfold actualUnit
  rw [←mul_pow,unitInverse_pow _ hD,←mul_pow]

end IntegralKernel

noncomputable def actualA (p : ℕ) [Fact p.Prime] : integralRationals p :=
  smallIntegralInverse p 4
noncomputable def actualB (p : ℕ) [Fact p.Prime] : integralRationals p := 4
noncomputable def actualC (p : ℕ) [Fact p.Prime] : integralRationals p :=
  11*smallIntegralInverse p 4

theorem actual_parameters_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualA p).val = (1/4 : ℚ) ∧ (actualB p).val = (4 : ℚ) ∧
      (actualC p).val = (11/4 : ℚ) := by
  have h4 := smallIntegralInverse_value p 4 (by omega) (by omega)
  unfold actualA actualB actualC
  refine ⟨?_,rfl,?_⟩
  · simpa only [Nat.cast_ofNat] using h4
  · change (11 : ℚ)*(smallIntegralInverse p 4).val = (11/4 : ℚ)
    rw [h4]
    ring

noncomputable def actualUnitCarryIntegral (p : ℕ) [Fact p.Prime] :
    (integralRationals p)⟦X⟧ := actualUnitCarry p (actualA p) (actualB p) (actualC p)

/-- The canonical rational difference is formed before coefficient reduction. -/
noncomputable def actualUnitCarryQ (p : ℕ) : ℚ⟦X⟧ :=
  C (1/(p : ℚ))*(actualUnit p (1/4 : ℚ) 4 (11/4)-frobeniusUnit p (1/4 : ℚ) 4 (11/4))

theorem actualUnitCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.map (integralRationals p).subtype (actualUnitCarryIntegral p) =
      actualUnitCarryQ p := by
  have hp0 : 0 < p := by omega
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp0)
  obtain ⟨ha,hb,hc⟩ := actual_parameters_rational p hp
  rw [actualUnitCarryIntegral, actualUnitCarry_map _ p hp0]
  simp only [Subring.subtype_apply, ha,hb,hc]
  unfold actualUnitCarryQ
  rw [actualUnit_firstTaylor p (by omega : 3 ≤ p)]
  have hpC : (p : ℚ⟦X⟧) = C (p : ℚ) := by simp
  rw [hpC]
  ring_nf
  rw [← map_mul, inv_mul_cancel₀ hpq, map_one, one_mul]

theorem actualUnitCarryQ_coeff_integral (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coeff n (actualUnitCarryQ p) ∈ integralRationals p := by
  rw [← actualUnitCarryIntegral_value p hp, coeff_map]
  exact (coeff n (actualUnitCarryIntegral p)).property

theorem literal_denominator_infinity :
    linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ) = LaurentPoleTrace.reversedA := by
  have hm : (C (1/4 : ℚ) : ℚ⟦X⟧)*C 4=1 := by rw [←map_mul]; norm_num
  have hs : (C (1/4 : ℚ) : ℚ⟦X⟧)+C 4=C (17/4 : ℚ) := by rw [←map_add]; norm_num
  calc
    _ = 1-(C (1/4 : ℚ)+C 4)*X+(C (1/4 : ℚ)*C 4)*X^2 := by unfold linearFactor; ring
    _ = LaurentPoleTrace.reversedA := by rw [hm,hs]; simp only [one_mul]; rfl

theorem literal_unitInverse_infinity :
    unitInverse (linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ)) =
      LaurentPoleTrace.reciprocal := by
  have hS := LaurentPoleTrace.reciprocal_identity
  rw [←literal_denominator_infinity] at hS
  have hD : constantCoeff (linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ))=1 := by
    rw [map_mul,linearFactor_constant,linearFactor_constant,one_mul]
  calc
    _ = unitInverse (linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ))*
        ((linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ))*LaurentPoleTrace.reciprocal) := by
      rw [hS,mul_one]
    _ = (unitInverse (linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ))*
        (linearFactor (1/4 : ℚ)*linearFactor (4 : ℚ)))*LaurentPoleTrace.reciprocal := by ring
    _ = LaurentPoleTrace.reciprocal := by rw [unitInverse_left _ hD,one_mul]

/-- The original rational numerator and denominator normalization at infinity. -/
noncomputable def literalKwInfinity (p : ℕ) : ℚ⟦X⟧ :=
  C (3*5^(p-1) : ℚ)*C ((-1/4 : ℚ)^p)*(C 4-C 11*X)^p*LaurentPoleTrace.reciprocal^p

theorem literalKwInfinity_unit (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    literalKwInfinity p = C (-3*5^(p-1) : ℚ)*actualUnit p (1/4 : ℚ) 4 (11/4) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hlin : (C (-1/4 : ℚ) : ℚ⟦X⟧)*(C 4-C 11*X) = -linearFactor (11/4 : ℚ) := by
    unfold linearFactor
    rw [mul_sub,←mul_assoc,←map_mul,←map_mul]
    norm_num
    ring
  have hs : (C (-3*5^(p-1) : ℚ) : ℚ⟦X⟧)=-C (3*5^(p-1) : ℚ) := by
    rw [show (-3*5^(p-1) : ℚ)=-(3*5^(p-1)) by ring,map_neg]
  unfold literalKwInfinity
  rw [map_pow]
  calc
    _ = C (3*5^(p-1) : ℚ)*(C (-1/4 : ℚ)*(C 4-C 11*X))^p*
        LaurentPoleTrace.reciprocal^p := by rw [mul_pow]; ring
    _ = -C (3*5^(p-1) : ℚ)*linearFactor (11/4 : ℚ)^p*
        LaurentPoleTrace.reciprocal^p := by rw [hlin,hodd.neg_pow]; ring
    _ = _ := by
      rw [hs,actualUnit_power,literal_unitInverse_infinity,mul_pow]
      ring

theorem literalKwInfinity_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    literalKwInfinity p =
      C (-3*5^(p-1) : ℚ)*frobeniusUnit p (1/4 : ℚ) 4 (11/4)+
        C (p : ℚ)*(C (-3*5^(p-1) : ℚ)*actualUnitCarryQ p) := by
  have hCQ : actualUnitCarryQ p=actualUnitCarry p (1/4 : ℚ) 4 (11/4) := by
    obtain ⟨ha,hb,hc⟩ := actual_parameters_rational p hp
    rw [←actualUnitCarryIntegral_value p hp,actualUnitCarryIntegral,
      actualUnitCarry_map _ p (by omega)]
    simp only [Subring.subtype_apply,ha,hb,hc]
  rw [literalKwInfinity_unit p (by omega),actualUnit_firstTaylor p (by omega),hCQ]
  have hpC : (p : ℚ⟦X⟧)=C (p : ℚ) := by simp
  rw [hpC]
  ring

noncomputable def finiteLogSeries (p : ℕ) [Fact p.Prime] (a : ZMod p) : (ZMod p)⟦X⟧ :=
  ∑ j ∈ Finset.Ico 1 p, C (a^j/(j : ZMod p))*X^j

theorem binomialCarry_field (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    binomialCarry p a = finiteLogSeries p a := by
  unfold binomialCarry finiteLogSeries
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hsign : (-1 : ZMod p)^(j-1)*(-1)^j = -1 := by
    rw [show j = (j-1)+1 by omega, pow_succ]
    calc
      (-1 : ZMod p)^(j-1)*((-1)^(j-1)*(-1)) = -((-1 : ZMod p)^(j-1))^2 := by ring
      _ = -1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
  have hs : -((((p.choose j : ℤ)/(p : ℤ)) : ℤ) : ZMod p)*(-a)^j =
      a^j/(j : ZMod p) := by
    rw [WPFiniteInversion.divided_choose_cast p j hj, neg_pow]
    simp only [div_eq_mul_inv]
    linear_combination -(a^j*(j : ZMod p)⁻¹)*hsign
  rw [← map_neg, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, ← neg_mul, ← map_neg]
  rw [neg_mul] at hs
  rw [hs]

theorem finiteLogSeries_coeff (p n : ℕ) [Fact p.Prime] (a : ZMod p) :
    coeff n (finiteLogSeries p a) = if n ∈ Finset.Ico 1 p then a^n/(n : ZMod p) else 0 := by
  simp [finiteLogSeries,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]

noncomputable def fieldCarry (p : ℕ) [Fact p.Prime] (a b c : ZMod p) : (ZMod p)⟦X⟧ :=
  (phaseFactor p c*(finiteLogSeries p a*phaseFactor p b+
    finiteLogSeries p b*phaseFactor p a)-
    finiteLogSeries p c*phaseFactor p a*phaseFactor p b)*
    unitInverse (phaseFactor p a*phaseFactor p b)*
    unitInverse (phaseFactor p a*phaseFactor p b)

theorem actualUnitCarry_field (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a b c : ZMod p) :
    actualUnitCarry p a b c = fieldCarry p a b c := by
  have ha := linearFactor_firstTaylor p hp a
  have hb := linearFactor_firstTaylor p hp b
  have hz : (p : (ZMod p)⟦X⟧) = 0 := by
    simpa only [map_natCast,map_zero] using
      congrArg (C : ZMod p →+* (ZMod p)⟦X⟧) (ZMod.natCast_self p)
  rw [hz,zero_mul,sub_zero] at ha hb
  simp only [actualUnitCarry, carryNumerator, binomialCarry_field, ha,hb,
    hz, zero_mul, sub_zero, fieldCarry]

theorem actual_parameters_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (actualA p) = (1/4 : ZMod p) ∧
    residueHom p (actualB p) = (4 : ZMod p) ∧
    residueHom p (actualC p) = (11/4 : ZMod p) := by
  have h4 := smallIntegralInverse_field p 4 (by omega) (by omega)
  simp only [Nat.cast_ofNat] at h4
  constructor
  · simpa only [actualA, one_div] using h4
  constructor
  · simp only [actualB, map_ofNat]
  · simp only [actualC, map_mul, map_ofNat, h4, div_eq_mul_inv]

theorem actualUnitCarryIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.map (residueHom p) (actualUnitCarryIntegral p) =
      fieldCarry p (1/4 : ZMod p) 4 (11/4) := by
  obtain ⟨ha,hb,hc⟩ := actual_parameters_field p hp
  rw [actualUnitCarryIntegral, actualUnitCarry_map _ p (by omega), ha,hb,hc,
    actualUnitCarry_field p (by omega)]

section Jets
variable {K : Type*} [CommRing K]

/-- An exact remainder of degree at least n, rather than an assigned truncated value. -/
def HasRemainder (n : ℕ) (F G : K⟦X⟧) : Prop := ∃ H, F=G+X^n*H

theorem HasRemainder.refl (n : ℕ) (F : K⟦X⟧) : HasRemainder n F F := by
  exact ⟨0, by ring⟩

theorem HasRemainder.add {n : ℕ} {F G P Q : K⟦X⟧}
    (h : HasRemainder n F G) (k : HasRemainder n P Q) :
    HasRemainder n (F+P) (G+Q) := by
  obtain ⟨H,rfl⟩ := h
  obtain ⟨J,rfl⟩ := k
  exact ⟨H+J, by ring⟩

theorem HasRemainder.sub {n : ℕ} {F G P Q : K⟦X⟧}
    (h : HasRemainder n F G) (k : HasRemainder n P Q) :
    HasRemainder n (F-P) (G-Q) := by
  obtain ⟨H,rfl⟩ := h
  obtain ⟨J,rfl⟩ := k
  exact ⟨H-J, by ring⟩

theorem HasRemainder.mul {n : ℕ} {F G P Q : K⟦X⟧}
    (h : HasRemainder n F G) (k : HasRemainder n P Q) :
    HasRemainder n (F*P) (G*Q) := by
  obtain ⟨H,rfl⟩ := h
  obtain ⟨J,rfl⟩ := k
  exact ⟨G*J+H*Q+X^n*H*J, by ring⟩

theorem HasRemainder.trans {n : ℕ} {F G P : K⟦X⟧}
    (h : HasRemainder n F G) (k : HasRemainder n G P) : HasRemainder n F P := by
  obtain ⟨H,rfl⟩ := h
  obtain ⟨J,rfl⟩ := k
  exact ⟨J+H, by ring⟩

theorem HasRemainder.coeff {n : ℕ} {F G : K⟦X⟧}
    (h : HasRemainder n F G) (j : ℕ) (hj : j < n) : coeff j F=coeff j G := by
  obtain ⟨H,rfl⟩ := h
  rw [map_add]
  have hz : PowerSeries.coeff j (X^n*H) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul',if_neg (by omega)]
  rw [hz, add_zero]

theorem phaseInverse_firstJet (p : ℕ) (hp : 0 < p) (a : K) :
    HasRemainder (2*p) (unitInverse (phaseFactor p a)) (1+C (a^p)*X^p) := by
  have hi := unitInverse_right (phaseFactor p a) (phaseFactor_constant p hp a)
  refine ⟨C (a^p)^2*unitInverse (phaseFactor p a), ?_⟩
  have hpow : (X : K⟦X⟧)^(2*p)=(X^p)^2 := by rw [Nat.mul_comm, pow_mul]
  rw [hpow]
  dsimp only [phaseFactor] at hi ⊢
  linear_combination (1+C (a^p)*X^p)*hi

theorem phaseProductInverse_firstJet (p : ℕ) (hp : 0 < p) (a b : K) :
    HasRemainder (2*p) (unitInverse (phaseFactor p a*phaseFactor p b))
      (1+(C (a^p)+C (b^p))*X^p) := by
  have hB : constantCoeff (phaseFactor p a*phaseFactor p b) = 1 := by
    rw [map_mul, phaseFactor_constant p hp, phaseFactor_constant p hp, one_mul]
  have hi := unitInverse_right (phaseFactor p a*phaseFactor p b) hB
  refine ⟨((C (a^p)+C (b^p))^2-C (a^p)*C (b^p)-
    (C (a^p)+C (b^p))*C (a^p)*C (b^p)*X^p)*
      unitInverse (phaseFactor p a*phaseFactor p b), ?_⟩
  have hpow : (X : K⟦X⟧)^(2*p)=(X^p)^2 := by rw [Nat.mul_comm, pow_mul]
  rw [hpow]
  dsimp only [phaseFactor] at hi ⊢
  linear_combination (1+(C (a^p)+C (b^p))*X^p)*hi

theorem frobeniusUnit_firstJet (p : ℕ) (hp : 0 < p) (a b c : K) :
    HasRemainder (2*p) (frobeniusUnit p a b c)
      (1+C (a^p+b^p-c^p)*X^p) := by
  have hi := phaseProductInverse_firstJet p hp a b
  have hm := (HasRemainder.refl (2*p) (phaseFactor p c)).mul hi
  apply hm.trans
  refine ⟨-C (c^p)*(C (a^p)+C (b^p)), ?_⟩
  have hpow : (X : K⟦X⟧)^(2*p)=(X^p)^2 := by rw [Nat.mul_comm,pow_mul]
  rw [hpow]
  unfold phaseFactor
  simp only [map_add,map_sub]
  ring

theorem frobeniusUnit_coeff_firstPhase (p : ℕ) (hp : 0 < p) (a b c : K) :
    coeff p (frobeniusUnit p a b c)=a^p+b^p-c^p := by
  rw [(frobeniusUnit_firstJet p hp a b c).coeff p (by omega)]
  rw [map_add,PowerSeries.coeff_C_mul_X_pow]
  simp [Nat.ne_of_gt hp]

end Jets

noncomputable def firstTwoPhases (p : ℕ) [Fact p.Prime] (a b c : ZMod p) : (ZMod p)⟦X⟧ :=
  finiteLogSeries p a+finiteLogSeries p b-finiteLogSeries p c+
    X^p*(C (a+b-c+a)*finiteLogSeries p a+
      C (a+b-c+b)*finiteLogSeries p b-C (a+b)*finiteLogSeries p c)

theorem fieldCarry_firstTwoPhases (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a b c : ZMod p) :
    HasRemainder (2*p) (fieldCarry p a b c) (firstTwoPhases p a b c) := by
  let Ea := finiteLogSeries p a
  let Eb := finiteLogSeries p b
  let Ec := finiteLogSeries p c
  let E0 := Ea+Eb-Ec
  let E1 := -(C b+C c)*Ea-(C a+C c)*Eb+(C a+C b)*Ec
  let H := phaseFactor p c*(Ea*phaseFactor p b+Eb*phaseFactor p a)-
    Ec*phaseFactor p a*phaseFactor p b
  let I := unitInverse (phaseFactor p a*phaseFactor p b)
  have hi : HasRemainder (2*p) I (1+(C a+C b)*X^p) := by
    simpa only [I, ZMod.pow_card] using phaseProductInverse_firstJet p (by omega) a b
  have hh : HasRemainder (2*p) H (E0+X^p*E1) := by
    refine ⟨C c*C b*Ea+C c*C a*Eb-C a*C b*Ec, ?_⟩
    have hpow : (X : (ZMod p)⟦X⟧)^(2*p)=(X^p)^2 := by rw [Nat.mul_comm, pow_mul]
    rw [hpow]
    dsimp only [H,E0,E1,phaseFactor]
    simp only [ZMod.pow_card]
    ring
  have hcarry : HasRemainder (2*p) (fieldCarry p a b c)
      ((E0+X^p*E1)*(1+(C a+C b)*X^p)*(1+(C a+C b)*X^p)) := by
    exact (hh.mul hi).mul hi
  apply hcarry.trans
  refine ⟨(C a+C b)^2*E0+2*(C a+C b)*E1+X^p*(C a+C b)^2*E1, ?_⟩
  have hpow : (X : (ZMod p)⟦X⟧)^(2*p)=(X^p)^2 := by rw [Nat.mul_comm, pow_mul]
  rw [hpow]
  dsimp only [firstTwoPhases,E0,E1,Ea,Eb,Ec]
  simp only [map_add, map_sub]
  ring

noncomputable def literalFirstTwoPhases (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ :=
  finiteLogSeries p (1/4)+finiteLogSeries p 4-finiteLogSeries p (11/4)+
    X^p*(C (7/4 : ZMod p)*finiteLogSeries p (1/4)+
      C (11/2 : ZMod p)*finiteLogSeries p 4-C (17/4 : ZMod p)*finiteLogSeries p (11/4))

theorem firstTwoPhases_literal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    firstTwoPhases p (1/4 : ZMod p) 4 (11/4) = literalFirstTwoPhases p := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : ZMod p)+4-11/4+1/4 = 7/4 := by field_simp [h4]; ring
  have hb : (1/4 : ZMod p)+4-11/4+4 = 11/2 := by field_simp [h2,h4]; ring
  have hc : (1/4 : ZMod p)+4 = 17/4 := by field_simp [h4]; ring
  unfold firstTwoPhases literalFirstTwoPhases
  rw [ha,hb,hc]

/-- The full required range includes both j and p+j, with no top-band deletion. -/
theorem actualUnitCarry_coeff_field (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hn : n < 2*p) :
    residueHom p (coeff n (actualUnitCarryIntegral p)) =
      coeff n (literalFirstTwoPhases p) := by
  rw [← coeff_map, actualUnitCarryIntegral_field p hp]
  rw [(fieldCarry_firstTwoPhases p (by omega) (1/4 : ZMod p) 4 (11/4)).coeff n hn,
    firstTwoPhases_literal p hp]

theorem actualUnitCarry_selected_phase (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (coeff p (actualUnitCarryIntegral p))=0 := by
  rw [actualUnitCarry_coeff_field p p hp (by omega),literalFirstTwoPhases]
  simp only [map_add,map_sub,PowerSeries.coeff_X_pow_mul',le_refl,if_pos,
    Nat.sub_self,PowerSeries.coeff_C_mul,finiteLogSeries_coeff]
  simp

noncomputable def actualKwCarryIntegral (p : ℕ) [Fact p.Prime] :
    (integralRationals p)⟦X⟧ := C (-3*5^(p-1))*actualUnitCarryIntegral p

/-- The whole original rational weight difference is divided in Q. -/
noncomputable def actualKwCarryQ (p : ℕ) : ℚ⟦X⟧ :=
  C (1/(p : ℚ))*(literalKwInfinity p-
    C (-3*5^(p-1) : ℚ)*frobeniusUnit p (1/4 : ℚ) 4 (11/4))

theorem actualKwCarryIntegral_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.map (integralRationals p).subtype (actualKwCarryIntegral p)=actualKwCarryQ p := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : p ≠ 0)
  rw [actualKwCarryIntegral,map_mul,PowerSeries.map_C,actualUnitCarryIntegral_value p hp]
  change C (-3*5^(p-1) : ℚ)*actualUnitCarryQ p=actualKwCarryQ p
  unfold actualKwCarryQ
  rw [literalKwInfinity_firstTaylor p hp]
  have hc : (C (1/(p : ℚ)) : ℚ⟦X⟧)*C (p : ℚ)=1 := by
    rw [←map_mul,one_div_mul_cancel hpq,map_one]
  symm
  calc
    _ = C (1/(p : ℚ))*C (p : ℚ)*
        (C (-3*5^(p-1) : ℚ)*actualUnitCarryQ p) := by ring
    _ = _ := by rw [hc,one_mul]

theorem actualKwCarryQ_coeff_integral (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coeff n (actualKwCarryQ p) ∈ integralRationals p := by
  rw [←actualKwCarryIntegral_value p hp,coeff_map]
  exact (coeff n (actualKwCarryIntegral p)).property

theorem actualKwCarry_coeff_field (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hn : n < 2*p) :
    residueHom p (coeff n (actualKwCarryIntegral p)) =
      (-3 : ZMod p)*coeff n (literalFirstTwoPhases p) := by
  have hs : residueHom p (-3*5^(p-1) : integralRationals p)=(-3 : ZMod p) := by
    simp only [map_mul,map_neg,map_ofNat,map_pow,ActualKwFieldTrace.five_fermat p hp,mul_one]
  rw [actualKwCarryIntegral,PowerSeries.coeff_C_mul,map_mul,hs,
    actualUnitCarry_coeff_field p n hp hn]

end WPFieldAssembly.ActualKwFirstCarry
