import WPFieldAssembly.ActualEntropyEndpoints
import WPFieldAssembly.ActualRationalPhaseCarry
import WPFiniteLoop

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPActualRankTwoLegendreField
  WPFieldAssembly.ActualEntropyPolynomial WPFieldAssembly.ActualEntropyEndpoints
  WPFieldAssembly.ActualRationalPhaseCarry

namespace WPFieldAssembly.ActualWeightedF0Carry

set_option maxHeartbeats 1200000

/-- This is the literal fifth-point endpoint difference, distinct from the conic C coefficient. -/
noncomputable def literalConstantI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (ActualEntropyPolynomial.movingEvenIntegral p).eval (4*smallIntegralInverse p 5)-
    (ActualEntropyPolynomial.movingEvenIntegral p).eval (smallIntegralInverse p 5)

noncomputable def literalConstantQ (p : ℕ) : ℚ :=
  (movingEvenQ p).eval (4/5)-(movingEvenQ p).eval (1/5)

noncomputable def AendI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  2*(ActualEntropyPolynomial.movingEvenIntegral p).eval 4-
    (ActualEntropyPolynomial.movingEvenIntegral p).eval (smallIntegralInverse p 4)-
    (ActualEntropyPolynomial.movingEvenIntegral p).eval 1-3*literalConstantI p

noncomputable def DendI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (ActualEntropyPolynomial.movingEvenIntegral p).eval (smallIntegralInverse p 4)-
    (ActualEntropyPolynomial.movingEvenIntegral p).eval 4

noncomputable def weightedF0I (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (5 : integralRationals p)^(p-1)*smallIntegralInverse p 5*
    ((17-4*kappaI p)*AendI p+4*betaI p*DendI p)

/-- The exact phase carry retains the integral units before reduction. -/
noncomputable def phaseCarryI (p : ℕ) [Fact p.Prime] (hp : 19≤p) : integralRationals p :=
  33*smallIntegralInverse p 5*quotientI p 5*(quotientI p 2-literalConstantI p)+
    11*smallIntegralInverse p 5*(p : integralRationals p)*quotientI p 5*
      literalR1Integral p hp-
    4*smallIntegralInverse p 5*(5 : integralRationals p)^(p-1)*
      kappaCarryI p*AendI p+
    4*smallIntegralInverse p 5*(5 : integralRationals p)^(p-1)*
      betaCarryI p*DendI p

noncomputable def weightedF0CarryI (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    integralRationals p :=
  11*smallIntegralInverse p 5*literalR1Integral p hp+phaseCarryI p hp

theorem movingEvenIntegral_eval_value (p : ℕ) [Fact p.Prime]
    (z : integralRationals p) :
    ((ActualEntropyPolynomial.movingEvenIntegral p).eval z).val=
      (movingEvenQ p).eval z.val := by
  change (integralRationals p).subtype
    ((ActualEntropyPolynomial.movingEvenIntegral p).eval z)=_
  rw [←eval_map_apply,ActualEntropyPolynomial.movingEvenIntegral_value]
  simp only [Subring.subtype_apply]

theorem movingEvenQ_endpoint_one (p : ℕ) :
    (movingEvenQ p).eval 1=rationalHarmonic ((p-1)/2)/2 := by
  simp only [movingEvenQ,rankCoefficientPolynomial,eval_finsetSum,
    eval_monomial,one_pow,mul_one]
  rw [Finset.sum_range_succ']
  simp only [ite_true,add_zero]
  unfold rationalHarmonic
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (by omega : j+1≠0)]
  push_cast
  simp only [one_div,mul_inv_rev]
  ring

theorem literalConstantI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (literalConstantI p).val=literalConstantQ p := by
  change (integralRationals p).subtype (literalConstantI p)=_
  rw [literalConstantI,map_sub]
  change ((ActualEntropyPolynomial.movingEvenIntegral p).eval
      (4*smallIntegralInverse p 5)).val-
    ((ActualEntropyPolynomial.movingEvenIntegral p).eval (smallIntegralInverse p 5)).val=_
  rw [movingEvenIntegral_eval_value,movingEvenIntegral_eval_value,
    Subring.coe_mul,smallIntegralInverse_value p 5 (by omega) (by omega)]
  rw [show ((4 : integralRationals p) : ℚ)=(4 : ℚ) from rfl]
  norm_num [literalConstantQ]

theorem AendI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (AendI p).val=2*(movingEvenQ p).eval 4-(movingEvenQ p).eval (1/4)-
      rationalHarmonic ((p-1)/2)/2-3*literalConstantQ p := by
  change (integralRationals p).subtype (AendI p)=_
  simp only [AendI,map_sub,map_mul,map_ofNat,Subring.subtype_apply,
    movingEvenIntegral_eval_value,smallIntegralInverse_value p 4 (by omega) (by omega),
    Subring.coe_one,Nat.cast_ofNat,literalConstantI_value p hp,
    movingEvenQ_endpoint_one]
  rw [show ((4 : integralRationals p) : ℚ)=(4 : ℚ) from rfl]

theorem DendI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (DendI p).val=(movingEvenQ p).eval (1/4)-(movingEvenQ p).eval 4 := by
  change (integralRationals p).subtype (DendI p)=_
  simp only [DendI,map_sub,Subring.subtype_apply,movingEvenIntegral_eval_value,
    smallIntegralInverse_value p 4 (by omega) (by omega),
    Nat.cast_ofNat]
  rw [show ((4 : integralRationals p) : ℚ)=(4 : ℚ) from rfl]

/-- The unchanged integral moving log reduces to the full half-cutoff finite log. -/
theorem movingEvenIntegral_field_eval (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (z : integralRationals p) :
    residueHom p ((ActualEntropyPolynomial.movingEvenIntegral p).eval z)=
      WPFiniteLoop.L ((p-1)/2) (residueHom p z)/2 := by
  rw [←eval_map_apply,ActualEntropyLogAttachment.movingEvenIntegral_actual_field p hp]
  simp only [WPFiniteLVSource.evenSquared,WPFiniteLoop.L,eval_finsetSum,
    eval_mul,eval_C,eval_pow,eval_X,mul_inv_rev,
    div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem AendI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (AendI p)=
      -(9/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)-
        3*residueHom p (literalConstantI p) := by
  rw [AendI,map_sub,map_sub,map_sub,map_mul,map_mul]
  simp only [map_ofNat,movingEvenIntegral_field_eval p hp,
    smallIntegralInverse_field p 4 (by omega) (by omega),map_one]
  norm_num only
  have he := WPFiniteLoop.L_rational_ends (K := ZMod p) p hp
  simp only [one_div] at he
  rw [he.1,he.2.1,he.2.2]
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  field_simp [h2,h4]
  ring

theorem DendI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (DendI p)=
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
        (3/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  rw [DendI,map_sub]
  simp only [movingEvenIntegral_field_eval p hp,
    smallIntegralInverse_field p 4 (by omega) (by omega),map_ofNat]
  norm_num only
  have he := WPFiniteLoop.L_rational_ends (K := ZMod p) p hp
  simp only [one_div] at he
  rw [he.2.1,he.2.2]
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  field_simp [h2,h4]
  ring

/-- This relation uses the canonical rational numerator divided by p. -/
theorem actual_R1_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    AendI p+3*DendI p=3*(quotientI p 2-literalConstantI p)+
      (p : integralRationals p)*literalR1Integral p hp := by
  apply Subtype.ext
  change (integralRationals p).subtype (AendI p+3*DendI p)=
    (integralRationals p).subtype
      (3*(quotientI p 2-literalConstantI p)+(p : integralRationals p)*literalR1Integral p hp)
  simp only [map_add,map_sub,map_mul,map_ofNat,map_natCast,Subring.subtype_apply,
    AendI_value p hp,DendI_value p hp,literalConstantI_value p hp,literalR1Integral_value p hp]
  change 2*(movingEvenQ p).eval 4-(movingEvenQ p).eval (1/4)-
      rationalHarmonic ((p-1)/2)/2-3*literalConstantQ p+
      3*((movingEvenQ p).eval (1/4)-(movingEvenQ p).eval 4)=
    3*(literalQuotientQ p 2-literalConstantQ p)+(p : ℚ)*literalR1Q p
  unfold literalR1Q
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hpq]
  ring

theorem fiveUnit_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (5 : integralRationals p)^(p-1)=1+(p : integralRationals p)*quotientI p 5 := by
  have h5 : (5 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5)
  have h : quotientI p 5*(p : integralRationals p)=
      (5 : integralRationals p)^(p-1)-1 := by
    unfold quotientI
    exact_mod_cast hq
  linear_combination -h

theorem weightedF0I_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (weightedF0I p).val=(5 : ℚ)^(p-1)/5*
      ((17-4*(kappaI p).val)*(AendI p).val+4*(betaI p).val*(DendI p).val) := by
  change (integralRationals p).subtype (weightedF0I p)=_
  simp only [weightedF0I,map_mul,map_add,map_sub,map_pow,map_ofNat,
    Subring.subtype_apply,smallIntegralInverse_value p 5 (by omega) (by omega)]
  ring

/-- The F0 contribution has an exact integral first Taylor expansion. -/
theorem weightedF0I_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    weightedF0I p=33*smallIntegralInverse p 5*(quotientI p 2-literalConstantI p)+
      (p : integralRationals p)*weightedF0CarryI p hp := by
  have hR := congrArg (integralRationals p).subtype (actual_R1_source p hp)
  apply Subtype.ext
  change (integralRationals p).subtype (weightedF0I p)=
    (integralRationals p).subtype
      (33*smallIntegralInverse p 5*(quotientI p 2-literalConstantI p)+
        (p : integralRationals p)*weightedF0CarryI p hp)
  simp only [weightedF0I,weightedF0CarryI,phaseCarryI,kappaI_firstTaylor p hp,
    betaI_firstTaylor p hp,fiveUnit_source p hp,map_add,map_sub,map_mul,map_ofNat,
    map_natCast,map_one,Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 4 (by omega) (by omega),
    smallIntegralInverse_value p 5 (by omega) (by omega)]
  simp only [map_add,map_sub,map_mul,map_ofNat,map_natCast,Subring.subtype_apply] at hR
  linear_combination (11/5 : ℚ)*(1+(p : ℚ)*(quotientI p 5).val)*hR

theorem weightedF0CarryI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (weightedF0CarryI p hp).val=
      ((weightedF0I p).val-(33/5 : ℚ)*
        (literalQuotientQ p 2-literalConstantQ p))/(p : ℚ) := by
  have h := congrArg (integralRationals p).subtype (weightedF0I_firstTaylor p hp)
  simp only [map_add,map_sub,map_mul,map_ofNat,map_natCast,Subring.subtype_apply,
    smallIntegralInverse_value p 5 (by omega) (by omega),literalConstantI_value p hp] at h
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply (eq_div_iff hpq).2
  change (weightedF0CarryI p hp).val*(p : ℚ)=
    (weightedF0I p).val-(33/5 : ℚ)*((quotientI p 2).val-literalConstantQ p)
  linear_combination -h

/-- Only after integral division are the rational phase units reduced. -/
theorem phaseCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (phaseCarryI p hp)=
      (33/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-residueHom p (literalConstantI p))-
      (4/5 : ZMod p)*(13*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (11/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 11 : ZMod p))*
          residueHom p (AendI p)+
      (62/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        residueHom p (DendI p) := by
  have h5unit : residueHom p ((5 : integralRationals p)^(p-1))=1 := by
    rw [fiveUnit_source p hp,map_add,map_one,map_mul,map_natCast,ZMod.natCast_self,
      zero_mul,add_zero]
  simp only [phaseCarryI,map_add,map_sub,map_mul,map_natCast,map_ofNat,quotientI,
    map_intCast,ZMod.natCast_self,h5unit,kappaCarryI_field p hp,betaCarryI_field p hp,
    smallIntegralInverse_field p 5 (by omega) (by omega),mul_one]
  have h4 : (4 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  field_simp [h2,h4,h5]
  ring

theorem weightedF0CarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (weightedF0CarryI p hp)=
      (11/5 : ZMod p)*residueHom p (literalR1Integral p hp)+
        residueHom p (phaseCarryI p hp) := by
  rw [weightedF0CarryI,map_add,map_mul,map_mul,map_ofNat,
    smallIntegralInverse_field p 5 (by omega) (by omega)]
  simp only [div_eq_mul_inv]
  norm_num only

/-- The complete phase carry is expressed in the original q2/q3/q5/q11 letters. -/
theorem phaseCarryI_alphabet (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (phaseCarryI p hp)=
      (33/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-residueHom p (literalConstantI p))+
      (4/5 : ZMod p)*(13*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (11/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 11 : ZMod p))*
          ((9/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
            3*residueHom p (literalConstantI p))+
      (62/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          (3/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)) := by
  rw [phaseCarryI_field p hp,AendI_field p hp,DendI_field p hp]
  ring

end WPFieldAssembly.ActualWeightedF0Carry
