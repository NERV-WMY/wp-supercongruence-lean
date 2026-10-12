import WPFieldAssembly.SourceClosureVbalDigits
import WPFieldAssembly.ActualComparisonFrobenius
import WPFieldAssembly.ActualProperEndpointAttachment
import WPFieldAssembly.ActualLogCAttachment
import WPFieldAssembly.ActualIntegralGreenTrace
import WPFieldAssembly.ActualComparisonF1Attachment
import WPFieldAssembly.ActualEndpointAlphabet
import WPKFifthEndpoint

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPActualRankTwoLegendreField
  WPFieldAssembly.ActualEntropyPolynomial WPFieldAssembly.ActualEntropyEndpoints
  WPFieldAssembly.ActualFiniteEntropyCarry WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualEntropyFifth WPFieldAssembly.ActualRationalPhaseCarry
  WPFieldAssembly.ActualWeightedF0Carry WPFieldAssembly.ActualComparisonKwAttachment
  WPFieldAssembly.ActualComparisonFrobenius WPFieldAssembly.ActualProperEndpointCarry
  WPFieldAssembly.ActualProperEndpointAttachment WPFieldAssembly.ActualLogCAttachment
  WPFieldAssembly.ActualLogCCarry WPFieldAssembly.ActualJointGreen
  WPFieldAssembly.ActualBalancedGreenTransfer WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.ActualKwSeriesAttachment
  WPFieldAssembly.ActualSB101Trace WPFieldAssembly.ActualIntegralGreenTrace

namespace WPFieldAssembly.ActualVbalCarry

set_option maxHeartbeats 1600000

theorem original_bare_trace (L : ℚ[T;T⁻¹]) : dlogQtrace L=rationalDlogQ L := by
  change inverseAtrace (3*T (-1)*(4-11*T 1)*L)=
    LaurentPoleTrace.trace 1 (3*T (-1)*(4-11*T 1)*L)
  exact (trace_one_eq_inverseAtrace _).symm

theorem original_weighted_trace (p : ℕ) (L : ℚ[T;T⁻¹]) :
    weightedDlogQtrace p L=actualWeightedTrace p L := by
  change LaurentPoleTrace.trace (p+1)
      (LaurentPolynomial.C (9*(5 : ℚ)^(p-1))*T ((p-1 : ℕ) : ℤ)*
        (4*T 1-11)^p*(4-11*T 1)*L)=
    LaurentPoleTrace.trace (p+1) ((originalWeightedNumerator p).toLaurent*L)
  rw [originalWeightedNumerator_laurent]

/-- The literal conic logarithm has its exact three rational endpoints. -/
theorem actual_bare_conic_trace (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    dlogQtrace (finiteConicLogQ p).toLaurent=
      -(3/2 : ℚ)*rationalHarmonic ((p-1)/2)+3*(movingEvenQ p).eval (121/125) := by
  rw [original_bare_trace,rationalDlogQ_endpoint,endpointTrace_polynomial,
    finiteConicLogQ_eq_narrow p hp,coeff_zero_eq_eval_zero]
  have ha : (1-WPActualPullbackSource.Vpolynomial : ℚ[X]).eval (1/4)=1 := by
    norm_num [WPActualPullbackSource.Vpolynomial]
  have hb : (1-WPActualPullbackSource.Vpolynomial : ℚ[X]).eval 4=1 := by
    norm_num [WPActualPullbackSource.Vpolynomial]
  have h0 : (1-WPActualPullbackSource.Vpolynomial : ℚ[X]).eval 0=121/125 := by
    norm_num [WPActualPullbackSource.Vpolynomial]
  simp only [conicLogQ,eval_comp,ha,hb,h0,
    ActualWeightedF0Carry.movingEvenQ_endpoint_one]
  ring

theorem actual_fifth_rational_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (movingEvenQ p).eval (121/125)=(11/5 : ℚ)*literalFifthConstantQ p-
      (16/5 : ℚ)*literalQuotientQ p 2+(3/2 : ℚ)*literalQuotientQ p 5+
      (p : ℚ)*(actualFifthCarryIntegral p).val := by
  have h := actualFifthCarryIntegral_value p hp
  unfold actualFifthFirstDifferenceQ at h
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs := (eq_div_iff hpq).mp h
  dsimp only [literalQuotientQ]
  linear_combination -hs

/-- The original rational weighted trace is split only after its actual p-division. -/
theorem actual_weighted_comparison_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    weightedDlogQtrace p (comparisonRational p hp)=(weightedF0I p).val+
      (p : ℚ)*(comparisonKwCarryI p hp).val := by
  have hc := comparisonKwCarryI_value p hp
  have h0 : (-3*(5 : ℚ)^(p-1))*
      seriesWeightedTrace (ActualKwFirstCarry.frobeniusUnit p (1/4 : ℚ) 4 (11/4))
        (comparisonRational p hp)=(weightedF0I p).val := by
    rw [comparison_frobenius_trace p hp,weightedF0I_value p hp]
    obtain ⟨hk,hb⟩ := rational_phase_values p hp
    rw [hk,hb,AendI_value p hp,DendI_value p hp]
    unfold actualAendQ actualDendQ literalFifthConstantQ literalConstantQ
    ring
  rw [h0] at hc
  rw [original_weighted_trace]
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hpq] at hc
  linear_combination -hc

/-- Every summand is the integral realization of its original rational first difference. -/
noncomputable def vbalCarryI (p : ℕ) [Fact p.Prime] (hp : 19≤p) : integralRationals p :=
  3*WPFiniteCarry.integralEvenLogEndpointCarry p hp-3*actualFifthCarryIntegral p-
    weightedF0CarryI p hp-comparisonKwCarryI p hp+3*endpointCarryIntegral p hp-
    2*endpointOriginIntegral p*logCDigitIntegral p-
    2*(p : integralRationals p)*endpointCarryIntegral p hp*logCDigitIntegral p

/-- Exact SB102 before reduction, preserving the literal R0 and the NC95 minus sign. -/
theorem actual_vBalanced_p_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    vBalancedQ p hp=(p : ℚ)*(vbalCarryI p hp).val := by
  have hw := congrArg (integralRationals p).subtype (weightedF0I_firstTaylor p hp)
  simp only [map_add,map_sub,map_mul,map_ofNat,map_natCast,Subring.subtype_apply,
    smallIntegralInverse_value p 5 (by omega) (by omega),literalConstantI_value p hp] at hw
  have hh := congrArg (integralRationals p).subtype (balancedProper_hstar_firstTaylor p hp)
  simp only [map_neg,map_add,map_mul,map_natCast,Subring.subtype_apply] at hh
  have hh' : ((ActualBalancedCarry.balancedProperIntegral p hp).eval 1).val=
      -(endpointOriginIntegral p).val-(p : ℚ)*(endpointCarryIntegral p hp).val := by
    linear_combination -hh
  have hC := congrArg (integralRationals p).subtype (actual_finite_C_firstTaylor p hp)
  simp only [map_add,map_mul,map_neg,map_ofNat,map_natCast,Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega)] at hC
  have hW : (weightedF0I p).val=(33/5 : ℚ)*
      (literalQuotientQ p 2-literalFifthConstantQ p)+(p : ℚ)*(weightedF0CarryI p hp).val := by
    change (weightedF0I p).val=(33/5 : ℚ)*
      ((quotientI p 2).val-literalConstantQ p)+(p : ℚ)*(weightedF0CarryI p hp).val
    linear_combination hw
  rw [vBalancedQ,actual_bare_conic_trace p hp,actual_fifth_rational_source p hp,
    actual_half_harmonic_first_digit p hp,actual_weighted_comparison_source p hp,hW]
  change _+2*((ActualBalancedCarry.balancedProperIntegral p hp).eval 1).val*
      (finiteLogCIntegral p hp).val=_
  rw [hh',hC,endpointOriginIntegral_value p hp]
  change _=(p : ℚ)*(integralRationals p).subtype (vbalCarryI p hp)
  simp only [vbalCarryI,map_sub,map_add,map_mul,map_ofNat,map_natCast,Subring.subtype_apply,
    endpointOriginIntegral_value p hp]
  unfold WPFirstResidue.LiteralNormalization.literalR0 literalQuotientQ
  ring

theorem vbalCarryI_value (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (vbalCarryI p hp).val=vBalancedQ p hp/(p : ℚ) := by
  rw [actual_vBalanced_p_source p hp]
  have hpq : (p : ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp [hpq]

theorem actual_vBalancedDividedIntegral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    vBalancedDividedIntegral p hp=vbalCarryI p hp := by
  apply Subtype.ext
  exact (vbalCarryI_value p hp).symm

/-- The field digit is the reduction of the actual rational V_bal/p. -/
theorem vbalCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (vbalCarryI p hp)=
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
      3*residueHom p (actualFifthCarryIntegral p)-
      (11/5 : ZMod p)*residueHom p (literalR1Integral p hp)-
      residueHom p (phaseCarryI p hp)-residueHom p (comparisonKwCarryI p hp)+
      3*residueHom p (endpointCarryIntegral p hp)-
      2*residueHom p (endpointOriginIntegral p)*residueHom p (logCDigitIntegral p) := by
  have hH : residueHom p (WPFiniteCarry.integralEvenLogEndpointCarry p hp)=
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2 :=
    actual_entropy_endpoint_field p hp
  rw [vbalCarryI]
  simp only [map_sub,map_add,map_mul,map_ofNat,map_natCast,ZMod.natCast_self,
    hH,weightedF0CarryI_field p hp]
  ring

theorem actual_vBalanced_field_Tw (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (vBalancedDividedIntegral p hp)=
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
      3*residueHom p (actualFifthCarryIntegral p)-
      (11/5 : ZMod p)*residueHom p (literalR1Integral p hp)-
      residueHom p (phaseCarryI p hp)-ActualComparisonF1Attachment.actualTwField p+
      3*residueHom p (endpointCarryIntegral p hp)-
      2*residueHom p (endpointOriginIntegral p)*residueHom p (logCDigitIntegral p) := by
  rw [actual_vBalancedDividedIntegral p hp,vbalCarryI_field p hp,
    ActualComparisonF1Attachment.comparisonKwCarryI_Tw p hp]

/-- The original divided value has the finite SB102 alphabet, with its full F1 trace. -/
theorem actual_vBalanced_field_alphabet (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (vBalancedDividedIntegral p hp)=
      (69/10 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
      (63/10 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+
      (9/8 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2-
      (11/10 : ZMod p)*WPFiniteInversion.R p (-2 : ZMod p)-
      3*residueHom p (actualFifthCarryIntegral p)-residueHom p (phaseCarryI p hp)-
      ActualComparisonF1Attachment.actualTwField p+
      (4*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
        3*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p))*
          ActualLogCCarry.logCFirstDigit p := by
  rw [actual_vBalanced_field_Tw p hp,ActualEndpointAlphabet.literalR1Integral_alphabet p hp,
    endpointCarryIntegral_field p hp,endpointOriginIntegral_field p hp,
    ActualLogCCarry.logCDigitIntegral_field p hp]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h8 : (8 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 8 (by omega) (by omega)
  have h10 : (10 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 10 (by omega) (by omega)
  field_simp [h2,h3,h4,h5,h8,h10]
  ring

section CharacteristicP

variable {K : Type*} [Field K]

/-- The fifth reduction retains the full original F1 trace and conic C digit. -/
theorem actual_vBalanced_field_alphabet_K (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (vBalancedDividedIntegral p hp))=
      (69/10 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)^2-
      (63/10 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteInversion.integerFermatQuotient p 3 : K)+
      (9/8 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2-
      (11/10 : K)*WPFiniteField.R p (-2 : K)-
      3*actualFifthCarryField p u-
      (ZMod.castHom (dvd_refl p) K) (residueHom p (phaseCarryI p hp))-
      (ZMod.castHom (dvd_refl p) K) (ActualComparisonF1Attachment.actualTwField p)+
      (4*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
        3*(WPFiniteInversion.integerFermatQuotient p 3 : K))*
          (ZMod.castHom (dvd_refl p) K) (ActualLogCCarry.logCFirstDigit p) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (actual_vBalanced_field_alphabet p hp)
  simp only [map_add,map_sub,map_mul,map_pow,map_div₀,map_ofNat,map_intCast,
    ←WPFiniteField.R_castHom,map_neg,
    actualFifthCarryIntegral_field p hp u hu] at h
  exact h

end CharacteristicP

end WPFieldAssembly.ActualVbalCarry
