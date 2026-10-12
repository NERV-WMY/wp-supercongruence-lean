import WPFieldAssembly.ActualEntropyFifth
import WPFieldAssembly.ActualWeightedF0Carry
import WPFieldAssembly.ActualLogCCarry

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPActualRankTwoLegendreField
  WPFieldAssembly.ActualEntropyPolynomial WPFieldAssembly.ActualEntropyFifth
  WPFieldAssembly.ActualRationalPhaseCarry WPFieldAssembly.ActualWeightedF0Carry
  WPFieldAssembly.ActualLogCCarry

namespace WPFieldAssembly.ActualVbalCarry

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- The half logarithm keeps its full upper endpoint in the even finite trace. -/
theorem halfLog_square_entropy (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (z : K) :
    ActualLogCCarry.halfLog ((p-1)/2) (z^2)=2*WPFiniteField.E p z := by
  have he : (WPFiniteLVSource.evenSquared p : K[X]).eval (z^2)=
      WPFiniteField.E p z := by
    have h := congrArg (fun P : K[X] => P.eval z)
      (WPFiniteLVSource.evenSquared_square p hp)
    simp only [eval_comp,eval_pow,eval_X] at h
    rw [h]
    simp only [WPFiniteKSource.EP,eval_mul,eval_C,eval_add,eval_comp,eval_neg,
      eval_X,WPFiniteAffineLog.LP_eval_eq,WPFiniteField.E,div_eq_mul_inv]
    ring
  have hs : ActualLogCCarry.halfLog ((p-1)/2) (z^2)=
      ∑ j ∈ Finset.Ico 1 ((p-1)/2+1), (z^2)^j/(j : K) := by
    rw [←Finset.sum_Ico_add' (fun j : ℕ => (z^2)^j/(j : K)) 0 ((p-1)/2) 1]
    simp only [ActualLogCCarry.halfLog,Nat.Ico_zero_eq_range]
  rw [hs,←he,WPFiniteLVSource.evenSquared,eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hn := WPFiniteWSource.half_exponent p hp
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hj0 : (j : K)≠0 := WPFiniteField.denominator_ne_zero p j
    (Finset.mem_Ico.mpr (by omega))
  simp only [eval_mul,eval_C,eval_pow,eval_X]
  field_simp [h2,hj0]

/-- The conic first digit is attached to both even endpoints, retaining Q11's carrier. -/
theorem logCDigitIntegral_field_fifth (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (logCDigitIntegral p))=
      (3/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
      (11/5 : K)*(WPFiniteField.E p (2*w)-WPFiniteField.E p w-
        WPFifthEntropy.C p u) := by
  rw [ActualLogCCarry.logCDigitIntegral_base_change p hp]
  have hu2 : (2*u)^2=(4/5 : K) := by rw [mul_pow,hu]; ring
  have hw2 : (2*w)^2=(12/11 : K) := by rw [mul_pow,hw]; ring
  rw [←hw,←hw2,←hu2,←hu,
    halfLog_square_entropy p hp w,halfLog_square_entropy p hp (2*w),
    halfLog_square_entropy p hp (2*u),halfLog_square_entropy p hp u]
  unfold WPFifthEntropy.C
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h5,h10]
  ring

/-- The literal endpoint difference is the same fifth letter after actual reduction. -/
theorem literalConstantI_field_fifth (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (literalConstantI p))=
      WPFifthEntropy.C p u := by
  let φ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hmove : ((entropyIntegral p).map (residueHom p)).map φ=
      ((ActualEntropyPolynomial.movingEvenIntegral p).map (residueHom p)).map φ := by
    have hm : (entropyIntegral p).map (residueHom p)=
        (ActualEntropyPolynomial.movingEvenIntegral p).map (residueHom p) := by
      rw [entropyIntegral,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
        map_natCast,ZMod.natCast_self,C_0,zero_mul,sub_zero]
    exact congrArg (fun P : (ZMod p)[X] => P.map φ) hm
  have h5 : φ (residueHom p (smallIntegralInverse p 5))=(1/5 : K) := by
    rw [smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [map_inv₀,Nat.cast_ofNat,one_div]
    rw [map_ofNat]
  have hpoint₁ : u^2=φ (residueHom p (smallIntegralInverse p 5)) := hu.trans h5.symm
  have hpoint₂ : (2*u)^2=φ (residueHom p (4*smallIntegralInverse p 5)) := by
    rw [map_mul,map_ofNat,map_mul,map_ofNat,h5,mul_pow,hu]
    ring
  have h₁ := entropyIntegral_base_change_eval p hp u
  have h₂ := entropyIntegral_base_change_eval p hp (2*u)
  change (((entropyIntegral p).map (residueHom p)).map φ).eval (u^2)=_ at h₁
  change (((entropyIntegral p).map (residueHom p)).map φ).eval ((2*u)^2)=_ at h₂
  rw [hmove,hpoint₁,eval_map_apply,eval_map_apply] at h₁
  rw [hmove,hpoint₂,eval_map_apply,eval_map_apply] at h₂
  change φ (residueHom p (literalConstantI p))=_
  rw [literalConstantI,map_sub,map_sub,h₂,h₁]
  rfl

/-- Both prime classes use the same original divided value in an arbitrary extension. -/
theorem phaseCarryI_field_fifth (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=(1/5 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (phaseCarryI p hp))=
      (33/5 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : K)-WPFifthEntropy.C p u)+
      (4/5 : K)*(13*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
        (11/4 : K)*(WPFiniteInversion.integerFermatQuotient p 11 : K))*
          ((9/4 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)+
            3*WPFifthEntropy.C p u)+
      (62/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : K)+
          (3/4 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (phaseCarryI_alphabet p hp)
  simpa only [map_add,map_sub,map_mul,map_div₀,map_ofNat,map_intCast,
    literalConstantI_field_fifth p hp u hu] using h

end WPFieldAssembly.ActualVbalCarry
