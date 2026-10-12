import WPFieldAssembly.ActualEntropyOdd
import WPFieldAssembly.ActualRationalPhaseCarry
import WPFiniteZSource
import WPLaurentIntegralResidue

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualEntropyOdd WPFieldAssembly.ActualRationalPhaseCarry
open LaurentPolynomial (T T_add T_pow)

namespace WPFieldAssembly.ActualSigmaNormCarrySource

set_option maxHeartbeats 1600000

noncomputable def signedRowI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  (fullEntropyIntegral p).comp (-X)

theorem signedRowI_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1-X : (integralRationals p)[X])^p =
      1-X^p+C (p : integralRationals p)*signedRowI p := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.comp (-X))
    (fullEntropyIntegral_source p)
  simp only [mul_comp,C_comp,pow_comp,add_comp,one_comp,X_comp,sub_comp,
    ←sub_eq_add_neg] at h
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [hodd.neg_pow (X : (integralRationals p)[X])] at h
  simp only [sub_neg_eq_add] at h
  change C (p : integralRationals p)*signedRowI p = (1-X)^p-1+X^p at h
  linear_combination -h

theorem signedRowI_field (p : ℕ) [Fact p.Prime] :
    (signedRowI p).map (residueHom p) = -(WPFiniteAffineLog.LP p : (ZMod p)[X]) := by
  rw [signedRowI,Polynomial.map_comp,Polynomial.map_neg,Polynomial.map_X,
    fullEntropyIntegral_field]
  simp only [neg_comp,comp_assoc,neg_comp,X_comp,neg_neg,comp_X]

private theorem four_inverseI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4 : integralRationals p)*smallIntegralInverse p 4=1 := by
  apply Subtype.ext
  change 4*(smallIntegralInverse p 4).val=1
  rw [smallIntegralInverse_value p 4 (by omega) (by omega)]
  norm_num

noncomputable def leftRowI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  C ((4 : integralRationals p)^p)*
    (signedRowI p).comp (C (smallIntegralInverse p 4)*X)

noncomputable def rightRowI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  -(signedRowI p).comp (4*X)

theorem factor_rows_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4-X : (integralRationals p)[X])^p =
      C ((4 : integralRationals p)^p)-X^p+C (p : integralRationals p)*leftRowI p ∧
    (4*X-1 : (integralRationals p)[X])^p =
      C ((4 : integralRationals p)^p)*X^p-1+C (p : integralRationals p)*rightRowI p := by
  have hleft := congrArg (fun P : (integralRationals p)[X] =>
    C ((4 : integralRationals p)^p)*P.comp (C (smallIntegralInverse p 4)*X))
    (signedRowI_source p hp)
  have hright := congrArg (fun P : (integralRationals p)[X] => -P.comp (4*X))
    (signedRowI_source p hp)
  have hunit := four_inverseI p hp
  have hfac : C (4 : integralRationals p)*(1-C (smallIntegralInverse p 4)*X)=4-X := by
    rw [mul_sub,mul_one,←mul_assoc,←C_mul,hunit,C_1,one_mul]
    simp only [map_ofNat]
  have hend : C ((4 : integralRationals p)^p)*(C (smallIntegralInverse p 4)*X)^p=X^p := by
    rw [mul_pow,←C_pow,←mul_assoc,←C_mul,←mul_pow,hunit,one_pow,C_1,one_mul]
  simp only [sub_comp,add_comp,one_comp,pow_comp,X_comp,mul_comp,C_comp] at hleft hright
  have hlead : C ((4 : integralRationals p)^p)*(1-C (smallIntegralInverse p 4)*X)^p=
      (4-X : (integralRationals p)[X])^p := by rw [C_pow,←mul_pow,hfac]
  rw [hlead] at hleft
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hrlead : -(1-4*X : (integralRationals p)[X])^p=(4*X-1)^p := by
    rw [←hodd.neg_pow (1-4*X : (integralRationals p)[X])]
    congr 1
    ring
  rw [hrlead] at hright
  have hrend : (4*X : (integralRationals p)[X])^p=C ((4 : integralRationals p)^p)*X^p := by
    rw [mul_pow,C_pow,map_ofNat]
  rw [hrend] at hright
  refine ⟨?_,?_⟩
  · rw [leftRowI]
    linear_combination hleft-hend
  · rw [rightRowI]
    linear_combination hright

theorem factor_rows_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (leftRowI p).map (residueHom p) =
      -4*(WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (C (1/4)*X) ∧
    (rightRowI p).map (residueHom p) =
      (WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (4*X) := by
  have hfour : (4 : ZMod p)^p=4 := ZMod.pow_card 4
  have hpower : residueHom p ((4 : integralRationals p)^p)=4 := by
    rw [map_pow,map_ofNat,hfour]
  constructor
  · simp only [leftRowI,Polynomial.map_mul,Polynomial.map_C,hpower,
      Polynomial.map_comp,Polynomial.map_X,signedRowI_field,
      smallIntegralInverse_field p 4 (by omega) (by omega),neg_comp,map_ofNat,one_div]
    ring
  · simp only [rightRowI,Polynomial.map_neg,Polynomial.map_comp,Polynomial.map_mul,
      Polynomial.map_ofNat,Polynomial.map_X,signedRowI_field,neg_comp,neg_neg]

noncomputable def fourCarryI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  8*quotientI p 2+4*(p : integralRationals p)*(quotientI p 2)^2

theorem fourCarryI_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4 : integralRationals p)^p=4+(p : integralRationals p)*fourCarryI p := by
  have h := (phase_end_power_sources p hp).2.1
  rw [twoUnit_source p hp] at h
  rw [h,fourCarryI]
  ring

noncomputable def inverseFiveUnitI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (smallIntegralInverse p 5)^(p-1)

noncomputable def inverseFiveCarryI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -quotientI p 5*inverseFiveUnitI p*(inverseFiveUnitI p+1)

theorem inverseFiveCarryI_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (inverseFiveUnitI p)^2=1+(p : integralRationals p)*inverseFiveCarryI p := by
  have h5z : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 5 (by simpa using h5z)
  have h5 : (5 : integralRationals p)^(p-1)=1+(p : integralRationals p)*quotientI p 5 := by
    have hz : quotientI p 5*(p : integralRationals p)=
        (5 : integralRationals p)^(p-1)-1 := by
      unfold quotientI
      exact_mod_cast hq
    linear_combination -hz
  have hu : (5 : integralRationals p)^(p-1)*inverseFiveUnitI p=1 := by
    apply Subtype.ext
    change (integralRationals p).subtype
      ((5 : integralRationals p)^(p-1)*inverseFiveUnitI p)=1
    simp only [inverseFiveUnitI,map_mul,map_pow,map_ofNat,Subring.subtype_apply,
      smallIntegralInverse_value p 5 (by omega) (by omega),←mul_pow]
    norm_num
  rw [h5] at hu
  rw [inverseFiveCarryI]
  linear_combination (inverseFiveUnitI p+1)*hu

theorem inverseFiveCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (inverseFiveUnitI p)=1 ∧
    residueHom p (inverseFiveCarryI p)=
      -2*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  have hu : residueHom p (inverseFiveUnitI p)=1 := by
    rw [inverseFiveUnitI,map_pow,smallIntegralInverse_field p 5 (by omega) (by omega)]
    apply ZMod.pow_card_sub_one_eq_one
    exact inv_ne_zero (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega))
  refine ⟨hu,?_⟩
  rw [inverseFiveCarryI]
  simp only [map_neg,map_mul,map_add,map_one,hu,quotientI,map_intCast]
  ring

noncomputable def normPhase {R : Type*} [CommRing R] (p : ℕ) : R[T;T⁻¹] :=
  17-4*T (p : ℤ)-4*T (-(p : ℤ))

noncomputable def normAbarI (p : ℕ) [Fact p.Prime] : (integralRationals p)[X] :=
  (4-X)*(4*X-1)

noncomputable def leftEndpointI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C ((4 : integralRationals p)^p)-T (p : ℤ)

noncomputable def rightEndpointI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C ((4 : integralRationals p)^p)*T (p : ℤ)-1

noncomputable def endpointCarryI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C (8*fourCarryI p+(p : integralRationals p)*(fourCarryI p)^2)-
    LaurentPolynomial.C (fourCarryI p)*(T (p : ℤ)+T (-(p : ℤ)))

/-- The complete product includes the p² contribution of the two internal rows. -/
noncomputable def productCarryI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  endpointCarryI p+T (-(p : ℤ))*
    ((leftRowI p).toLaurent*rightEndpointI p+
      leftEndpointI p*(rightRowI p).toLaurent+
      LaurentPolynomial.C (p : integralRationals p)*
        (leftRowI p).toLaurent*(rightRowI p).toLaurent)

theorem productCarryI_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    T (-(p : ℤ))*(normAbarI p).toLaurent^p =
      normPhase p+LaurentPolynomial.C (p : integralRationals p)*productCarryI p := by
  obtain ⟨ha,hb⟩ := factor_rows_source p hp
  have hprod : (normAbarI p).toLaurent^p=
      (leftEndpointI p+LaurentPolynomial.C (p : integralRationals p)*(leftRowI p).toLaurent)*
      (rightEndpointI p+LaurentPolynomial.C (p : integralRationals p)*(rightRowI p).toLaurent) := by
    rw [normAbarI,map_mul,mul_pow,←map_pow,←map_pow,ha,hb]
    simp only [map_add,map_sub,map_mul,Polynomial.toLaurent_C,
      Polynomial.toLaurent_X,map_pow,map_one,T_pow,mul_one,leftEndpointI,rightEndpointI]
  have ht : (T (-(p : ℤ)) : (integralRationals p)[T;T⁻¹])*T (p : ℤ)=1 := by
    rw [←T_add]
    simp
  have hend : T (-(p : ℤ))*leftEndpointI p*rightEndpointI p=
      LaurentPolynomial.C ((4 : integralRationals p)^p)^2+1-
        LaurentPolynomial.C ((4 : integralRationals p)^p)*(T (p : ℤ)+T (-(p : ℤ))) := by
    rw [leftEndpointI,rightEndpointI]
    linear_combination
      (LaurentPolynomial.C ((4 : integralRationals p)^p)^2+1-
        LaurentPolynomial.C ((4 : integralRationals p)^p)*T (p : ℤ))*ht
  have he : T (-(p : ℤ))*leftEndpointI p*rightEndpointI p=
      normPhase p+LaurentPolynomial.C (p : integralRationals p)*endpointCarryI p := by
    rw [hend,fourCarryI_source p hp]
    simp only [map_add,map_mul,map_ofNat,normPhase,endpointCarryI]
    simp only [map_pow]
    ring
  rw [hprod,productCarryI]
  linear_combination he

noncomputable def normCarryI (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[T;T⁻¹] :=
  -LaurentPolynomial.C (inverseFiveCarryI p)*normPhase p-
    LaurentPolynomial.C ((inverseFiveUnitI p)^2)*productCarryI p

/-- Exact integral numerator equality precedes the actual rational p-division. -/
theorem normCarryI_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    normPhase p-LaurentPolynomial.C ((inverseFiveUnitI p)^2)*
      T (-(p : ℤ))*(normAbarI p).toLaurent^p=
        LaurentPolynomial.C (p : integralRationals p)*normCarryI p := by
  have hf := congrArg (fun z : integralRationals p =>
    (LaurentPolynomial.C z : (integralRationals p)[T;T⁻¹]))
    (inverseFiveCarryI_source p hp)
  simp only [map_add,map_one,map_mul] at hf
  rw [mul_assoc,productCarryI_source p hp,normCarryI]
  linear_combination -normPhase p*hf

noncomputable def normEntropyField (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  (T (-(p : ℤ))-4)*
    ((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (Polynomial.C (1/4)*X)).toLaurent+
  (T (-(p : ℤ))-LaurentPolynomial.C (1/4))*
    ((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (4*X)).toLaurent

theorem productCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p) (productCarryI p)=
      LaurentPolynomial.C (64*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p))-
      LaurentPolynomial.C (8*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p))*
        (T (p : ℤ)+T (-(p : ℤ)))+4*normEntropyField p := by
  obtain ⟨hl,hr⟩ := factor_rows_field p hp
  have hfour : residueHom p (fourCarryI p)=
      8*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
    simp only [fourCarryI,quotientI,map_add,map_mul,map_ofNat,map_natCast,
      map_pow,map_intCast,ZMod.natCast_self,mul_zero,zero_mul,add_zero]
  have hzeroL : (p : (ZMod p)[T;T⁻¹])=0 := by
    change LaurentPolynomial.C (p : ZMod p)=0
    rw [ZMod.natCast_self,map_zero]
  have hpowerL : (4 : (ZMod p)[T;T⁻¹])^p=4 := by
    have hh := congrArg (fun z : ZMod p => LaurentPolynomial.C z) (ZMod.pow_card (4 : ZMod p))
    simpa only [map_pow,map_ofNat] using hh
  have ht : (T (-(p : ℤ)) : (ZMod p)[T;T⁻¹])*T (p : ℤ)=1 := by
    rw [←T_add]
    simp
  rw [productCarryI]
  simp only [map_add,map_mul,WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_C,WPActualChiSource.coefficientMap_toLaurent,
    hl,hr,map_natCast,
    leftEndpointI,rightEndpointI,endpointCarryI,map_sub,map_one,hfour,
    map_ofNat,map_pow,WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_C]
  simp only [map_neg,map_ofNat,hzeroL,zero_mul,add_zero,hpowerL]
  rw [normEntropyField]
  have h4 : (4 : ZMod p)*(1/4 : ZMod p)=1 := by
    exact mul_one_div_cancel
      (WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega))
  have h4L := congrArg (fun z : ZMod p => LaurentPolynomial.C z) h4
  simp only [map_mul,map_one,map_ofNat] at h4L
  linear_combination
    (-16*((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (Polynomial.C (1/4)*X)).toLaurent-
      ((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (4*X)).toLaurent)*ht+
    ((WPFiniteAffineLog.LP p : (ZMod p)[X]).comp (4*X)).toLaurent*h4L

/-- The full norm carrier reduces to the prescribed DN without a substituted digit. -/
theorem normCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p) (normCarryI p)=
      LaurentPolynomial.C
        (-64*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)+
          34*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))+
      LaurentPolynomial.C
        (8*((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)))*
        (T (p : ℤ)+T (-(p : ℤ)))-4*normEntropyField p := by
  obtain ⟨hu,hc⟩ := inverseFiveCarryI_field p hp
  rw [normCarryI]
  simp only [map_sub,map_neg,map_mul,WPActualChiSource.coefficientMap_C,
    map_pow,hu,hc,one_pow,map_one,one_mul,
    productCarryI_field p hp,normPhase,map_ofNat,WPActualChiSource.coefficientMap_T]
  simp only [map_add,map_mul,map_ofNat,map_neg]
  ring

/-- The carrier is the literal rational quotient of the complete scaled norm. -/
theorem normCarryI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype (normCarryI p)=
      LaurentPolynomial.C (1/(p : ℚ))*
        (17-4*T (p : ℤ)-4*T (-(p : ℤ))-
          LaurentPolynomial.C ((1/5 : ℚ)^(2*(p-1)))*T (-(p : ℤ))*
            (WPFiniteZSource.Abar : ℚ[X]).toLaurent^p) := by
  have h := congrArg (WPActualChiSource.coefficientMap (integralRationals p).subtype)
    (normCarryI_source p hp)
  have hi : (integralRationals p).subtype ((inverseFiveUnitI p)^2)=
      (1/5 : ℚ)^(2*(p-1)) := by
    simp only [inverseFiveUnitI,map_pow,Subring.subtype_apply,
      smallIntegralInverse_value p 5 (by omega) (by omega),←pow_mul]
    congr 1
    omega
  have hA : (normAbarI p).map (integralRationals p).subtype=
      (WPFiniteZSource.Abar : ℚ[X]) := by
    simp only [normAbarI,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_ofNat,
      Polynomial.map_X,Polynomial.map_one,WPFiniteZSource.Abar]
  rw [map_sub,map_mul,map_mul,WPActualChiSource.coefficientMap_C,hi] at h
  simp only [map_sub,map_mul,map_pow,
    WPActualChiSource.coefficientMap_T,WPActualChiSource.coefficientMap_toLaurent,
    hA,map_natCast,normPhase,map_ofNat] at h
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : LaurentPolynomial.C (1/(p : ℚ))*(p : ℚ[T;T⁻¹])=1 := by
    change LaurentPolynomial.C (1/(p : ℚ))*LaurentPolynomial.C (p : ℚ)=1
    rw [←map_mul,one_div_mul_cancel hpq,map_one]
  have hs := congrArg (fun F : ℚ[T;T⁻¹] => LaurentPolynomial.C (1/(p : ℚ))*F) h
  rw [←mul_assoc,hu,one_mul] at hs
  simpa only [map_pow] using hs.symm

end WPFieldAssembly.ActualSigmaNormCarrySource
