import WPFieldAssembly.ActualEntropyCubic

open scoped BigOperators
open WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualRationalPhaseCarry

set_option maxHeartbeats 1000000

noncomputable def quotientI (p : ℕ) [Fact p.Prime] (a : ℤ) : integralRationals p :=
  (WPFiniteInversion.integerFermatQuotient p a : integralRationals p)

noncomputable def inverseTwoUnitI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (smallIntegralInverse p 2)^(p-1)

noncomputable def kappaI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (smallIntegralInverse p 4)^p+4^p-(11*smallIntegralInverse p 4)^p

noncomputable def betaI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  (smallIntegralInverse p 4)^p+2*4^p

/-- The divided phases are built from the original integer quotients and rational inverse unit. -/
noncomputable def kappaCarryI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  8*quotientI p 2+4*(p : integralRationals p)*(quotientI p 2)^2+
    5*smallIntegralInverse p 2*quotientI p 2*inverseTwoUnitI p*(inverseTwoUnitI p+1)-
    11*smallIntegralInverse p 4*quotientI p 11*(inverseTwoUnitI p)^2

noncomputable def betaCarryI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  16*quotientI p 2+8*(p : integralRationals p)*(quotientI p 2)^2-
    smallIntegralInverse p 4*quotientI p 2*inverseTwoUnitI p*(inverseTwoUnitI p+1)

theorem twoUnit_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2 : integralRationals p)^(p-1)=1+(p : integralRationals p)*quotientI p 2 := by
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
  have h : (quotientI p 2)*(p : integralRationals p)=
      (2 : integralRationals p)^(p-1)-1 := by
    unfold quotientI
    exact_mod_cast hq
  linear_combination -h

theorem inverseTwoUnit_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    inverseTwoUnitI p=1-(p : integralRationals p)*quotientI p 2*inverseTwoUnitI p := by
  have hu : (2 : integralRationals p)^(p-1)*inverseTwoUnitI p=1 := by
    apply Subtype.ext
    change (integralRationals p).subtype
      ((2 : integralRationals p)^(p-1)*inverseTwoUnitI p)=1
    simp only [inverseTwoUnitI,map_mul,map_pow,map_ofNat,Subring.subtype_apply,
      smallIntegralInverse_value p 2 (by omega) (by omega),←mul_pow]
    norm_num
  rw [twoUnit_source p hp] at hu
  linear_combination hu

theorem rational_phase_values (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (kappaI p).val=(1/4 : ℚ)^p+4^p-(11/4 : ℚ)^p ∧
    (betaI p).val=(1/4 : ℚ)^p+2*4^p := by
  change (integralRationals p).subtype (kappaI p)=_ ∧
    (integralRationals p).subtype (betaI p)=_
  simp only [kappaI,betaI,map_add,map_sub,map_mul,map_pow,map_ofNat,Subring.subtype_apply,
    smallIntegralInverse_value p 4 (by omega) (by omega)]
  norm_num

theorem phase_end_power_sources (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (smallIntegralInverse p 4)^p=
      smallIntegralInverse p 4*(inverseTwoUnitI p)^2 ∧
    (4 : integralRationals p)^p=4*((2 : integralRationals p)^(p-1))^2 ∧
    (11*smallIntegralInverse p 4)^p=
      11*smallIntegralInverse p 4*
        (1+(p : integralRationals p)*quotientI p 11)*(inverseTwoUnitI p)^2 := by
  have h4 : smallIntegralInverse p 4=(smallIntegralInverse p 2)^2 := by
    apply Subtype.ext
    rw [Subring.coe_pow,smallIntegralInverse_value p 4 (by omega) (by omega),
      smallIntegralInverse_value p 2 (by omega) (by omega)]
    norm_num
  have h11 : (11 : integralRationals p)^(p-1)=
      1+(p : integralRationals p)*quotientI p 11 := by
    have hn : (11 : ZMod p)≠0 :=
      WPActualGaussProper.small_cast_ne_zero p 11 (by omega) (by omega)
    have hq := WPFiniteInversion.integerFermatQuotient_mul p 11 (by simpa using hn)
    have h : quotientI p 11*(p : integralRationals p)=
        (11 : integralRationals p)^(p-1)-1 := by
      unfold quotientI
      exact_mod_cast hq
    linear_combination -h
  have hpow (z : integralRationals p) : z^p=z*z^(p-1) := by
    calc
      z^p = z^((p-1)+1) := congrArg (fun n : ℕ => z^n) (by omega)
      _ = z*z^(p-1) := by rw [pow_succ]; ring
  have htwo : (4 : integralRationals p)=(2 : integralRationals p)^2 := by norm_num
  have ha : (smallIntegralInverse p 4)^p=
      smallIntegralInverse p 4*(inverseTwoUnitI p)^2 := by
    rw [hpow,h4,inverseTwoUnitI]
    congr 1
    rw [←pow_mul,←pow_mul,Nat.mul_comm 2 (p-1)]
  have hb : (4 : integralRationals p)^p=4*((2 : integralRationals p)^(p-1))^2 := by
    rw [hpow,htwo]
    congr 1
    rw [←pow_mul,←pow_mul,Nat.mul_comm 2 (p-1)]
  refine ⟨ha,hb,?_⟩
  rw [mul_pow,hpow (11 : integralRationals p),h11,ha]
  ring

theorem kappaI_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    kappaI p=3*smallIntegralInverse p 2+(p : integralRationals p)*kappaCarryI p := by
  obtain ⟨ha,hb,hc⟩ := phase_end_power_sources p hp
  have hi := inverseTwoUnit_source p hp
  apply Subtype.ext
  change (integralRationals p).subtype (kappaI p)=
    (integralRationals p).subtype
      (3*smallIntegralInverse p 2+(p : integralRationals p)*kappaCarryI p)
  simp only [kappaI,kappaCarryI,ha,hb,hc,twoUnit_source p hp,map_add,
    map_sub,map_mul,map_pow,map_natCast,map_ofNat,map_one,Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 4 (by omega) (by omega)]
  have hv := congrArg (fun z : integralRationals p => z.val) hi
  change (inverseTwoUnitI p).val=1-(p : ℚ)*(quotientI p 2).val*(inverseTwoUnitI p).val at hv
  linear_combination -(5/2 : ℚ)*((inverseTwoUnitI p).val+1)*hv

theorem betaI_firstTaylor (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    betaI p=33*smallIntegralInverse p 4+(p : integralRationals p)*betaCarryI p := by
  obtain ⟨ha,hb,_⟩ := phase_end_power_sources p hp
  have hi := inverseTwoUnit_source p hp
  apply Subtype.ext
  change (integralRationals p).subtype (betaI p)=
    (integralRationals p).subtype
      (33*smallIntegralInverse p 4+(p : integralRationals p)*betaCarryI p)
  simp only [betaI,betaCarryI,ha,hb,twoUnit_source p hp,map_add,
    map_sub,map_mul,map_pow,map_natCast,map_ofNat,map_one,Subring.subtype_apply,
    smallIntegralInverse_value p 4 (by omega) (by omega)]
  have hv := congrArg (fun z : integralRationals p => z.val) hi
  change (inverseTwoUnitI p).val=1-(p : ℚ)*(quotientI p 2).val*(inverseTwoUnitI p).val at hv
  linear_combination (1/4 : ℚ)*((inverseTwoUnitI p).val+1)*hv

theorem inverseTwoUnitI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (inverseTwoUnitI p)=1 := by
  rw [inverseTwoUnitI,map_pow,smallIntegralInverse_field p 2 (by omega) (by omega)]
  apply ZMod.pow_card_sub_one_eq_one
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  exact inv_ne_zero h2

theorem kappaCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (kappaCarryI p)=
      13*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (11/4 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 11 : ZMod p) := by
  simp only [kappaCarryI,quotientI,map_add,map_sub,map_mul,map_pow,map_natCast,
    map_intCast,map_ofNat,map_one,ZMod.natCast_self,inverseTwoUnitI_field p hp,
    smallIntegralInverse_field p 2 (by omega) (by omega),
    smallIntegralInverse_field p 4 (by omega) (by omega)]
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := by
    rw [show (4 : ZMod p)=2^2 by ring]
    exact pow_ne_zero _ h2
  field_simp [h2,h4]
  ring

theorem betaCarryI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (betaCarryI p)=
      (31/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  simp only [betaCarryI,quotientI,map_add,map_sub,map_mul,map_pow,map_natCast,
    map_intCast,map_ofNat,map_one,ZMod.natCast_self,inverseTwoUnitI_field p hp,
    smallIntegralInverse_field p 4 (by omega) (by omega)]
  have h2 : (2 : ZMod p)≠0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := by
    rw [show (4 : ZMod p)=2^2 by ring]
    exact pow_ne_zero _ h2
  field_simp [h2,h4]
  ring

end WPFieldAssembly.ActualRationalPhaseCarry
