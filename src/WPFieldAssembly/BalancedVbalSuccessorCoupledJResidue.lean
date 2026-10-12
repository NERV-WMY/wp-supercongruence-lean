import WPFieldAssembly.BalancedVbalSuccessorCoupledSourceResidue
import WPFieldAssembly.NativeJointSuccessorJSeries

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPActualChiSource WPFiniteKSource
  WPFiniteCubicLog WPFiniteLVSource WPFiniteJHighCoefficient WPActualNativeJacobiJet
  WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualGaussBottom WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.BalancedVbalSuccessorCoupledJResidue

open BalancedVbalSuccessorCoupledSource BalancedVbalSuccessorCoupledSourceResidue
  NativeClosureMixedSource NativeJointSuccessorJSeries ActualBpairLowHLocalPole
  SourceClosureBalancedNativeParticular

variable (p : ℕ) [Fact p.Prime]
set_option maxHeartbeats 2400000

/-- Reindexing retains every original odd coefficient, including exponent p-2. -/
theorem actual_OP_original_odd_cutoff (hp : 19≤p) :
    (OP p : (ZMod p)[X])=X*(oddReciprocalF p).comp (X^2) := by
  classical
  rw [ActualFiniteA2.OP_half_cutoff p hp,Finset.sum_Ico_eq_sum_range,
    oddReciprocalF,sum_comp,Finset.mul_sum]
  simp only [Nat.add_sub_cancel,mul_comp,C_comp,pow_comp,X_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 2*(1+i)-1=2*i+1 by omega,←pow_mul,pow_succ]
  ring

private theorem full_odd_conic (hp : 19≤p) :
    (actualOddProperPull p).comp conic=(actualOddProperProduct p).comp Tc := by
  have hY := NativeIR28.legendreField_reflect p (p/6) (by omega : 7≤p)
  change (actualLegendreJacobi p).comp (-X)=
    Polynomial.C ((-1 : ZMod p)^(p/6))*actualLegendreJacobi p at hY
  have hn := NativeIR28.actual_proper_legendre_reflect p hp
  have hi : (-X : (ZMod p)[X]).comp (-X)=X := by simp
  have hO : (OP p : (ZMod p)[X]).comp (-X)= -OP p := by
    simp only [OP,mul_comp,C_comp,sub_comp,comp_assoc,hi,comp_X]
    ring
  have hs : (Polynomial.C ((-1 : ZMod p)^(p/6)) : (ZMod p)[X])^2=1 := by
    rw [←Polynomial.C_pow,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have heven : (actualOddProperProduct p).comp (-X)=actualOddProperProduct p := by
    unfold actualOddProperProduct
    rw [mul_comp,mul_comp,hY,hn,hO]
    linear_combination (actualLegendreJacobi p*properLegendreJacobi p*OP p)*hs
  have he := even_native_attachment p hp (actualOddProperProduct p) heven
  rw [actualOddProperPull,comp_assoc,actual_native_V_conic p hp,
    show (1-Tc^2 : (ZMod p)[X])=(1-X^2 : (ZMod p)[X]).comp Tc by
      simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,he]

/-- The whole odd product is descended before a branch denominator is inverted. -/
theorem actual_odd_proper_polynomial_product (hp : 19≤p) :
    (WPFiniteWSource.squaredCoordinate : (ZMod p)[X])^((p-1)/2)*actualOddProperPull p=
      ActualFirstGreen.CB p*(4*X-11)*(oddReciprocalF p).comp V := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hc5 : Polynomial.C (1/5 : ZMod p)*(5 : (ZMod p)[X])=1 := by
    change Polynomial.C (1/5 : ZMod p)*Polynomial.C (5 : ZMod p)=Polynomial.C 1
    rw [←Polynomial.C_mul,one_div_mul_cancel h5]
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hN : 2*((p-1)/2)+1=p := by obtain ⟨k,hk⟩ := hpodd; omega
  have hTc : (Tc : (ZMod p)[X])=X*(4*X^2-3) := by
    dsimp only [Tc]
    ring
  have hpow : ((X^2)^((p-1)/2)*Tc : (ZMod p)[X])=X^p*(4*X^2-3) := by
    rw [hTc,←pow_mul]
    rw [show 2*((p-1)/2)=p-1 by omega,←mul_assoc,←pow_succ,
      Nat.sub_add_cancel (by omega : 1≤p)]
  have hB : (4*X-11 : (ZMod p)[X]).comp conic=5*(4*X^2-3) := by
    simp only [conic,mul_comp,sub_comp,ofNat_comp,X_comp]
    ring
  apply conic_comp_injective p hp
  rw [mul_comp,pow_comp,WPFiniteWSource.squaredCoordinate_conic p hp,
    full_odd_conic p hp,mul_comp,mul_comp,
    (ActualFirstGreen.actual_carrier_pullbacks p hp).1,hB,comp_assoc,V_conic p hp]
  simp only [actualOddProperProduct,ActualFirstGreen.CBt,ActualFirstGreen.B,mul_comp]
  rw [actual_OP_original_odd_cutoff p hp,mul_comp,X_comp,comp_assoc,pow_comp,X_comp]
  calc
    _ = ((X^2)^((p-1)/2)*Tc)*(actualLegendreJacobi p).comp Tc*
        (properLegendreJacobi p).comp Tc*(oddReciprocalF p).comp (Tc^2) := by ring
    _ = X^p*(4*X^2-3)*(actualLegendreJacobi p).comp Tc*
        (properLegendreJacobi p).comp Tc*(oddReciprocalF p).comp (Tc^2) := by rw [hpow]
    _ = _ := by
      linear_combination -X^p*(4*X^2-3)*(actualLegendreJacobi p).comp Tc*
        (properLegendreJacobi p).comp Tc*(oddReciprocalF p).comp (Tc^2)*hc5

private theorem original_V_inverse :
    invert (V : (ZMod p)[X]).toLaurent=(oddReciprocalW : (ZMod p)[T;T⁻¹]) := by
  have ht : (T (-1)*T 1 : (ZMod p)[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have hb : invert (4*X-11 : (ZMod p)[X]).toLaurent=T (-1)*(4-11*T 1) := by
    simp only [map_sub,map_mul,map_ofNat,Polynomial.toLaurent_X,invert_T]
    linear_combination 11*ht
  have ht3 : (T (-1)*T (-1)^2 : (ZMod p)[T;T⁻¹])=T (-3) := by
    rw [T_pow,←T_add]
    norm_num
  have hc : LaurentPolynomial.C (((5 : ZMod p)^2)⁻¹)=
      (LaurentPolynomial.C ((5 : ZMod p)⁻¹) : (ZMod p)[T;T⁻¹])^2 := by
    rw [←map_pow,inv_pow]
  simp only [V,map_mul,map_pow,Polynomial.toLaurent_C,
    WPFiniteZSource.invert_squaredCoordinate,invert_C,hb,mul_pow,
    oddReciprocalW,hc]
  linear_combination LaurentPolynomial.C ((5 : ZMod p)⁻¹)^2*
    WPFiniteWSource.squaredCoordinate.toLaurent*(4-11*T 1)^2*ht3

/-- The entire odd source has exactly the finite reciprocal kernel's signed shift. -/
theorem actual_odd_proper_reflected_product (hp : 19≤p) :
    (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent^((p-1)/2)*
        (T (((p-1)/2 : ℕ) : ℤ)*invert (actualOddProperPull p).toLaurent)=
      actualBv p*oddReciprocalS p := by
  let N := (p-1)/2
  have hN : 1≤N := by dsimp only [N]; omega
  have he := congrArg (fun Q : (ZMod p)[X] => invert Q.toLaurent)
    (actual_odd_proper_polynomial_product p hp)
  simp only [map_mul] at he
  rw [←substituteOver_toLaurent (oddReciprocalF p : (ZMod p)[X])
    (V : (ZMod p)[X])] at he
  simp only [map_pow,WPFiniteZSource.invert_squaredCoordinate,mul_pow,T_pow,
    mul_neg_one,substituteOver_invert,original_V_inverse p] at he
  have ht : (T (-1)*T 1 : (ZMod p)[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  have hb : invert (4*X-11 : (ZMod p)[X]).toLaurent=T (-1)*(4-11*T 1) := by
    simp only [map_sub,map_mul,map_ofNat,Polynomial.toLaurent_X,invert_T]
    linear_combination 11*ht
  rw [hb] at he
  have htN : (T (2*(N : ℤ))*T (-(N : ℤ)) : (ZMod p)[T;T⁻¹])=T (N : ℤ) := by
    rw [←T_add]
    congr 1
    omega
  have hphase : (T (2*(N : ℤ))*T (-1) : (ZMod p)[T;T⁻¹])=
      T (N : ℤ)*T ((N-1 : ℕ) : ℤ) := by
    rw [←T_add,←T_add]
    congr 1
    omega
  change T (-(N : ℤ))*WPFiniteWSource.squaredCoordinate.toLaurent^N*
      invert (actualOddProperPull p).toLaurent=
    invert (ActualFirstGreen.CB p).toLaurent*(T (-1)*(4-11*T 1))*
      substituteOver (oddReciprocalF p) oddReciprocalW at he
  change WPFiniteWSource.squaredCoordinate.toLaurent^N*
    (T (N : ℤ)*invert (actualOddProperPull p).toLaurent)=_
  calc
    _ = T (2*(N : ℤ))*(T (-(N : ℤ))*
        WPFiniteWSource.squaredCoordinate.toLaurent^N*
          invert (actualOddProperPull p).toLaurent) := by
      rw [show T (2*(N : ℤ))*(T (-(N : ℤ))*
          WPFiniteWSource.squaredCoordinate.toLaurent^N*
            invert (actualOddProperPull p).toLaurent)=
        (T (2*(N : ℤ))*T (-(N : ℤ)))*
          WPFiniteWSource.squaredCoordinate.toLaurent^N*
            invert (actualOddProperPull p).toLaurent by ring,htN]
      ring
    _ = T (2*(N : ℤ))*(invert (ActualFirstGreen.CB p).toLaurent*
        (T (-1)*(4-11*T 1))*substituteOver (oddReciprocalF p) oddReciprocalW) :=
      congrArg (fun Q : (ZMod p)[T;T⁻¹] => T (2*(N : ℤ))*Q) he
    _ = _ := by
      rw [actualBv,oddReciprocalS,oddReciprocalKernel_substitution]
      change _=T (N : ℤ)*invert (ActualFirstGreen.CB p).toLaurent*
        (T ((N-1 : ℕ) : ℤ)*((4-11*T 1)*
          substituteOver (oddReciprocalF p) oddReciprocalW))
      linear_combination invert (ActualFirstGreen.CB p).toLaurent*(4-11*T 1)*
        substituteOver (oddReciprocalF p) oddReciprocalW*hphase

/-- The original complete finite residual is the SAME full j product after clearing s^N. -/
theorem actual_full_j_original_residual (hp : 19≤p) :
    (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent^((p-1)/2)*
        actualFullJProduct p=
      actualBv p*mixedResidual p (actualAK p : (ZMod p)[X]).toLaurent
        (WPFiniteNC122.h p) := by
  have ha : actualAPull p=(actualAK p : (ZMod p)[X]) := by
    have hid : ActualThreePhase.φ (K:=ZMod p) p=RingHom.id (ZMod p) :=
      Subsingleton.elim _ _
    rw [actualAK,hid,Polynomial.map_id]
    rfl
  have ho := actual_odd_proper_reflected_product p hp
  rw [actual_full_j_literal p hp,ha,actual_harmonic_is_finite_h p hp,
    mixedResidual,mixedEvenSource,frobeniusPhi]
  linear_combination ho

private theorem original_s_series_nonzero (hp : 19≤p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent≠0 := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  intro hz
  have hs : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent=0 := by
    ext n
    simpa [localFiniteSeries_coeff] using
      congrArg (fun Q : LaurentSeries (ZMod p) => Q.coeff n) hz
  have hp0 : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X])=0 :=
    Polynomial.toLaurent_injective (hs.trans (map_zero _).symm)
  have hcoef := congrArg (fun P : (ZMod p)[X] => P.coeff 1) hp0
  have hval : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).coeff 1=(5 : ZMod p)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate,Polynomial.coeff_one]
  rw [hval,Polynomial.coeff_zero] at hcoef
  exact inv_ne_zero h5 hcoef

/-- Clearing the original s unit identifies j itself with the existing original series. -/
theorem actual_full_j_original_series (hp : 19≤p) :
    localFiniteSeriesHom (actualFullJProduct p)=
      localFiniteSeriesHom (actualBv p)*(actualJSeries p : LaurentSeries (ZMod p)) := by
  rw [actualJSeries,←mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ (original_s_series_nonzero p hp))).mpr
  have he := congrArg localFiniteSeriesHom (actual_full_j_original_residual p hp)
  simp only [map_mul,map_pow] at he
  linear_combination he

private theorem original_scalar_coefficient (c : ZMod p) (Q : LaurentSeries (ZMod p)) :
    (localFiniteSeriesHom (LaurentPolynomial.C c)*Q).coeff (-1)=c*Q.coeff (-1) := by
  rw [localFiniteSeries_C,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
    HahnSeries.coeff_single_mul,sub_zero]

/-- This is the original Jcoupled residue, printed inline with its full existing j-series.
The metric factor and dlog(V) are the original ones; no scalar is assigned. -/
theorem actual_original_Jcoupled_residue (hp : 19≤p) :
    (2/3 : ZMod p)*
      ((localFiniteSeriesHom
          (LaurentPolynomial.C (3/5 : ZMod p)*
              (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
            (ActualFirstGreen.CB p).toLaurent)*
          (actualJSeries p : LaurentSeries (ZMod p))*
          (-3*localFiniteSeriesHom (4*T 1-11)/
            localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      ActualSimplePoleResidue.originPole (actualJSubtractionCleared p) := by
  have hm : LaurentPolynomial.C (3/5 : ZMod p)*
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
        (ActualFirstGreen.CB p).toLaurent=actualBv p := by
    linear_combination actual_coupled_metric_source p hp
  rw [hm]
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hc : (LaurentPolynomial.C (2/3 : ZMod p)*(-3) : (ZMod p)[T;T⁻¹])= -2 := by
    have hs : (2/3 : ZMod p)*(-3)= -2 := by field_simp [h3]
    simpa only [map_mul,map_neg,map_ofNat] using
      congrArg (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) hs
  have hcs := congrArg localFiniteSeriesHom hc
  simp only [map_mul,map_neg,map_ofNat,div_eq_mul_inv] at hcs
  rw [←original_scalar_coefficient]
  have he : localFiniteSeriesHom (LaurentPolynomial.C (2/3 : ZMod p))*
      (localFiniteSeriesHom (actualBv p)*(actualJSeries p : LaurentSeries (ZMod p))*
        (-3*localFiniteSeriesHom (4*T 1-11)/
          localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent))=
      localFiniteSeriesHom (actualJSubtractionCleared p)/
        localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent := by
    rw [←actual_full_j_original_series p hp,actualJSubtractionCleared,
      map_mul,map_mul,map_neg,map_ofNat]
    simp only [div_eq_mul_inv,map_mul,map_ofNat] at hcs ⊢
    linear_combination localFiniteSeriesHom (4*T 1-11)*
      localFiniteSeriesHom (actualFullJProduct p)*
      (localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)⁻¹*hcs
  rw [he,local_Abar_quotient_residue p hp]

/-- The original reflected Sigma, proper QO and ORIGINAL Jcoupled give the actual Jjoint pole. -/
theorem actual_original_coupled_residue_identity (hp : 19≤p) :
    (2/3 : ZMod p)*LaurentPoleField.fieldTrace p (p+1)
        (SourceClosureSigmaNativeKernel.actualReflectedSigmaWeightedNumerator p hp)+
      (2/3 : ZMod p)*ActualDeltaUNextSource.QO p
        (SourceClosureCommonWholeSource.properSource p)-
      (2/3 : ZMod p)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : ZMod p)*
                (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p-
              (ActualFirstGreen.CB p).toLaurent)*
            (actualJSeries p : LaurentSeries (ZMod p))*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent)).coeff (-1))=
      ActualSimplePoleResidue.originPole (actualJjoint p hp) := by
  rw [actual_original_Jcoupled_residue p hp,actual_Jjoint_origin_three_carriers p hp]

end WPFieldAssembly.BalancedVbalSuccessorCoupledJResidue
