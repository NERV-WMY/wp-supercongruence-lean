import WPFieldAssembly.SourceClosureHFNativeTransport
import WPFieldAssembly.NativeJointSuccessorWneedCore

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries WPFiniteLaurentDifferential

namespace WPFieldAssembly.BalancedVbalSuccessorWneedBridge

open ActualBpairContraction ActualBpairLowHLocalPole ActualGreenResidue
  ActualSimplePoleResidue NativeJointSuccessorJSeries NativeJointSuccessorCBMixed
  NativeJointSuccessorWneedCore SourceClosureHFNativeTransport

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

private theorem actual_Abar_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent≠0 := by
  intro hz
  apply WPFiniteZSource.Abar_nonzero (K:=K) p hp
  ext j
  simpa [localFiniteSeries_coeff] using
    congrArg (fun Q : LaurentSeries K => Q.coeff j) hz

private theorem actual_even_period_row (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
        LaurentPolynomial.C (WPFiniteNC122.q p : K)=
      invert (actualAK p : K[X]).toLaurent-
        LaurentPolynomial.C (WPFiniteNC122.q p-WPFiniteNC122.h p : K) := by
  have hh : hK (K:=K) p=(WPFiniteNC122.h p : K) := by
    unfold hK
    rw [actual_harmonic_is_finite_h p hp]
    simp only [WPFiniteNC122.h,WPFiniteNC122.q,map_intCast,map_sub,map_mul,
      map_neg,map_ofNat,map_div₀]
  rw [(actual_LV_native_pair (K:=K) p hp).2,hh,map_sub]
  ring

private theorem series_scalar_coefficient (c : K) (Q : LaurentSeries K) :
    (algebraMap K (LaurentSeries K) c*Q).coeff (-1)=c*Q.coeff (-1) := by
  rw [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
    HahnSeries.coeff_single_mul,sub_zero]

private theorem Euler_adjoint_algebra {F : Type*} [Field F]
    (a h d l f dh dd : F) (ha : a≠0) (he : a*dh=(f-1)*l) :
    (d*l-a*h*dd)/a=(f*d*l)/a-(dh*d+h*dd) := by
  field_simp [ha]
  linear_combination d*he

private theorem original_delta_period_algebra {F : Type*} [Field F]
    (a f c b e s t j : F) (ha : a≠0)
    (h3 : (3 : F)≠0) (h5 : (5 : F)≠0) (h9 : (9 : F)≠0) :
    (f*((2/5)*s*j+(2/3)*t*e)*(-3*b)+
        c*(-(2/3)*j-(10/9)*e)*(-3*b))/a=
      (2/3)*(((3/5)*f*s-c)*j*(-3*b/a))+
        ((-3*b)*(f*((2/3)*t*e)+c*((-10/9)*e)))/a := by
  field_simp [ha,h3,h5,h9]
  ring

private theorem full_HF_power_cancel {F : Type*} [Field F]
    (a h w : F) (p : ℕ) (ha : a≠0) :
    (a^p*h*w)/a^(p+1)=(h*w)/a := by
  rw [pow_succ]
  field_simp [ha,pow_ne_zero p ha]

/-- The entire original delta series, including every pole and invisible phase,
is integrated against the same original H before its residue is selected. -/
theorem actual_H_delta_full_derivative_residue_zero (p : ℕ) [Fact p.Prime]
    [CharP K p] :
    (LaurentSeries.derivative K
      (localFiniteSeriesHom (HpullK (K:=K) p).toLaurent*
        actualDeltaSeries p)).coeff (-1)=0 :=
  lowH_series_derivative_residue _

/-- The actual Euler identity moves the full differentiated delta into f*delta. -/
theorem actual_delta_Euler_series_adjoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    ((actualDeltaSeries p*localFiniteSeriesHom (33-12*T 1)-
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent*
          localFiniteSeriesHom (HpullK (K:=K) p).toLaurent*
            LaurentSeries.derivative K (actualDeltaSeries p))/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1)=
    ((localFiniteSeriesHom (ActualThreePhase.fK (K:=K) p hp).toLaurent*
        actualDeltaSeries p*localFiniteSeriesHom (33-12*T 1))/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1) := by
  let A := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  let H := localFiniteSeriesHom (HpullK (K:=K) p).toLaurent
  let d := (actualDeltaSeries p : LaurentSeries K)
  let L := localFiniteSeriesHom (33-12*T 1 : K[T;T⁻¹])
  let f := localFiniteSeriesHom (ActualThreePhase.fK (K:=K) p hp).toLaurent
  have he : A*localFiniteSeriesHom (D (HpullK (K:=K) p).toLaurent)=
      (f-1)*L := by
    simpa only [A,f,L,map_mul,map_sub,map_one] using
      congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
        (actual_two_Euler_sources (K:=K) p hp).1
  have hi := finite_series_derivative_product (HpullK (K:=K) p).toLaurent d
  have hr := congrArg (fun Q : LaurentSeries K => Q.coeff (-1)) hi
  rw [lowH_series_derivative_residue,HahnSeries.coeff_add] at hr
  have ha : A≠0 := actual_Abar_series_ne_zero (K:=K) p hp
  have hs : (d*L-A*H*LaurentSeries.derivative K d)/A=
      (f*d*L)/A-
        (localFiniteSeriesHom (D (HpullK (K:=K) p).toLaurent)*d+
          H*LaurentSeries.derivative K d) := by
    exact Euler_adjoint_algebra A H d L f
      (localFiniteSeriesHom (D (HpullK (K:=K) p).toLaurent))
      (LaurentSeries.derivative K d) ha he
  change ((d*L-A*H*LaurentSeries.derivative K d)/A).coeff (-1)=
    ((f*d*L)/A).coeff (-1)
  rw [hs,HahnSeries.coeff_sub,HahnSeries.coeff_add]
  dsimp only [H] at *
  linear_combination hr

/-- The corrected literal native core has exactly the ORIGINAL Jcoupled row
and both IR63b period rows, with no assigned residue or source premise. -/
theorem actual_Wneed_core_original_J_period_rows (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) :
    ((actualWneedCoreSeries p : LaurentSeries K)/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1)=
      (2/3 : K)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : K)*
                (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
              (ActualThreePhase.CBK (K:=K) p).toLaurent)*
            actualJSeries p*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1))+
      originPole
        ((33-12*T 1)*
          ((ActualThreePhase.fK (K:=K) p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : K)))+
            (ActualThreePhase.CBK (K:=K) p).toLaurent*
              (LaurentPolynomial.C (-10/9 : K)*
                (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : K))))) := by
  let A := localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent
  let f := (ActualThreePhase.fK (K:=K) p hp).toLaurent
  let CB := (ActualThreePhase.CBK (K:=K) p).toLaurent
  let L := (33-12*T 1 : K[T;T⁻¹])
  let B := (4*T 1-11 : K[T;T⁻¹])
  let E := invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
    LaurentPolynomial.C (WPFiniteNC122.q p : K)
  let P := L*(f*(LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*E)+
    CB*(LaurentPolynomial.C (-10/9 : K)*E))
  let fS := localFiniteSeriesHom f
  let cS := localFiniteSeriesHom CB
  let lS := localFiniteSeriesHom L
  let bS := localFiniteSeriesHom B
  let eS := localFiniteSeriesHom E
  let sS := localFiniteSeriesHom (Dsym p : K[T;T⁻¹])
  let tS := localFiniteSeriesHom (Dstar p : K[X]).toLaurent
  let jS := (actualJSeries p : LaurentSeries K)
  have ha : A≠0 := actual_Abar_series_ne_zero (K:=K) p hp
  have h3 : (3 : LaurentSeries K)≠0 := by
    change HahnSeries.C (3 : K)≠0
    exact HahnSeries.C_ne_zero (WPFiniteField.denominator_ne_zero p 3
      (Finset.mem_Ico.mpr (by omega)))
  have h5 : (5 : LaurentSeries K)≠0 := by
    change HahnSeries.C (5 : K)≠0
    exact HahnSeries.C_ne_zero (WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega)))
  have h9 : (9 : LaurentSeries K)≠0 := by
    rw [show (9 : LaurentSeries K)=3^2 by ring]
    exact pow_ne_zero _ h3
  have hl : lS=-3*bS := by
    dsimp only [lS,bS,L,B]
    simp only [map_sub,map_mul,map_ofNat]
    ring
  have hd : (actualDeltaSeries p : LaurentSeries K)=
      (2/5)*sS*jS+(2/3)*tS*eS := by
    simp only [actualDeltaSeries,sS,jS,tS,eS,E,
      ←actual_even_period_row (K:=K) p hp]
  have hdB : (actualDeltaBSeries p : LaurentSeries K)=
      -(2/3)*jS-(10/9)*eS := by
    simp only [actualDeltaBSeries,jS,eS,E,
      ←actual_even_period_row (K:=K) p hp]
  have hcoupled :
      localFiniteSeriesHom (LaurentPolynomial.C (3/5 : K)*f*Dsym p-CB)=
        (3/5 : LaurentSeries K)*fS*sS-cS := by
    dsimp only [fS,sS,cS]
    simp only [map_sub,map_mul,localFiniteSeries_C,map_div₀,map_ofNat]
  have hperiod : localFiniteSeriesHom P=
      lS*(fS*((2/3 : LaurentSeries K)*tS*eS)+cS*((-10/9)*eS)) := by
    dsimp only [P,lS,fS,tS,eS,cS]
    simp only [map_mul,map_add,localFiniteSeries_C,map_div₀,map_neg,map_ofNat]
  have hs : (localFiniteSeriesHom f*actualDeltaSeries p*localFiniteSeriesHom L+
      localFiniteSeriesHom CB*actualDeltaBSeries p*localFiniteSeriesHom L)/A=
      (2/3 : LaurentSeries K)*
        (localFiniteSeriesHom (LaurentPolynomial.C (3/5 : K)*f*Dsym p-CB)*
          actualJSeries p*(-3*localFiniteSeriesHom B/A))+
        localFiniteSeriesHom P/A := by
    rw [hd,hdB,hcoupled,hperiod]
    change (fS*((2/5)*sS*jS+(2/3)*tS*eS)*lS+
        cS*(-(2/3)*jS-(10/9)*eS)*lS)/A=
      (2/3)*(((3/5)*fS*sS-cS)*jS*(-3*bS/A))+
        (lS*(fS*((2/3)*tS*eS)+cS*((-10/9)*eS)))/A
    rw [hl]
    exact original_delta_period_algebra A fS cS bS eS sS tS jS ha h3 h5 h9
  have hr := congrArg (fun Q : LaurentSeries K => Q.coeff (-1)) hs
  have hc : (2/3 : LaurentSeries K)=algebraMap K (LaurentSeries K) (2/3 : K) := by
    simp only [map_div₀,map_ofNat]
  rw [HahnSeries.coeff_add,hc,series_scalar_coefficient] at hr
  have hj := actual_delta_Euler_series_adjoint (K:=K) p hp
  have hcore : ((actualWneedCoreSeries p : LaurentSeries K)/A).coeff (-1)=
      ((localFiniteSeriesHom f*actualDeltaSeries p*localFiniteSeriesHom L+
          localFiniteSeriesHom CB*actualDeltaBSeries p*localFiniteSeriesHom L)/A).coeff (-1) := by
    unfold actualWneedCoreSeries
    rw [add_div,HahnSeries.coeff_add,add_div,HahnSeries.coeff_add]
    dsimp only [A,f,CB,L]
    linear_combination hj
  change ((actualWneedCoreSeries p : LaurentSeries K)/A).coeff (-1)=
    (2/3 : K)*(localFiniteSeriesHom (LaurentPolynomial.C (3/5 : K)*f*Dsym p-CB)*
      actualJSeries p*(-3*localFiniteSeriesHom B/A)).coeff (-1)+originPole P
  rw [hcore,hr]
  congr 1
  exact local_Abar_quotient_residue (K:=K) p hp P

/-- The whole original HF numerator cancels exactly its p-fold denominator.
The complete logarithmic and Frobenius bracket remains in the simple-pole residue. -/
theorem actual_HF_full_successor_series_origin (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (localFiniteSeriesHom (nativeHFOriginNumerator (K:=K) p hp)/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^(p+1)).coeff (-1)=
      originPole
        ((HpullK (K:=K) p).toLaurent*
          (nativeHFSigmaNumerator p+
            WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
              (4*T (-(p : ℤ))-11)*nativeHFBracket p u)) := by
  have hf := congrArg (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K)
    (actual_HF_native_Laurent_source (K:=K) p hp u hu)
  simp only [map_mul,map_pow] at hf
  have ha := actual_Abar_series_ne_zero (K:=K) p hp
  rw [hf,full_HF_power_cancel _ _ _ p ha,←map_mul]
  exact local_Abar_quotient_residue (K:=K) p hp _

/-- The literal original HF-origin, both period rows and ORIGINAL Jcoupled
equal the residue of the existing native core plus its entire weighted HF.
No new scalar or series is defined, and neither native source is evaluated away. -/
theorem actual_original_HF_period_J_Wneed_series_bridge (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (localFiniteSeriesHom (nativeHFOriginNumerator (K:=K) p hp)/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^(p+1)).coeff (-1)+
      originPole
        ((33-12*T 1)*
          ((ActualThreePhase.fK (K:=K) p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : K)))+
            (ActualThreePhase.CBK (K:=K) p).toLaurent*
              (LaurentPolynomial.C (-10/9 : K)*
                (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : K)))))+
      (2/3 : K)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : K)*
                (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
              (ActualThreePhase.CBK (K:=K) p).toLaurent)*
            actualJSeries p*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1))=
      ((actualWneedCoreSeries p+
          localFiniteSeriesHom (HpullK (K:=K) p).toLaurent*
            localFiniteSeriesHom
              (nativeHFSigmaNumerator p+
                WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                  (4*T (-(p : ℤ))-11)*nativeHFBracket p u))/
        localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent).coeff (-1) := by
  rw [add_div,HahnSeries.coeff_add,←map_mul,local_Abar_quotient_residue p hp]
  rw [actual_Wneed_core_original_J_period_rows p hp,
    actual_HF_full_successor_series_origin p hp u hu]
  ring

/-- The same entire native Wneed has its literal finite Laurent residue.
The existing core carrier and the complete weighted HF are retained together. -/
theorem actual_original_HF_period_J_Wneed_Laurent_bridge (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    (localFiniteSeriesHom (nativeHFOriginNumerator (K:=K) p hp)/
      localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent^(p+1)).coeff (-1)+
      originPole
        ((33-12*T 1)*
          ((ActualThreePhase.fK (K:=K) p hp).toLaurent*
            (LaurentPolynomial.C (2/3 : K)*(Dstar p : K[X]).toLaurent*
              (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                LaurentPolynomial.C (WPFiniteNC122.q p : K)))+
            (ActualThreePhase.CBK (K:=K) p).toLaurent*
              (LaurentPolynomial.C (-10/9 : K)*
                (invert (WPFiniteLVSource.LV p : K[X]).toLaurent-
                  LaurentPolynomial.C (WPFiniteNC122.q p : K)))))+
      (2/3 : K)*
        ((localFiniteSeriesHom
            (LaurentPolynomial.C (3/5 : K)*
                (ActualThreePhase.fK (K:=K) p hp).toLaurent*Dsym p-
              (ActualThreePhase.CBK (K:=K) p).toLaurent)*
            actualJSeries p*
            (-3*localFiniteSeriesHom (4*T 1-11)/
              localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent)).coeff (-1))=
      originPole
        (actualWneedCoreCarrier p+
          (HpullK (K:=K) p).toLaurent*
            (nativeHFSigmaNumerator p+
              WPFiniteWSource.squaredCoordinate.toLaurent^((p-1)/2)*
                (4*T (-(p : ℤ))-11)*nativeHFBracket p u)) := by
  have h := actual_original_HF_period_J_Wneed_series_bridge (K:=K) p hp u hu
  rw [actual_Wneed_core_Laurent p hp,←map_mul,←map_add,
    local_Abar_quotient_residue p hp] at h
  exact h

/- BalancedVbalSuccessorOriginSeriesTransport supplies the original originTrace
map into this same complete p+1 local-series quotient. Its consumer retains the
whole native core and weighted HF, subject to their affected ancestry checks. -/

end WPFieldAssembly.BalancedVbalSuccessorWneedBridge
