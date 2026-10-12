import WPFieldAssembly.SourceClosureVbalProperSource
import WPFieldAssembly.SourceClosureSigmaNativeKernel
import WPFieldAssembly.ActualSB72Attachment
import WPFieldAssembly.ActualFiniteA2

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPFiniteKSource WPFiniteCubicLog WPFiniteLVSource WPActualRankTwoLegendreField
  WPFiniteJHighCoefficient WPActualNativeJacobiJet WPActualRankTwoProper
  WPActualGaussBottom WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.ActualBpairContraction WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.SourceClosureVbalProperSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureSigmaNativeKernel
  WPFieldAssembly.SourceClosureHFNativeTransport

namespace WPFieldAssembly.BalancedVbalSuccessorCoupledSource

set_option maxHeartbeats 2000000

variable (p : ℕ) [Fact p.Prime]

/-- The complete odd proper source, before either quadratic descent or reflection. -/
noncomputable def actualOddProperProduct : (ZMod p)[X] :=
  actualLegendreJacobi p*properLegendreJacobi p*OP p

noncomputable def actualOddProperPull : (ZMod p)[X] :=
  (quadraticInverse (actualOddProperProduct p)).comp (WPHasseIntegralTransport.fieldV p)

noncomputable def actualProperPull : (ZMod p)[X] :=
  (quadraticInverse (originalProperProduct p)).comp (WPHasseIntegralTransport.fieldV p)

noncomputable def actualEvenPull : (ZMod p)[X] :=
  (evenSquared p).comp V

noncomputable def actualAPull : (ZMod p)[X] :=
  (actualLogMinusH p).comp (WPHasseIntegralTransport.fieldV p)

noncomputable def actualBv : (ZMod p)[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ)*invert (ActualFirstGreen.CB p).toLaurent

/-- The whole product Bv*j. The odd quotient is kept multiplied by Bv;
this requires no inversion of s=(x+1)/5 or of the actual proper factor. -/
noncomputable def actualFullJProduct : (ZMod p)[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ)*invert (actualOddProperPull p).toLaurent+
    (4*T (-(p : ℤ))-11)*actualBv p*
      (invert (actualEvenPull p).toLaurent+
        LaurentPolynomial.C (1/3 : ZMod p)*(actualAPull p).toLaurent)

/-- The original (2/3) Bv*j*dlog(V), after dlog(V)=-3B dx/Abar. -/
noncomputable def actualJSubtractionCleared : (ZMod p)[T;T⁻¹] :=
  -2*(4*T 1-11)*actualFullJProduct p

/-- The same three original sources: reflected Sigma, proper QO and full j subtraction. -/
noncomputable def actualJjoint (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  nativeKSigma p*(4*T 1-11)*(actualSigmaPullback p hp).toLaurent+
    LaurentPolynomial.C (2/3 : ZMod p)*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
      SourceClosureCommonWholeSource.properOriginDensity p-
    actualJSubtractionCleared p

/-- Both full finite log halves and the last odd pivot remain in the actual odd source. -/
theorem actual_odd_proper_full_cutoff (hp : 19≤p) :
    actualOddProperProduct p=actualLegendreJacobi p*properLegendreJacobi p*
      ∑ j ∈ Finset.Ico 1 ((p-1)/2+1),
        Polynomial.C (((2*j-1 : ℕ) : ZMod p)⁻¹)*X^(2*j-1) := by
  rw [actualOddProperProduct,ActualFiniteA2.OP_half_cutoff p hp]

private theorem actual_odd_pivot_band (hp : 19≤p) (j : ℕ)
    (hj : j ∈ Finset.Ico 1 ((p-1)/2+1)) :
    1≤2*j-1 ∧ 2*j-1≤p-2 ∧ (((2*j-1 : ℕ) : ZMod p)≠0) := by
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := ho
  have hhalf : 2*((p-1)/2)+1=p := by omega
  obtain ⟨hj1,hjN⟩ := Finset.mem_Ico.mp hj
  have hlo : 0<2*j-1 := by omega
  have hhi : 2*j-1<p := by omega
  exact ⟨by omega,by omega,
    WPActualGaussProper.small_cast_ne_zero p (2*j-1) hlo hhi⟩

theorem actual_odd_last_pivot (hp : 19≤p) :
    2*((p-1)/2)-1=p-2 ∧ ((p-2 : ℕ) : ZMod p)≠0 := by
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := ho
  have hlast : 2*((p-1)/2)-1=p-2 := by omega
  have hj : (p-1)/2 ∈ Finset.Ico 1 ((p-1)/2+1) :=
    Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hu := (actual_odd_pivot_band p hp ((p-1)/2) hj).2.2
  rw [hlast] at hu
  exact ⟨hlast,hu⟩

private theorem actual_odd_proper_even (hp : 19≤p) :
    (actualOddProperProduct p).comp (-X)=actualOddProperProduct p := by
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
  unfold actualOddProperProduct
  rw [mul_comp,mul_comp,hY,hn,hO]
  linear_combination (actualLegendreJacobi p*properLegendreJacobi p*OP p)*hs

private theorem actual_odd_proper_conic (hp : 19≤p) :
    (actualOddProperPull p).comp conic=(actualOddProperProduct p).comp Tc := by
  have he := even_native_attachment p hp (actualOddProperProduct p)
    (actual_odd_proper_even p hp)
  rw [actualOddProperPull,comp_assoc,actual_native_V_conic p hp,
    show (1-Tc^2 : (ZMod p)[X])=(1-X^2 : (ZMod p)[X]).comp Tc by
      simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,he]

private theorem actual_even_pull_conic (hp : 19≤p) :
    (actualEvenPull p).comp conic=(EP p : (ZMod p)[X]).comp Tc := by
  have he := congrArg (fun Q : (ZMod p)[X] => Q.comp Tc)
    (evenSquared_square (K := ZMod p) p hp)
  simp only [comp_assoc,pow_comp,X_comp] at he
  rw [actualEvenPull,comp_assoc,V_conic p hp,he]

/-- The positive Frobenius phase is the entire Tc^p carrier under the actual conic. -/
theorem actual_positive_phase_CB_conic (hp : 19≤p) :
    ((4*X^p-11)*ActualFirstGreen.CB p).comp conic=
      Tc^p*(actualLegendreJacobi p).comp Tc*(properLegendreJacobi p).comp Tc := by
  let c : (ZMod p)[X] := 4*X^2-3
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hnum (n : ℕ) : (n : (ZMod p)[X])^p=n := by
    have he := congrArg (Polynomial.C : ZMod p →+* (ZMod p)[X])
      (ZMod.pow_card (n : ZMod p))
    simpa only [map_pow,map_natCast] using he
  have h4p : (4 : (ZMod p)[X])^p=4 := by
    simpa only [Nat.cast_ofNat] using hnum 4
  have h5p : (5 : (ZMod p)[X])^p=5 := by
    simpa only [Nat.cast_ofNat] using hnum 5
  have h11p : (11 : (ZMod p)[X])^p=11 := by
    simpa only [Nat.cast_ofNat] using hnum 11
  have hu5 : (5 : (ZMod p)[X])*Polynomial.C (1/5 : ZMod p)=1 := by
    change Polynomial.C (5 : ZMod p)*Polynomial.C (1/5 : ZMod p)=1
    rw [←Polynomial.C_mul,mul_one_div_cancel h5,Polynomial.C_1]
  have hTc : (Tc : (ZMod p)[X])=X*c := by dsimp only [Tc,c]; ring
  have hbase : (4*X-11 : (ZMod p)[X]).comp conic=5*c := by
    simp only [conic,mul_comp,sub_comp,ofNat_comp,X_comp]
    dsimp only [c]
    ring
  have hbp : (4*X^p-11 : (ZMod p)[X]).comp conic=5*c^p := by
    calc
      _=((4*X-11 : (ZMod p)[X])^p).comp conic := by
        rw [sub_pow_char,mul_pow,h4p,h11p]
      _=((4*X-11 : (ZMod p)[X]).comp conic)^p := by rw [pow_comp]
      _=(5*c)^p := by rw [hbase]
      _=_ := by rw [mul_pow,h5p]
  rw [mul_comp,hbp,(ActualFirstGreen.actual_carrier_pullbacks p hp).1]
  simp only [ActualFirstGreen.CBt,ActualFirstGreen.B,mul_comp]
  calc
    _=(5*Polynomial.C (1/5 : ZMod p))*(X*c)^p*
        (actualLegendreJacobi p).comp Tc*(properLegendreJacobi p).comp Tc := by
      rw [mul_pow]
      ring
    _=_ := by rw [hu5,one_mul,←hTc]

/-- Quadratic descent of the same properSource keeps both Frobenius phases. -/
theorem actual_proper_pull_split (hp : 19≤p) :
    actualProperPull p=actualOddProperPull p+
      (4*X^p-11)*ActualFirstGreen.CB p*actualEvenPull p := by
  apply conic_comp_injective p hp
  have he := (original_proper_product_native p hp).1
  have hq : (actualProperPull p).comp conic=(originalProperProduct p).comp Tc := by
    rw [actualProperPull,comp_assoc,actual_native_V_conic p hp,
      show (1-Tc^2 : (ZMod p)[X])=(1-X^2 : (ZMod p)[X]).comp Tc by
        simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,he]
  rw [hq,add_comp,mul_comp,actual_odd_proper_conic p hp,
    actual_positive_phase_CB_conic p hp,actual_even_pull_conic p hp]
  simp only [originalProperProduct,actualOddProperProduct,mul_comp,add_comp,
    pow_comp,X_comp]
  ring

/-- The actual A is the full even log plus its original q-h value. -/
theorem actual_A_even_source (hp : 19≤p) :
    actualAPull p=Polynomial.C (WPFiniteNC122.q p-fieldHarmonic p (p/6))+
      actualEvenPull p := by
  rw [actualAPull,actualLogMinusH,sub_comp,C_comp,actual_log_V_attachment p hp,
    LV,actualEvenPull]
  simp only [Polynomial.C_sub]
  ring

private theorem original_reciprocal_cleared (G : (ZMod p)[X]) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*reciprocalDensity G=
      (substituteOver G originalQ-LaurentPolynomial.C (G.coeff 0))*(33-12*T 1) := by
  have hd : X*G.divX=G-Polynomial.C (G.coeff 0) := by
    linear_combination X_mul_divX_add G
  have hs := congrArg
    (Polynomial.eval₂RingHom LaurentPolynomial.C (originalQ : (ZMod p)[T;T⁻¹])) hd
  have hs' : originalQ*substituteOver G.divX originalQ=
      substituteOver G originalQ-LaurentPolynomial.C (G.coeff 0) := by
    simpa only [substituteOver,Polynomial.coe_eval₂RingHom,map_mul,map_sub,
      Polynomial.eval₂_X,Polynomial.eval₂_C] using hs
  rw [reciprocalDensity_factor]
  calc
    _=substituteOver G.divX originalQ*
        ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*Fnegative) := by ring
    _=substituteOver G.divX originalQ*(originalQ*(33-12*T 1)) := by
      rw [original_cubic_density_cleared]
    _=_ := by rw [←hs']; ring

/-- The actual zero slot is proved before divX, so no source term is lost. -/
theorem actual_proper_origin_cleared (hp : 19≤p) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
        SourceClosureCommonWholeSource.properOriginDensity p=
      -3*(4*T 1-11)*
        (T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperPull p).toLaurent) := by
  let G := quadraticInverse (originalProperProduct p)
  have h0 : G.coeff 0=0 := (original_proper_product_native p hp).2
  have ht : substituteOver G (originalQ : (ZMod p)[T;T⁻¹])=
      invert (actualProperPull p).toLaurent := by
    rw [originalQ,←substituteOver_invert,substituteOver_toLaurent,
      ActualLowEuler.Qrev_eq_fieldV p]
    rfl
  have he := original_reciprocal_cleared p G
  rw [h0,map_zero,sub_zero,ht] at he
  change (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
    (T (((p-1)/2 : ℕ) : ℤ)*reciprocalDensity G)=_
  linear_combination T (((p-1)/2 : ℕ) : ℤ)*he

/-- Reflection transports the entire proper kernel, including the negative phase phi. -/
theorem actual_proper_pull_reflection (hp : 19≤p) :
    T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperPull p).toLaurent=
      T (((p-1)/2 : ℕ) : ℤ)*invert (actualOddProperPull p).toLaurent+
        (4*T (-(p : ℤ))-11)*actualBv p*invert (actualEvenPull p).toLaurent := by
  have he := congrArg (fun Q : (ZMod p)[X] => invert Q.toLaurent)
    (actual_proper_pull_split p hp)
  simp only [map_add,map_mul,map_sub,map_ofNat,Polynomial.toLaurent_X_pow,
    invert_T] at he
  unfold actualBv
  linear_combination T (((p-1)/2 : ℕ) : ℤ)*he

/-- This is the literal original full j, after multiplication by Bv makes it Laurent. -/
theorem actual_full_j_literal (hp : 19≤p) :
    actualFullJProduct p=
      T (((p-1)/2 : ℕ) : ℤ)*invert (actualOddProperPull p).toLaurent+
        (4*T (-(p : ℤ))-11)*actualBv p*
          (invert (actualAPull p).toLaurent-
            LaurentPolynomial.C (WPFiniteNC122.q p-fieldHarmonic p (p/6))+
            LaurentPolynomial.C (1/3 : ZMod p)*(actualAPull p).toLaurent) := by
  have he := congrArg (fun Q : (ZMod p)[X] => invert Q.toLaurent)
    (actual_A_even_source p hp)
  simp only [map_add,Polynomial.toLaurent_C,invert_C] at he
  unfold actualFullJProduct
  linear_combination -(4*T (-(p : ℤ))-11)*actualBv p*he

theorem actual_full_j_proper_source (hp : 19≤p) :
    actualFullJProduct p=
      T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperPull p).toLaurent+
        LaurentPolynomial.C (1/3 : ZMod p)*(4*T (-(p : ℤ))-11)*
          actualBv p*(actualAPull p).toLaurent := by
  have he := actual_proper_pull_reflection p hp
  unfold actualFullJProduct
  linear_combination -he

/-- The retained reflected Sigma numerator has exactly this contribution after pole reduction. -/
theorem actual_reflected_sigma_source_attachment (hp : 19≤p) :
    LaurentPolynomial.C (-2/3 : ZMod p)*T (2*(p : ℤ))*
        invert (actualReflectedSigmaWeightedNumerator p hp)=
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent^p*
        (nativeKSigma p*(4*T 1-11)*(actualSigmaPullback p hp).toLaurent) := by
  have he := actual_reflected_sigma_native_kernel p hp
  simpa only [mul_assoc] using he

/-- The original proper and full j sources cancel as whole carriers, before any residue. -/
theorem actual_Jjoint_original_kernel (hp : 19≤p) :
    actualJjoint p hp=
      nativeKSigma p*(4*T 1-11)*(actualSigmaPullback p hp).toLaurent+
        LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
          actualBv p*(actualAPull p).toLaurent := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hscale : LaurentPolynomial.C (2/3 : ZMod p)*3=
      (2 : (ZMod p)[T;T⁻¹]) := by
    change LaurentPolynomial.C (2/3 : ZMod p)*LaurentPolynomial.C (3 : ZMod p)=
      LaurentPolynomial.C (2 : ZMod p)
    rw [←map_mul,div_mul_cancel₀ _ h3]
  have hthird : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/3 : ZMod p)=
      LaurentPolynomial.C (2/3 : ZMod p) := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/3 : ZMod p)=_
    rw [←map_mul]
    congr 1
    ring
  rw [actualJjoint,actualJSubtractionCleared]
  rw [show LaurentPolynomial.C (2/3 : ZMod p)*
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
        SourceClosureCommonWholeSource.properOriginDensity p=
      LaurentPolynomial.C (2/3 : ZMod p)*
        ((WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*
          SourceClosureCommonWholeSource.properOriginDensity p) by ring,
    actual_proper_origin_cleared p hp,actual_full_j_proper_source p hp]
  linear_combination
    -(4*T 1-11)*(T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperPull p).toLaurent)*hscale+
      (4*T 1-11)*(4*T (-(p : ℤ))-11)*actualBv p*(actualAPull p).toLaurent*hthird

/-- Root-free SB72 and its actual antisymmetric defect give the whole metric identity. -/
theorem actual_coupled_metric_source (hp : 19≤p) :
    LaurentPolynomial.C (3/5 : ZMod p)*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      Dsym p=(ActualFirstGreen.CB p).toLaurent+actualBv p := by
  have hid : ActualThreePhase.φ (K := ZMod p) p=RingHom.id (ZMod p) :=
    Subsingleton.elim _ _
  have hδ := actual_deltaK_anti (K := ZMod p) p hp
  simp only [actualDeltaK,hid,Polynomial.map_id] at hδ
  rw [actual_SB72_ZMod p hp] at hδ
  simp only [map_sub,map_mul,Polynomial.toLaurent_C,invert_C] at hδ
  have hf := actual_fK_SB72_reflection (K := ZMod p) p hp
  simp only [ActualThreePhase.fK,hid,Polynomial.map_id] at hf
  have hsum : (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p=
      LaurentPolynomial.C (5/3 : ZMod p)*
        ((ActualFirstGreen.CB p).toLaurent+actualBv p) := by
    dsimp only [Dsym,actualBv]
    linear_combination hδ+invert (Dstar p : (ZMod p)[X]).toLaurent*hf
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hunit : LaurentPolynomial.C (3/5 : ZMod p)*LaurentPolynomial.C (5/3 : ZMod p)=
      (1 : (ZMod p)[T;T⁻¹]) := by
    rw [←map_mul]
    have he : (3/5 : ZMod p)*(5/3)=1 := by field_simp [h3,h5]
    rw [he,map_one]
  linear_combination LaurentPolynomial.C (3/5 : ZMod p)*hsum+
    ((ActualFirstGreen.CB p).toLaurent+actualBv p)*hunit

theorem actual_coupled_Sigma_source (hp : 19≤p) :
    (actualSigmaPullback p hp).toLaurent=
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*(actualAPull p).toLaurent-
        (4*T (p : ℤ)-11)*(ActualFirstGreen.CB p).toLaurent := by
  have he := congrArg (fun Q : (ZMod p)[X] => Q.toLaurent)
    (actual_Sigma_V_source p hp)
  simpa only [actualSigmaPullback,actualAPull,actualLogMinusH,sub_comp,C_comp,
    actual_log_V_attachment p hp,actual_f_pullback_field_eq p hp,map_mul,map_sub,
    map_ofNat,Polynomial.toLaurent_X_pow] using he

/-- The same original coupled numerator, with no supplied source, carrier or scalar premise. -/
theorem actual_Jjoint_cleared_source (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualJjoint p hp=
      -LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
        ((ActualFirstGreen.CB p).toLaurent*(actualSigmaPullback p hp).toLaurent-
          (4*T (p : ℤ)-11)*(ActualFirstGreen.CB p).toLaurent*actualBv p) := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hscale : LaurentPolynomial.C (2/5 : ZMod p)=
      LaurentPolynomial.C (2/3 : ZMod p)*LaurentPolynomial.C (3/5 : ZMod p) := by
    rw [←map_mul]
    congr 1
    field_simp [h3,h5]
  have hm := actual_coupled_metric_source p hp
  have hs := actual_coupled_Sigma_source p hp
  -- The mixed Bv*Sigma terms cancel only after the complete Sigma source is used.
  -- The surviving high phase is alpha*CB*Bv, with alpha=4*x^p-11.
  have hwhole :
      LaurentPolynomial.C (3/5 : ZMod p)*
          (NativeChiFieldSource.halfPullbackField p hp).toLaurent*Dsym p*
            (actualSigmaPullback p hp).toLaurent-
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
          actualBv p*(actualAPull p).toLaurent=
      (ActualFirstGreen.CB p).toLaurent*(actualSigmaPullback p hp).toLaurent-
        (4*T (p : ℤ)-11)*(ActualFirstGreen.CB p).toLaurent*actualBv p := by
    linear_combination (actualSigmaPullback p hp).toLaurent*hm+actualBv p*hs
  rw [actual_Jjoint_original_kernel p hp,nativeKSigma]
  change _*(-LaurentPolynomial.C (2/5 : ZMod p)*(4*T (-(p : ℤ))-11)*Dsym p*
      (4*T 1-11)*(actualSigmaPullback p hp).toLaurent+
        LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
          actualBv p*(actualAPull p).toLaurent)=_
  rw [hscale]
  linear_combination
    -LaurentPolynomial.C (2/3 : ZMod p)*(4*T 1-11)*(4*T (-(p : ℤ))-11)*
      hwhole

end WPFieldAssembly.BalancedVbalSuccessorCoupledSource
