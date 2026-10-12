import WPFieldAssembly.ActualGreenResidue
import WPFieldAssembly.ActualThreePhase
import WPFieldAssembly.FirstGreen
import WPFieldAssembly.NativeEulerIntegral

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly
  WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualGreenResidue

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

noncomputable def Hpull (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (WPFieldAssembly.NativeEulerPrimitive.nativeHField p).comp (WPHasseIntegralTransport.fieldV p)
noncomputable def HpullK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (Hpull p).map (ActualThreePhase.φ (K := K) p)

private theorem residue_HX_low (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨WPActualEtaPole.HX (p/6), WPActualEtaIntegrality.actual_HX_integral p (p/6)
        (by omega) (by omega)⟩ = (Hpull p).toLaurent := by
  let I := (WPFieldAssembly.NativeEulerPrimitive.nativeHIntegral p (by omega)).comp
    (WPHasseIntegralTransport.integralV p (by omega))
  have hi : (⟨WPActualEtaPole.HX (p/6),
        WPActualEtaIntegrality.actual_HX_integral p (p/6) (by omega) (by omega)⟩ :
      WPActualEtaIntegrality.integralLaurent p) =
      NativeChiFieldSource.polynomialLaurentModel p I := by
    apply Subtype.ext
    rw [NativeChiFieldSource.polynomialLaurentModel_val]
    simp only [I, Polynomial.map_comp,
      WPFieldAssembly.NativeEulerPrimitive.nativeHIntegral_map_rational,
      WPHasseIntegralTransport.integralV_map_rational]
    exact WPActualChiSource.substituteOver_toLaurent
      (WPActualPullbackSource.Hpolynomial (p/6)) WPActualPullbackSource.Vpolynomial
  rw [hi, NativeChiFieldSource.residue_polynomialLaurentModel]
  simp only [I, Polynomial.map_comp,
    WPFieldAssembly.NativeEulerPrimitive.nativeHIntegral_map_field,
    WPHasseIntegralTransport.integralV_map_field, Hpull]

private theorem residue_HX_literal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨WPActualEtaPole.HX (p-1-p/6), WPActualEtaIntegrality.actual_HX_integral
        p (p-1-p/6) (by omega) (by omega)⟩ = (Hpull p).toLaurent := by
  let H : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.HX (p-1-p/6),
      WPActualEtaIntegrality.actual_HX_integral p _ (by omega) (by omega)⟩
  let H0 : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.HX (p/6),
      WPActualEtaIntegrality.actual_HX_integral p _ (by omega) (by omega)⟩
  obtain ⟨hi,hz⟩ := WPActualResidueVanishing.actual_HX_low_cutoff
    p (p-1-p/6) (by omega) (by omega) (by omega)
  have hsub : (⟨H.val-H0.val,hi⟩ : WPActualEtaIntegrality.integralLaurent p)=H-H0 := by
    apply Subtype.ext
    rfl
  rw [hsub,map_sub] at hz
  exact (sub_eq_zero.mp hz).trans (residue_HX_low p hp)

private theorem residue_chi_literal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPLaurentIntegralResidue.residueLaurent p
      ⟨WPActualEtaPole.chiX p ((p-1)/2) (p-1-p/6),
        WPActualChiSource.actual_chiX_integral p _ (by omega) (by omega) (by omega)⟩ =
      NativeChiFieldSource.halfChiField p hp := by
  let X : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.chiX p ((p-1)/2) (p-1-p/6),
      WPActualChiSource.actual_chiX_integral p _ (by omega) (by omega) (by omega)⟩
  let X0 := NativeShiftedChi.halfChiIntegral p hp
  obtain ⟨hi,hz⟩ := WPActualEtaFieldCutoff.actual_chi_tail_residue_zero
    p (p-1-p/6) (by omega) (by omega) (by omega)
  have hsub : (⟨X.val-X0.val,hi⟩ : WPActualEtaIntegrality.integralLaurent p)=X-X0 := by
    apply Subtype.ext
    rfl
  change WPLaurentIntegralResidue.residueLaurent p
    (⟨X.val-X0.val,hi⟩ : WPActualEtaIntegrality.integralLaurent p) = 0 at hz
  rw [hsub,map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Integral divided differences are reduced after the actual rational quotients are formed. -/
theorem literal_Peta_transport (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualFieldPrimitive.literalFieldPeta p hp =
      GreenLaurentOperators.eta (NativeChiFieldSource.halfChiField p hp) (Hpull p).toLaurent := by
  let R := WPPIntegralReduction.integralRationals p
  let X : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.chiX p ((p-1)/2) (p-1-p/6),
      WPActualChiSource.actual_chiX_integral p _ (by omega) (by omega) (by omega)⟩
  let H : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.HX (p-1-p/6),
      WPActualEtaIntegrality.actual_HX_integral p _ (by omega) (by omega)⟩
  have ha : (1/4 : ℚ) ∈ R := WPFiniteConductorPolynomial.small_inverse_integral
    p 4 (by norm_num) (by omega)
  have hb : (4 : ℚ) ∈ R := natCast_mem R 4
  have hai : (1/4 : ℚ)⁻¹ ∈ R := by simp
  have hbi : (4 : ℚ)⁻¹ ∈ R := by simpa only [one_div] using ha
  let DA : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.dividedDifference (1/4) (X+H).val,
      WPActualEtaIntegrality.dividedDifference_integral p _ ha hai _ (X+H).property⟩
  let DB : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.dividedDifference 4 (X+H).val,
      WPActualEtaIntegrality.dividedDifference_integral p _ hb hbi _ (X+H).property⟩
  let E : WPActualEtaIntegrality.integralLaurent p :=
    ⟨WPActualEtaPole.Peta p ((p-1)/2) (p-1-p/6),
      WPActualEtaIntegrality.actual_Peta_integral p _ (by omega) (by omega) (by omega)⟩
  have he : E=2*DA+DB-NativeChiFieldSource.halfLaurent p hp*H*
      NativeChiFieldSource.integralT p (-1) := by
    apply Subtype.ext
    rfl
  have hE : WPActualFieldPrimitive.literalFieldPeta p hp =
      WPLaurentIntegralResidue.residueLaurent p E := by
    ext j
    rw [WPActualFieldPrimitive.literalFieldPeta,WPPIntegralReduction.reduceLaurent_coeff,
      WPLaurentIntegralResidue.residueLaurent_coeff]
  have hDa := GreenLaurentOperators.residueLaurent_DD p (1/4) ha hai (X+H)
  have hDb := GreenLaurentOperators.residueLaurent_DD p 4 hb hbi (X+H)
  have hq : ((1/4 : ℚ) : ZMod p)=(1/4 : ZMod p) := by norm_num [Rat.cast_def]
  have hqinv : (((1/4 : ℚ)⁻¹ : ℚ) : ZMod p)=4 := by norm_num
  have hbinv : (((4 : ℚ)⁻¹ : ℚ) : ZMod p)=1/4 := by
    simpa only [one_div] using hq
  have hbcast : ((4 : ℚ) : ZMod p) = (4 : ZMod p) := by norm_num
  rw [hE,he]
  simp only [map_sub,map_add,map_mul,map_ofNat,
    NativeChiFieldSource.residue_halfLaurent,NativeChiFieldSource.halfField_eq,
    NativeChiFieldSource.residue_integralT]
  rw [hDa,hDb,hq,hqinv,hbinv,hbcast]
  simp only [map_add]
  rw [residue_chi_literal p hp,residue_HX_literal p hp]
  unfold GreenLaurentOperators.eta GreenLaurentOperators.weightedDD
  simp only [map_add, map_ofNat]

/-- Generic field base change preserves the actual literal middle residue. -/
theorem actual_eta_middle_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (GreenLaurentOperators.eta (ActualThreePhase.χK (K := K) p hp)
      (HpullK (K := K) p).toLaurent).coeff ((p : ℤ)-1)=0 := by
  have hn := literal_Peta_middle_zero p hp
  rw [literal_Peta_transport p hp] at hn
  have hmap := congrArg (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p))
    (literal_Peta_transport p hp)
  simp only [GreenLaurentOperators.eta,weightedDD,map_sub,map_add,map_mul,
    WPActualChiSource.coefficientMap_C,WPActualChiSource.coefficientMap_T,
    GreenLaurentOperators.DD_map,map_div₀,map_one,map_ofNat,
    WPActualChiSource.coefficientMap_toLaurent] at hmap
  have he : WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
      (WPActualFieldPrimitive.literalFieldPeta p hp) =
      GreenLaurentOperators.eta (ActualThreePhase.χK (K := K) p hp)
        (HpullK (K := K) p).toLaurent := by
    simpa only [GreenLaurentOperators.eta, weightedDD, ActualThreePhase.χK,
      HpullK, map_add, map_ofNat] using hmap
  rw [←he,WPActualChiSource.coefficientMap_coeff,literal_Peta_middle_zero p hp,map_zero]

noncomputable def Kpull (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (WPActualPositivePair.eulerPrimitive p (WPFieldAssembly.NativeEulerPrimitive.nativeHField p)).comp
    (WPHasseIntegralTransport.fieldV p)
noncomputable def KpullK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (Kpull p).map (ActualThreePhase.φ (K := K) p)
noncomputable def CMK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (ActualFirstGreen.CM p).map (ActualThreePhase.φ (K := K) p)
noncomputable def hK (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  ActualThreePhase.φ (K := K) p (WPActualGaussBottom.fieldHarmonic p (p/6))
noncomputable def VK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (WPHasseIntegralTransport.fieldV p).map (ActualThreePhase.φ (K := K) p)

private theorem native_H_theta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (X : (ZMod p)[X])*(WPFieldAssembly.NativeEulerPrimitive.nativeHField p).derivative =
      WPActualNativeHasse.nativeField p (p/6)-1 := by
  have he : WPFieldAssembly.NativeEulerPrimitive.nativeHField p =
      WPActualPositivePair.eulerPrimitive p (WPActualNativeHasse.nativeField p (p/6)-1) := by
    unfold WPFieldAssembly.NativeEulerPrimitive.nativeHField
    ext n
    rw [WPActualPositivePair.eulerPrimitive_coeff,WPActualPositivePair.eulerPrimitive_coeff]
    by_cases hn : n=0
    · subst n; simp
    · simp [Polynomial.coeff_sub,Polynomial.coeff_one,hn]
  rw [he]
  apply WPActualPositivePair.eulerPrimitive_derivative
  · have hd : (WPActualNativeHasse.nativeField p (p / 6) - 1).natDegree ≤ p / 6 :=
      (natDegree_sub_le _ _).trans (max_le
      (WPActualNativeHasse.actual_native_field_degree p) (by simp))
    exact hd.trans_lt (by omega)
  · rw [Polynomial.coeff_sub,Polynomial.coeff_one_zero,
      Polynomial.coeff_zero_eq_eval_zero,WPActualNativeHasse.actual_native_field_origin]
    ring

private theorem native_K_theta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (X : (ZMod p)[X])*
      (WPActualPositivePair.eulerPrimitive p (WPFieldAssembly.NativeEulerPrimitive.nativeHField p)).derivative =
      WPFieldAssembly.NativeEulerPrimitive.nativeHField p :=
  WPActualPositivePair.eulerPrimitive_derivative p _
    ((WPFieldAssembly.NativeEulerPrimitive.nativeHField_degree p).trans_lt (by omega))
    (WPFieldAssembly.NativeEulerPrimitive.nativeHField_origin p)

private theorem VK_formula (p : ℕ) [Fact p.Prime] [CharP K p] :
    VK (K := K) p = Polynomial.C (1/125 : K)*(4*X-1)^2*(4-X) := by
  have hc : (((1 / 125 : ℚ) : ZMod p)) = (1 / 125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Rat.cast_inv_nat (α := ZMod p) 125)
  simp only [VK,WPHasseIntegralTransport.fieldV,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_ofNat,Polynomial.map_one,
    Polynomial.map_X,hc,map_div₀,map_one,map_ofNat]

private theorem VK_logarithmic (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteZSource.Abar : K[X])*(VK (K := K) p).derivative =
      VK p*(33-12*X) := by
  rw [VK_formula]
  simp only [WPFiniteZSource.Abar,Polynomial.derivative_mul,Polynomial.derivative_C,
    Polynomial.derivative_pow,Polynomial.derivative_sub,Polynomial.derivative_ofNat,
    Polynomial.derivative_X,Polynomial.derivative_one,zero_mul,
    zero_add,mul_one]
  norm_num only [Nat.cast_ofNat, map_ofNat]
  ring

private theorem fK_native (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualThreePhase.fK (K := K) p hp =
      ((WPActualNativeHasse.nativeField p (p/6)).map (ActualThreePhase.φ p)).comp (VK p) := by
  rw [ActualThreePhase.fK,NativeChiFieldSource.halfPullbackField_eq,
    WPActualNativeHasse.actual_full_native_field_cutoff p ((p-1)/2)
      (by omega) (by omega) (by omega),Polynomial.map_comp]
  rfl

private theorem chart_euler (p : ℕ) [Fact p.Prime] [CharP K p]
    (Y J : K[X]) (c : K) (hθ : X*J.derivative=Y-Polynomial.C c) :
    (WPFiniteZSource.Abar : K[X])*(J.comp (VK p)).derivative =
      (Y.comp (VK p)-Polynomial.C c)*(33-12*X) := by
  have ht := congrArg (fun Q : K[X] => Q.comp (VK p)) hθ
  simp only [Polynomial.mul_comp,Polynomial.X_comp,Polynomial.sub_comp,
    Polynomial.C_comp] at ht
  rw [Polynomial.derivative_comp]
  have hv := VK_logarithmic (K := K) p
  linear_combination (J.derivative.comp (VK p))*hv + (33-12*X)*ht

/-- Both actual Euler pullbacks are attached to the original logarithmic source. -/
theorem actual_two_Euler_sources (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent*WPFiniteLaurentDifferential.D (HpullK p).toLaurent =
      ((ActualThreePhase.fK (K := K) p hp).toLaurent-1)*(33-12*T 1) ∧
    (WPFiniteZSource.Abar : K[X]).toLaurent*WPFiniteLaurentDifferential.D (KpullK p).toLaurent =
      (HpullK (K := K) p).toLaurent*(33-12*T 1) := by
  have hH := congrArg (fun Q : (ZMod p)[X] => Q.map (ActualThreePhase.φ (K := K) p))
    (native_H_theta p hp)
  have hJ := congrArg (fun Q : (ZMod p)[X] => Q.map (ActualThreePhase.φ (K := K) p))
    (native_K_theta p hp)
  simp only [Polynomial.map_mul,Polynomial.map_X,Polynomial.map_sub,
    Polynomial.map_one,←Polynomial.derivative_map] at hH hJ
  have hsH := chart_euler (K := K) p
    ((WPActualNativeHasse.nativeField p (p/6)).map (ActualThreePhase.φ p))
    ((WPFieldAssembly.NativeEulerPrimitive.nativeHField p).map (ActualThreePhase.φ p)) 1
    (by simpa using hH)
  have hsJ := chart_euler (K := K) p
    ((WPFieldAssembly.NativeEulerPrimitive.nativeHField p).map (ActualThreePhase.φ p))
    ((WPActualPositivePair.eulerPrimitive p (WPFieldAssembly.NativeEulerPrimitive.nativeHField p)).map
      (ActualThreePhase.φ p)) 0 (by simpa using hJ)
  have hHpull : HpullK (K := K) p =
      ((WPFieldAssembly.NativeEulerPrimitive.nativeHField p).map (ActualThreePhase.φ p)).comp
        (VK p) := by
    simp only [HpullK, Hpull, Polynomial.map_comp, VK]
  have hKpull : KpullK (K := K) p =
      ((WPActualPositivePair.eulerPrimitive p
        (WPFieldAssembly.NativeEulerPrimitive.nativeHField p)).map (ActualThreePhase.φ p)).comp
        (VK p) := by
    simp only [KpullK, Kpull, Polynomial.map_comp, VK]
  rw [← fK_native p hp, ← hHpull] at hsH
  rw [← hHpull, ← hKpull] at hsJ
  have hh := congrArg (fun Q : K[X] => Q.toLaurent) hsH
  have hj := congrArg (fun Q : K[X] => Q.toLaurent) hsJ
  simp only [
    map_mul,map_sub,map_ofNat,map_one,map_zero,sub_zero,Polynomial.toLaurent_X,
    ←WPFiniteLaurentDifferential.D_toLaurent] at hh hj
  exact ⟨hh,hj⟩

private theorem D_map {L : Type*} [Field L] (f : K →+* L) (G : K[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (WPFiniteLaurentDifferential.D G) =
      WPFiniteLaurentDifferential.D (WPActualChiSource.coefficientMap f G) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff,WPFiniteLaurentDifferential.D_coeff,
    WPFiniteLaurentDifferential.D_coeff,WPActualChiSource.coefficientMap_coeff,
    map_mul,map_intCast]

private theorem zeta_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p) (ActualFirstGreen.zeta p) =
      ActualChiEndpoints.zeta (K := K) p := by
  simp only [ActualFirstGreen.zeta,ActualChiEndpoints.zeta,map_mul,map_pow,
    WPActualChiSource.coefficientMap_C,WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_toLaurent,map_div₀,map_one,map_ofNat,
    WPFiniteZSource.Abar,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_ofNat,
    Polynomial.map_X,Polynomial.map_one]

private theorem R_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
      (WPFiniteZSource.R (K := ZMod p) p)=WPFiniteZSource.R (K := K) p := by
  simp only [WPFiniteZSource.R,map_mul,map_pow,WPActualChiSource.coefficientMap_C,
    WPActualChiSource.coefficientMap_T,WPActualChiSource.coefficientMap_toLaurent,
    map_div₀,map_one,map_ofNat,WPFiniteZSource.Abar,WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_C,
    Polynomial.map_ofNat,Polynomial.map_X,Polynomial.map_one,map_inv₀]

theorem actual_mapped_CM_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent*ActualChiEndpoints.zeta p*
      WPFiniteLaurentDifferential.D (CMK (K := K) p).toLaurent =
    (WPFiniteZSource.Abar : K[X]).toLaurent*WPFiniteZSource.R p*
      ((HpullK (K := K) p).toLaurent+2*LaurentPolynomial.C (hK p)) -
      ActualChiEndpoints.zeta p*(ActualThreePhase.CBK (K := K) p).toLaurent*(33-12*T 1) := by
  have hm := congrArg (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p))
    (ActualFirstGreen.actual_laurent_source p hp)
  simp only [map_sub,map_mul,map_ofNat,
    WPActualChiSource.coefficientMap_toLaurent,WPActualChiSource.coefficientMap_T,
    D_map,zeta_map,R_map] at hm
  simpa only [CMK,ActualThreePhase.CBK,HpullK,Hpull,hK,ActualFirstGreen.Hbar,
    Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_ofNat,
    map_add,map_mul,map_ofNat,Polynomial.toLaurent_C,
    WPFiniteZSource.Abar,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_one] using hm

noncomputable def candidateChi (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[T;T⁻¹] :=
  (ActualThreePhase.fK (K := K) p hp).toLaurent*WPFiniteZSource.P p u+
    ActualChiEndpoints.zeta p*(ActualThreePhase.CBK (K := K) p).toLaurent
noncomputable def greenPrimitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K[T;T⁻¹] :=
  WPFiniteZSource.P p u*((HpullK (K := K) p).toLaurent+2*LaurentPolynomial.C (hK p))+
    (KpullK (K := K) p).toLaurent-ActualChiEndpoints.zeta p*(CMK (K := K) p).toLaurent

theorem actual_candidate_green_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (WPFiniteZSource.Abar : K[X]).toLaurent*WPFiniteLaurentDifferential.D (greenPrimitive p u) =
      (candidateChi p hp u+(HpullK p).toLaurent-WPFiniteZSource.P p u)*(33-12*T 1)-
        (WPFiniteZSource.Abar : K[X]).toLaurent*
          ((HpullK p).toLaurent+2*LaurentPolynomial.C (hK p))*
          (LaurentPolynomial.C (1/2 : K)*T (-1)) := by
  obtain ⟨hH,hJ⟩ := actual_two_Euler_sources (K := K) p hp
  have hz := congrArg (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p))
    (ActualFirstGreen.zeta_derivative p hp)
  rw [D_map,zeta_map,map_zero] at hz
  exact FirstGreen.first_green_cleared
    (WPFiniteZSource.Abar : K[X]).toLaurent (33-12*T 1)
    (LaurentPolynomial.C (1/2 : K)*T (-1)) (WPFiniteZSource.R p)
    (ActualThreePhase.fK p hp).toLaurent (candidateChi p hp u) (WPFiniteZSource.P p u)
    (HpullK p).toLaurent (KpullK p).toLaurent (ActualChiEndpoints.zeta p)
    (ActualThreePhase.CBK p).toLaurent (CMK p).toLaurent (hK p)
    rfl (WPFiniteZSource.P_derivative p hp u) hH hJ hz (actual_mapped_CM_source p hp)

private theorem green_eta_identity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (h4 : (4 : K) ≠ 0)
    (χ P H G : K[T;T⁻¹]) (h : K)
    (ha : ev (1/4) (div_ne_zero one_ne_zero h4)
      (χ+H) = ev (1/4) (div_ne_zero one_ne_zero h4) P)
    (hb : ev 4 h4 (χ+H) = ev 4 h4 P)
    (hg : (WPFiniteZSource.Abar : K[X]).toLaurent*WPFiniteLaurentDifferential.D G =
      (χ+H-P)*(33-12*T 1)-(WPFiniteZSource.Abar : K[X]).toLaurent*
        (H+2*LaurentPolynomial.C h)*(LaurentPolynomial.C (1/2 : K)*T (-1))) :
    GreenLaurentOperators.eta χ H=WPFiniteLaurentDifferential.D G+weightedDD P+LaurentPolynomial.C h*T (-1) := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2
  have hu : (2 : K[T;T⁻¹])*LaurentPolynomial.C (1/2 : K)=1 := by
    change LaurentPolynomial.C (2 : K)*LaurentPolynomial.C (1/2 : K)=LaurentPolynomial.C 1
    rw [←map_mul,mul_one_div_cancel h2]
  have hχ := GreenLaurentOperators.weightedDD_cleared h4 (χ+H)
  have hP := GreenLaurentOperators.weightedDD_cleared h4 P
  rw [ha,hb] at hχ
  apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := K) p hp)
  unfold GreenLaurentOperators.eta
  linear_combination hχ-hP-hg+
    (WPFiniteZSource.Abar : K[X]).toLaurent*LaurentPolynomial.C h*T (-1)*hu

private theorem ev_toLaurent (a : K) (ha : a ≠ 0) (Q : K[X]) :
    GreenLaurentOperators.ev a ha Q.toLaurent=Q.eval a := by
  rw [GreenLaurentOperators.ev,LaurentPolynomial.eval₂_toLaurent]
  rfl

theorem actual_native_pullback_facts (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualThreePhase.fK (K := K) p hp).natDegree<p ∧
    (ActualThreePhase.fK (K := K) p hp).eval (1/4)=1 ∧
    (ActualThreePhase.fK (K := K) p hp).eval 4=1 ∧
    (HpullK (K := K) p).eval (1/4)=0 ∧ (HpullK (K := K) p).eval 4=0 := by
  let Y := (WPActualNativeHasse.nativeField p (p/6)).map (ActualThreePhase.φ (K := K) p)
  let J := (WPFieldAssembly.NativeEulerPrimitive.nativeHField p).map (ActualThreePhase.φ (K := K) p)
  have hf : ActualThreePhase.fK (K := K) p hp=Y.comp (VK p) := fK_native p hp
  have hh : HpullK (K := K) p=J.comp (VK p) := by
    simp only [HpullK,Hpull,Polynomial.map_comp,J,VK]
  have hy : Y.eval 0=1 := by
    rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_map,
      Polynomial.coeff_zero_eq_eval_zero,WPActualNativeHasse.actual_native_field_origin,map_one]
  have hj : J.eval 0=0 := by
    rw [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_map,
      WPFieldAssembly.NativeEulerPrimitive.nativeHField_origin,map_zero]
  have h4 := WPFiniteField.denominator_ne_zero (K := K) p 4 (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h4
  have hva : (VK (K := K) p).eval (1/4)=0 := by
    rw [VK_formula]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_sub,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,
      mul_one_div_cancel h4,sub_self,zero_pow (by omega : (2 : ℕ)≠0),mul_zero,zero_mul]
  have hvb : (VK (K := K) p).eval 4=0 := by rw [VK_formula]; simp
  have hdY : Y.natDegree≤p/6 :=
    Polynomial.natDegree_map_le.trans (WPActualNativeHasse.actual_native_field_degree p)
  have hdV : (VK (K := K) p).natDegree≤3 := by rw [VK_formula]; compute_degree
  have hd : (ActualThreePhase.fK (K := K) p hp).natDegree<p := by
    rw [hf]
    exact (Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul hdY hdV)).trans_lt (by
      have := Nat.div_mul_le_self p 6
      omega)
  refine ⟨hd,?_,?_,?_,?_⟩
  · rw [hf,Polynomial.eval_comp,hva,hy]
  · rw [hf,Polynomial.eval_comp,hvb,hy]
  · rw [hh,Polynomial.eval_comp,hva,hj]
  · rw [hh,Polynomial.eval_comp,hvb,hj]

/-- The actual scaled CM is the complete Green primitive contribution. -/
theorem actual_candidate_eta_formula (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    GreenLaurentOperators.eta (candidateChi (K := K) p hp u) (HpullK p).toLaurent =
      WPFiniteLaurentDifferential.D (greenPrimitive p u)+
        weightedDD (WPFiniteZSource.P p u)+LaurentPolynomial.C (hK p)*T (-1) := by
  obtain ⟨_,hfa,hfb,hHa,hHb⟩ := actual_native_pullback_facts (K := K) p hp
  have h4 : (4 : K) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.denominator_ne_zero (K := K) p 4
      (Finset.mem_Ico.mpr (by omega))
  let ha := div_ne_zero one_ne_zero h4
  have hz := ActualChiEndpoints.zeta_CB_endpoints (K := K) p hp
    (ActualThreePhase.CBK (K := K) p).toLaurent
  have hza : ev (1/4) ha
      (ActualChiEndpoints.zeta p*(ActualThreePhase.CBK p).toLaurent)=0 := by
    have hu : Units.mk0 (1/4 : K) ha = (ActualChiEndpoints.fourUnit (K := K) p hp)⁻¹ := by
      apply Units.ext
      simp [ActualChiEndpoints.fourUnit, one_div]
    unfold ev
    rw [hu]
    exact hz.2
  have hzb : ev 4 h4
      (ActualChiEndpoints.zeta p*(ActualThreePhase.CBK p).toLaurent)=0 := by
    have hu : Units.mk0 (4 : K) h4 = ActualChiEndpoints.fourUnit (K := K) p hp := by
      apply Units.ext
      rfl
    unfold ev
    rw [hu]
    exact hz.1
  apply green_eta_identity p hp h4 (candidateChi p hp u) (WPFiniteZSource.P p u)
    (HpullK p).toLaurent (greenPrimitive p u) (hK p)
  · rw [map_add,candidateChi,map_add,map_mul,ev_toLaurent,hfa,hza,
      ev_toLaurent,hHa]
    ring
  · rw [map_add,candidateChi,map_add,map_mul,ev_toLaurent,hfb,hzb,
      ev_toLaurent,hHb]
    ring
  · exact actual_candidate_green_source p hp u

theorem actual_candidate_eta_middle_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=1/5) :
    (GreenLaurentOperators.eta (candidateChi (K := K) p hp u) (HpullK p).toLaurent).coeff ((p : ℤ)-1)=0 := by
  rw [actual_candidate_eta_formula p hp u]
  have hs : (LaurentPolynomial.C (hK (K := K) p)*T (-1)).coeff ((p : ℤ)-1)=0 := by
    rw [←LaurentPolynomial.single_eq_C_mul_T]
    change (Finsupp.single (-1 : ℤ) (hK (K := K) p)) ((p : ℤ)-1) = 0
    simp only [Finsupp.single_apply,if_neg (by omega : (-1 : ℤ)≠(p : ℤ)-1)]
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    derivative_middle_zero,finite_P_middle_zero p hp u hu,hs,zero_add]

/-- The actual literal residue and normalized Green primitive kill all three phases. -/
theorem actual_chi_finite_P (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=1/5) :
    ActualThreePhase.χK (K := K) p hp =
      (ActualThreePhase.fK (K := K) p hp).toLaurent*WPFiniteZSource.P p u+
        ActualChiEndpoints.zeta p*(ActualThreePhase.CBK (K := K) p).toLaurent := by
  obtain ⟨α,β,γ,hχ,ha,hb⟩ := ActualThreePhase.actual_half_chi_three_phase (K := K) p hp u
  let phasePart : K[T;T⁻¹] := LaurentPolynomial.C α*T (p : ℤ)+
    LaurentPolynomial.C β+LaurentPolynomial.C γ*T (-(p : ℤ))
  have hχ' : ActualThreePhase.χK (K := K) p hp=candidateChi p hp u+
      (ActualThreePhase.fK p hp).toLaurent*phasePart := by
    rw [hχ]
    unfold candidateChi
    dsimp only [phasePart]
    ring
  have hη : GreenLaurentOperators.eta (ActualThreePhase.χK (K := K) p hp) (HpullK p).toLaurent =
      GreenLaurentOperators.eta (candidateChi p hp u) (HpullK p).toLaurent+
        weightedDD ((ActualThreePhase.fK p hp).toLaurent*phasePart) := by
    rw [hχ']
    unfold GreenLaurentOperators.eta weightedDD
    simp only [map_add]
    ring
  obtain ⟨hdeg,hfa,hfb,_,_⟩ := actual_native_pullback_facts (K := K) p hp
  have hphase : (weightedDD ((ActualThreePhase.fK p hp).toLaurent*phasePart)).coeff
      ((p : ℤ)-1)=3*α := by
    simpa only [weightedDD,phasePart,map_ofNat] using GreenLaurentOperators.homogeneous_middle p (by omega)
      (ActualThreePhase.fK (K := K) p hp) hdeg hfa hfb α β γ
  have hc := congrArg (fun L : K[T;T⁻¹] => L.coeff ((p : ℤ)-1)) hη
  rw [actual_eta_middle_zero p hp,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    actual_candidate_eta_middle_zero p hp u hu,hphase,zero_add] at hc
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 := WPFiniteField.denominator_ne_zero (K := K) p 4 (Finset.mem_Ico.mpr (by omega))
  have h15 := WPFiniteField.denominator_ne_zero (K := K) p 15 (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3 h4 h15
  obtain ⟨hα,hβ,hγ⟩ := FirstGreen.three_phase_zero h3 h4 h15 α β γ ha hb hc.symm
  rw [hα,hβ,hγ] at hχ
  simpa only [map_zero,zero_mul,add_zero] using hχ

end WPFieldAssembly.ActualGreenResidue
