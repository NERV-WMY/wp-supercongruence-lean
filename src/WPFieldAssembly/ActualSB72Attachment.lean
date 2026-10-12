import WPFieldAssembly.ActualSB72Finite
import WPFieldAssembly.ActualBpairSigma
import WPFieldAssembly.ActualEtaTransport
import WPActualNativeChiTaylor
import WPActualPartialHarmonic
import WPFiniteJWeightedResidue
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000



section LiteralDelta
open WPActualNativeChiTaylor WPActualPullbackSource WPActualEtaPole
  WPActualChiSource WPFiniteLaurentIntegral WPPIntegralReduction
  WPActualEtaIntegrality NativeChiFieldSource WPLaurentIntegralResidue

noncomputable def nativeTermPullbackQ (p : ℕ) : ℚ[X] :=
  (nativeTermPolynomial p).comp Vpolynomial

theorem nativeTermPullbackQ_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeTermPullbackQ p).natDegree ≤ (p - 1) / 2 := by
  have hV : Vpolynomial.natDegree ≤ 3 := by unfold Vpolynomial; compute_degree
  have hd := natDegree_comp_le (p := nativeTermPolynomial p) (q := Vpolynomial)
  have hterm := nativeTermPolynomial_degree p (by omega)
  have hdiv := Nat.div_mul_le_self p 6
  have hhalf := WPFiniteWSource.half_exponent p hp
  change (nativeTermPullbackQ p).natDegree ≤
    (nativeTermPolynomial p).natDegree * Vpolynomial.natDegree at hd
  exact hd.trans ((Nat.mul_le_mul hterm hV).trans (by omega))

/-- An original rational polynomial model of the whole terminating delta source. -/
noncomputable def nativeDeltaQ (p : ℕ) : ℚ[X] :=
  Polynomial.C (1 / (p : ℚ)) *
    (nativeTermPullbackQ p - (nativeTermPullbackQ p).reflect ((p - 1) / 2))

theorem nativeDeltaQ_toLaurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeDeltaQ p).toLaurent = deltaTerm p := by
  have hV : (nativeTermPullbackQ p).toLaurent =
      substitute (nativeTermPolynomial p) Vx :=
    (substituteOver_toLaurent (nativeTermPolynomial p) Vpolynomial).symm
  have hQ : invert (substitute (nativeTermPolynomial p) Vx) =
      substitute (nativeTermPolynomial p) Qx := by
    change invert (substituteOver (nativeTermPolynomial p) Vx) =
      substituteOver (nativeTermPolynomial p) Qx
    rw [substituteOver_invert, actual_Vx_reciprocal]
  rw [nativeDeltaQ, map_mul, map_sub, Polynomial.toLaurent_C,
    WPActualHasseReciprocal.toLaurent_reflect _ _ (nativeTermPullbackQ_degree p hp), hV, hQ]
  rfl

theorem nativeDeltaQ_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeDeltaQ p).natDegree ≤ (p - 1) / 2 := by
  unfold nativeDeltaQ
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_sub_le _ _).trans (max_le (nativeTermPullbackQ_degree p hp)
      (natDegree_reflect_le.trans (max_le le_rfl (nativeTermPullbackQ_degree p hp)))))

noncomputable def nativeDeltaIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  liftOfLaurent p (nativeDeltaQ p) (by
    rw [nativeDeltaQ_toLaurent p hp]
    exact actual_deltaTerm_integral p (by omega))

theorem nativeDeltaIntegral_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeDeltaIntegral p hp).map (integralRationals p).subtype = nativeDeltaQ p :=
  liftOfLaurent_mapQ p _ _

noncomputable def actualDeltaField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[X] := (nativeDeltaIntegral p hp).map (residueHom p)

/-- The polynomial model is the residue of the original rational deltaTerm. -/
theorem actual_deltaTerm_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualDeltaField p hp).toLaurent =
      residueLaurent p ⟨deltaTerm p, actual_deltaTerm_integral p (by omega)⟩ := by
  rw [actualDeltaField, ← residue_polynomialLaurentModel]
  congr 1
  apply Subtype.ext
  rw [polynomialLaurentModel_val, nativeDeltaIntegral_rational,
    nativeDeltaQ_toLaurent p hp]

theorem actual_deltaTerm_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualDeltaField p hp).natDegree ≤ (p - 1) / 2 := by
  apply natDegree_map_le.trans
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  apply Subtype.ext
  change ((nativeDeltaIntegral p hp).coeff n : ℚ) = 0
  have hc := congrArg (fun P : ℚ[X] => P.coeff n) (nativeDeltaIntegral_rational p hp)
  rw [coeff_map, coeff_eq_zero_of_natDegree_lt
    ((nativeDeltaQ_degree p hp).trans_lt hn)] at hc
  exact hc

end LiteralDelta

section WholeTaylor
open WPActualNativeChiTaylor WPActualCentralNativeJet WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeJetODE WPActualChiSource
  WPFiniteLaurentIntegral WPActualEtaPole WPPIntegralReduction WPActualEtaIntegrality
  WPLaurentIntegralResidue NativeChiFieldSource WPHasseIntegralTransport
  ActualNormCrossAttachment NativeShiftedChi

noncomputable def nativeJetIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  ∑ n : Fin ((p - 1) / 2 + 1), Polynomial.monomial n.val
    (integralParameterJet p n.val (by omega) (by have := n.isLt; omega))

theorem nativeJetIntegral_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeJetIntegral p hp).map (integralRationals p).subtype = nativeJetPolynomial p := by
  have h7 : 7 ≤ p := by omega
  have hN : (p - 1) / 2 + 1 ≤ p := by omega
  have hc (n : Fin ((p - 1) / 2 + 1)) :
      (integralRationals p).subtype
        (integralParameterJet p n.val h7 (n.isLt.trans_le hN)) =
        parameterJet n.val (-(p : ℚ) / 6) :=
    integralParameterJet_value p n.val h7 (n.isLt.trans_le hN)
  simp only [nativeJetIntegral, Polynomial.map_sum, map_monomial, hc]
  exact Fin.sum_univ_eq_sum_range
    (fun n => Polynomial.monomial n (parameterJet n (-(p : ℚ) / 6))) ((p - 1) / 2 + 1)

theorem nativeJetIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeJetIntegral p hp).map (residueHom p) = nativeJetField p := by
  have h7 : 7 ≤ p := by omega
  have hN : (p - 1) / 2 + 1 ≤ p := by omega
  have hr (z : integralRationals p) : residueHom p z = (z.val : ZMod p) := rfl
  have hc (n : Fin ((p - 1) / 2 + 1)) :
      residueHom p (integralParameterJet p n.val h7 (n.isLt.trans_le hN)) =
        (parameterJet n.val (-(p : ℚ) / 6) : ZMod p) := by
    rw [hr]
    exact congrArg (fun q : ℚ => (q : ZMod p))
      (integralParameterJet_value p n.val h7 (n.isLt.trans_le hN))
  simp only [nativeJetIntegral, Polynomial.map_sum, map_monomial, hc]
  exact Fin.sum_univ_eq_sum_range
    (fun n => Polynomial.monomial n (parameterJet n (-(p : ℚ) / 6) : ZMod p))
    ((p - 1) / 2 + 1)

/-- Reduction preserves both complete pullbacks of the original finite native jet. -/
theorem actual_jetDifference_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueLaurent p ⟨jetDifference p, actual_jetDifference_integral p (by omega)⟩ =
      ((nativeJetField p).comp (fieldV p)).toLaurent -
        T (((p - 1) / 2 : ℕ) : ℤ) *
          invert ((nativeJetField p).comp (fieldV p)).toLaurent := by
  let J : (integralRationals p)[T;T⁻¹] :=
    ((nativeJetIntegral p hp).comp (integralV p (by omega))).toLaurent
  have hJQ : coefficientMap (integralRationals p).subtype J =
      substitute (nativeJetPolynomial p) Vx := by
    dsimp only [J]
    rw [coefficientMap_toLaurent, Polynomial.map_comp, nativeJetIntegral_rational,
      integralV_map_rational]
    exact (substituteOver_toLaurent _ _).symm
  have hJF : coefficientMap (residueHom p) J =
      ((nativeJetField p).comp (fieldV p)).toLaurent := by
    dsimp only [J]
    rw [coefficientMap_toLaurent, Polynomial.map_comp, nativeJetIntegral_field,
      integralV_map_field]
  have hLift : integralLift p ⟨jetDifference p, actual_jetDifference_integral p (by omega)⟩ =
      J - T (((p - 1) / 2 : ℕ) : ℤ) * invert J := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (integralRationals p).subtype (Subring.subtype_injective (integralRationals p))
    rw [integralLift_rational, map_sub, map_mul, coefficientMap_T,
      coefficientMap_invert, hJQ]
    change jetDifference p = substituteOver (nativeJetPolynomial p) Vx -
      T (((p - 1) / 2 : ℕ) : ℤ) * invert (substituteOver (nativeJetPolynomial p) Vx)
    rw [substituteOver_invert, actual_Vx_reciprocal]
    rfl
  change coefficientMap (residueHom p) (integralLift p _) = _
  rw [hLift, map_sub, map_mul, coefficientMap_T, coefficientMap_invert, hJF]

/-- The exact rational Taylor identity supplies the actual full Sigma difference. -/
theorem actual_chi_Sigma_Taylor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    halfChiField p hp = (actualDeltaField p hp).toLaurent +
      LaurentPolynomial.C (1 / 3 : ZMod p) *
        (((actualSigmaNative p hp).comp (fieldV p)).toLaurent -
          T (((p - 1) / 2 : ℕ) : ℤ) *
            invert ((actualSigmaNative p hp).comp (fieldV p)).toLaurent) := by
  let δ : integralLaurent p := ⟨deltaTerm p, actual_deltaTerm_integral p (by omega)⟩
  let J : integralLaurent p := ⟨jetDifference p, actual_jetDifference_integral p (by omega)⟩
  let s : integralRationals p := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by omega) (by omega)⟩
  let S : integralLaurent p := ⟨LaurentPolynomial.C s.val, integral_C p _ s.property⟩
  have herr : (halfChiIntegral p hp - δ - S * J).val = errorDifference p :=
    actual_chi_nativeTaylor_identity p
  have hzero : residueLaurent p (halfChiIntegral p hp - δ - S * J) = 0 := by
    have hk := actual_errorDifference_kernel p (by omega)
    rw [residueZero_iff] at hk
    ext j
    rw [residueLaurent_coeff]
    change (((halfChiIntegral p hp - δ - S * J).val.coeff j : ℚ) : ZMod p) = 0
    rw [herr]
    exact hk.2 j
  have hS : residueLaurent p S = LaurentPolynomial.C (1 / 6 : ZMod p) := by
    rw [show S = ⟨LaurentPolynomial.C s.val, integral_C p _ s.property⟩ from rfl,
      residueLaurent_C]
    congr 1
    change ((1 / 6 : ℚ) : ZMod p) = (1 / 6 : ZMod p)
    norm_num [Rat.cast_def]
  rw [map_sub, map_sub, map_mul, hS,
    show residueLaurent p δ = (actualDeltaField p hp).toLaurent from
      (actual_deltaTerm_attachment p hp).symm,
    show residueLaurent p J = _ from actual_jetDifference_attachment p hp,
    actual_jet_twice_Sigma p hp] at hzero
  simp only [Nat.cast_ofNat, mul_comp, ofNat_comp, map_mul, map_ofNat] at hzero
  change halfChiField p hp - (actualDeltaField p hp).toLaurent -
    LaurentPolynomial.C (1 / 6 : ZMod p) *
      (2 * ((actualSigmaNative p hp).comp (fieldV p)).toLaurent -
        T (((p - 1) / 2 : ℕ) : ℤ) *
          (2 * invert ((actualSigmaNative p hp).comp (fieldV p)).toLaurent)) = 0 at hzero
  have h6 : (6 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 6
    (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hs : (1 / 6 : ZMod p) * 2 = 1 / 3 := by
    field_simp [h6, h3]
    ring
  have hsC := congrArg (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) hs
  simp only [map_mul, map_ofNat] at hsC
  linear_combination hzero +
    (((actualSigmaNative p hp).comp (fieldV p)).toLaurent -
      T (((p - 1) / 2 : ℕ) : ℤ) *
        invert ((actualSigmaNative p hp).comp (fieldV p)).toLaurent) * hsC

end WholeTaylor



section ActualComparison
variable {K : Type*} [Field K]
open WPActualChiSource NativeChiFieldSource NativeShiftedChi ActualNormCrossAttachment
  ActualLowEuler WPPIntegralReduction WPLaurentIntegralResidue WPActualEtaIntegrality

private theorem weighted_difference_anti {R : Type*} [CommRing R]
    (N : ℕ) (c : R) (U : R[T;T⁻¹]) :
    LaurentPolynomial.C c * (U - T (N : ℤ) * invert U) + T (N : ℤ) *
      invert (LaurentPolynomial.C c * (U - T (N : ℤ) * invert U)) = 0 := by
  have ht : (T (N : ℤ) * T (-(N : ℤ)) : R[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  simp only [map_mul, map_sub, invert_C, invert_T, involutive_invert U]
  calc
    _ = LaurentPolynomial.C c * (U - (T (N : ℤ) * T (-(N : ℤ))) * U) := by ring
    _ = 0 := by rw [ht]; ring

private theorem residue_weighted_anti (p N : ℕ) [Fact p.Prime]
    (L : integralLaurent p) (hL : L.val + T (N : ℤ) * invert L.val = 0) :
    residueLaurent p L + T (N : ℤ) * invert (residueLaurent p L) = 0 := by
  have hi : integralLift p L + T (N : ℤ) * invert (integralLift p L) = 0 := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (integralRationals p).subtype (Subring.subtype_injective (integralRationals p))
    simpa only [map_add, map_mul, map_zero, coefficientMap_T,
      coefficientMap_invert, integralLift_rational] using hL
  have hf := congrArg (coefficientMap (residueHom p)) hi
  change coefficientMap (residueHom p) (integralLift p L) + T (N : ℤ) *
    invert (coefficientMap (residueHom p) (integralLift p L)) = 0
  simpa only [map_add, map_mul, map_zero, coefficientMap_T, coefficientMap_invert] using hf

noncomputable def actualDeltaK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] := (actualDeltaField p hp).map (ActualThreePhase.φ p)

noncomputable def actualAK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  ((actualLogMinusH p).comp (WPHasseIntegralTransport.fieldV p)).map (ActualThreePhase.φ p)

noncomputable def actualSigmaK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] :=
  ((actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p)).map (ActualThreePhase.φ p)

noncomputable def actualXiK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] :=
  ((actualNormXi p hp).comp (WPHasseIntegralTransport.fieldV p)).map (ActualThreePhase.φ p)

theorem actual_f_pullback_field_eq (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualF p).comp (WPHasseIntegralTransport.fieldV p) = halfPullbackField p hp := by
  rw [actualF_eq_native p hp, halfPullbackField_eq,
    WPActualNativeHasse.actual_full_native_field_cutoff p ((p - 1) / 2)
      (by omega) (by omega) (by omega)]

private theorem finite_LV_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteLVSource.LV p : (ZMod p)[X]).map (ActualThreePhase.φ (K := K) p) =
      (WPFiniteLVSource.LV p : K[X]) := by
  simp only [WPFiniteLVSource.LV, WPFiniteLVSource.evenSquared, WPFiniteLVSource.V,
    WPFiniteWSource.squaredCoordinate, WPFiniteNC122.q, Polynomial.map_add,
    Polynomial.map_C, map_intCast, Polynomial.map_intCast, Polynomial.map_comp, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_ofNat, Polynomial.map_sub, map_div₀, map_one, map_mul,
    map_ofNat, map_natCast, map_inv₀]

theorem actual_AK_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK (K := K) p) = WPFiniteLVSource.LV p -
      Polynomial.C ((ActualThreePhase.φ (K := K) p)
        (WPActualGaussBottom.fieldHarmonic p (p / 6))) := by
  rw [actualAK, actualLogMinusH, sub_comp, C_comp, actual_log_V_attachment p hp,
    Polynomial.map_sub, Polynomial.map_C, finite_LV_map]

/-- The entire native polynomial retains the full half cutoff through its cubic pullback. -/
theorem actual_AK_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK (K := K) p).natDegree ≤ 3 * ((p - 1) / 2) := by
  have hE : (WPFiniteLVSource.evenSquared p : K[X]).natDegree ≤ (p - 1) / 2 := by
    unfold WPFiniteLVSource.evenSquared
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).2
    calc
      _ ≤ (X ^ j : K[X]).natDegree := natDegree_C_mul_le _ _
      _ ≤ j := by simp
      _ ≤ (p - 1) / 2 := by omega
  have hV : (WPFiniteLVSource.V : K[X]).natDegree ≤ 3 := by
    unfold WPFiniteLVSource.V WPFiniteWSource.squaredCoordinate
    compute_degree
  rw [actual_AK_source p hp, WPFiniteLVSource.LV]
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · calc
        _ ≤ (WPFiniteLVSource.evenSquared p : K[X]).natDegree *
            (WPFiniteLVSource.V : K[X]).natDegree := natDegree_comp_le
        _ ≤ ((p - 1) / 2) * 3 := Nat.mul_le_mul hE hV
        _ = 3 * ((p - 1) / 2) := Nat.mul_comm _ _
  · simp

theorem actual_SigmaK_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    actualSigmaK (K := K) p hp = ActualThreePhase.fK (K := K) p hp * actualAK p -
      (4 * X ^ p - 11) * ActualThreePhase.CBK (K := K) p := by
  have hs : (actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p) =
      halfPullbackField p hp * (actualLogMinusH p).comp (WPHasseIntegralTransport.fieldV p) -
        (4 * X ^ p - 11) * ActualFirstGreen.CB p := by
    rw [actual_Sigma_V_source p hp, actualLogMinusH, sub_comp, C_comp,
      actual_log_V_attachment p hp, ← actual_f_pullback_field_eq p hp]
  have h := congrArg (fun P : (ZMod p)[X] => P.map (ActualThreePhase.φ (K := K) p)) hs
  simpa only [actualSigmaK, actualAK, ActualThreePhase.fK, ActualThreePhase.CBK,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_X] using h

theorem actual_XiK_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    actualXiK (K := K) p hp = 2 * actualAK p * actualSigmaK p hp -
      ActualThreePhase.fK p hp * actualAK p ^ 2 := by
  have hs : (actualNormXi p hp).comp (WPHasseIntegralTransport.fieldV p) =
      2 * (actualLogMinusH p).comp (WPHasseIntegralTransport.fieldV p) *
        (actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p) -
      halfPullbackField p hp * (actualLogMinusH p).comp (WPHasseIntegralTransport.fieldV p) ^ 2 := by
    rw [actual_Xi_native_source p hp, sub_comp, mul_comp, mul_comp, ofNat_comp,
      mul_comp, pow_comp, actual_f_pullback_field_eq p hp]
    norm_num only [Nat.cast_ofNat]
  have h := congrArg (fun P : (ZMod p)[X] => P.map (ActualThreePhase.φ (K := K) p)) hs
  simpa only [actualXiK, actualAK, actualSigmaK, ActualThreePhase.fK,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat] using h

theorem actual_chiK_Sigma_Taylor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualThreePhase.χK (K := K) p hp = (actualDeltaK (K := K) p hp).toLaurent +
      LaurentPolynomial.C (1 / 3 : K) *
        ((actualSigmaK (K := K) p hp).toLaurent -
          T (((p - 1) / 2 : ℕ) : ℤ) * invert (actualSigmaK (K := K) p hp).toLaurent) := by
  have h := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p))
    (actual_chi_Sigma_Taylor p hp)
  simpa only [ActualThreePhase.χK, actualDeltaK, actualSigmaK, map_add, map_mul,
    map_sub, coefficientMap_C, map_div₀, map_one, map_ofNat,
    coefficientMap_toLaurent, coefficientMap_T, coefficientMap_invert] using h

/-- A minimal source helper avoids importing the downstream root trace module. -/
theorem actual_chiK_SB72_anti (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualThreePhase.χK (K := K) p hp + T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (ActualThreePhase.χK (K := K) p hp) = 0 := by
  have hQ := WPActualChiSource.Fpull_reciprocal ((p - 1) / 2)
  have hr : (halfChiIntegral p hp).val + T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (halfChiIntegral p hp).val = 0 := by
    change WPActualEtaPole.chiX p ((p - 1) / 2) ((p - 1) / 2) +
      T (((p - 1) / 2 : ℕ) : ℤ) *
        invert (WPActualEtaPole.chiX p ((p - 1) / 2) ((p - 1) / 2)) = 0
    rw [WPActualEtaPole.chiX, ← hQ]
    exact weighted_difference_anti ((p - 1) / 2) (1 / (p : ℚ)) _
  have hs := residue_weighted_anti p ((p - 1) / 2) (halfChiIntegral p hp) hr
  have h := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p)) hs
  simpa only [ActualThreePhase.χK, halfChiField, map_add, map_mul, map_zero,
    coefficientMap_T, coefficientMap_invert] using h

theorem actual_fK_SB72_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualThreePhase.fK (K := K) p hp).toLaurent = T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (ActualThreePhase.fK (K := K) p hp).toLaurent := by
  have hr : (halfPullbackField p hp).toLaurent = T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (halfPullbackField p hp).toLaurent := by
    rw [← actual_f_pullback_field_eq p hp, actualF_eq_native p hp]
    exact WPActualHasseReciprocal.actual_native_Hasse_Laurent p (by omega)
  have h := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p)) hr
  simpa only [ActualThreePhase.fK, map_mul, coefficientMap_T,
    coefficientMap_invert, coefficientMap_toLaurent] using h

theorem actual_deltaK_anti (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualDeltaK (K := K) p hp).toLaurent + T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (actualDeltaK (K := K) p hp).toLaurent = 0 := by
  let L : integralLaurent p :=
    ⟨WPActualNativeChiTaylor.deltaTerm p,
      WPActualNativeChiTaylor.actual_deltaTerm_integral p (by omega)⟩
  have hr : L.val + T (((p - 1) / 2 : ℕ) : ℤ) * invert L.val = 0 := by
    have hQ : invert (WPFiniteLaurentIntegral.substitute
        (WPActualNativeChiTaylor.nativeTermPolynomial p) WPActualEtaPole.Vx) =
        WPFiniteLaurentIntegral.substitute
          (WPActualNativeChiTaylor.nativeTermPolynomial p) WPActualEtaPole.Qx := by
      change invert (substituteOver _ _) = substituteOver _ _
      rw [WPActualChiSource.substituteOver_invert,
        WPActualChiSource.actual_Vx_reciprocal]
    change WPActualNativeChiTaylor.deltaTerm p +
      T (((p - 1) / 2 : ℕ) : ℤ) *
        invert (WPActualNativeChiTaylor.deltaTerm p) = 0
    rw [WPActualNativeChiTaylor.deltaTerm, WPActualNativeChiTaylor.termDifference, ← hQ]
    exact weighted_difference_anti ((p - 1) / 2) (1 / (p : ℚ)) _
  have hs := residue_weighted_anti p ((p - 1) / 2) L hr
  rw [← actual_deltaTerm_attachment p hp] at hs
  have h := congrArg (coefficientMap (ActualThreePhase.φ (K := K) p)) hs
  simpa only [actualDeltaK, map_add, map_mul, map_zero,
    coefficientMap_T, coefficientMap_invert, coefficientMap_toLaurent] using h

theorem actual_fK_degree_half (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualThreePhase.fK (K := K) p hp).natDegree ≤ (p - 1) / 2 := by
  rw [ActualThreePhase.fK, ← actual_f_pullback_field_eq p hp]
  apply natDegree_map_le.trans
  have hV : (WPHasseIntegralTransport.fieldV p).natDegree ≤ 3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  exact ((natDegree_comp_le (p := actualF p)).trans
    (Nat.mul_le_mul (actualF_degree p hp) hV)).trans (by
      have := Nat.div_mul_le_self p 6
      have := WPFiniteWSource.half_exponent p hp
      omega)

/-- The actual CB carrier bound retains its whole proper polynomial. -/
theorem actual_CBK_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualThreePhase.CBK (K := K) p).natDegree ≤ p - 2 := by
  have h5 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h5
  have hB : (ConicCoefficients.B : K[X]).natDegree = 2 := by
    apply le_antisymm
    · unfold ConicCoefficients.B
      compute_degree
    · apply le_natDegree_of_ne_zero
      simpa [ConicCoefficients.B, coeff_one, coeff_X_pow, coeff_X] using h5
  have hd : ((ActualThreePhase.CBK (K := K) p).comp ConicCoefficients.B).natDegree ≤
      p + 6 * (p / 6) - 3 := by
    rw [ActualThreePhase.actual_CB_pullback p hp]
    apply natDegree_map_le.trans
    have hn : (WPActualRankTwoProper.properLegendreJacobi p).natDegree ≤ p / 6 - 1 := by
      have := WPActualRankTwoProper.properLegendreJacobi_degree p (by omega : 7 ≤ p)
      omega
    have hb := natDegree_mul_le_of_le
      (WPActualRankTwoComparison.actualLegendreJacobi_degree p) hn
    have hTc : (WPFiniteCubicLog.Tc : (ZMod p)[X]).natDegree ≤ 3 := by
      unfold WPFiniteCubicLog.Tc
      compute_degree
    have hc := (natDegree_comp_le
      (p := WPActualRankTwoLegendreField.actualLegendreJacobi p *
        WPActualRankTwoProper.properLegendreJacobi p)
      (q := WPFiniteCubicLog.Tc)).trans
        (Nat.mul_le_mul hb hTc)
    have hx : (Polynomial.C (1 / 5 : ZMod p) * X ^ p).natDegree ≤ p :=
      (natDegree_C_mul_le _ _).trans (by simp)
    change (Polynomial.C (1 / 5 : ZMod p) * X ^ p *
      (WPActualRankTwoLegendreField.actualLegendreJacobi p *
        WPActualRankTwoProper.properLegendreJacobi p).comp WPFiniteCubicLog.Tc).natDegree ≤ _
    exact (natDegree_mul_le_of_le hx hc).trans (by
      have := Nat.div_mul_le_self p 6
      omega)
  rw [natDegree_comp, hB] at hd
  have := Nat.div_mul_le_self p 6
  omega

theorem actual_deltaK_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualDeltaK (K := K) p hp).natDegree ≤ (p - 1) / 2 :=
  natDegree_map_le.trans (actual_deltaTerm_degree p hp)

private theorem actual_V_zero_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPHasseIntegralTransport.fieldV p).eval (1 / 4) = 0 ∧
      (WPHasseIntegralTransport.fieldV p).eval 4 = 0 := by
  have h4 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 4
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h4
  simp only [WPHasseIntegralTransport.fieldV, eval_mul, eval_C, eval_sub,
    eval_pow, eval_X, eval_one, eval_ofNat, mul_one_div_cancel h4,
    sub_self, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, zero_mul]
  constructor <;> trivial

private theorem actual_log_origin_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualLogNative p).eval 0 = 0 := by
  have h2 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2
  have hE : WPFiniteField.E p (1 : ZMod p) = -WPFiniteNC122.q p := by
    have h := (WPFiniteLoop.L_rational_ends (K := ZMod p) p hp).1
    have he := WPFiniteLoop.L_square_eq_twice_E (K := ZMod p) p hp 1
    rw [one_pow] at he
    rw [he] at h
    apply mul_left_cancel₀ h2
    simpa only [WPFiniteNC122.q, mul_neg, neg_mul] using h
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 1)
    (even_native_attachment p hp (WPFiniteKSource.LPsrc p)
      (WPFiniteNC122Residue.LPsrc_even p))
  simpa only [eval_comp, eval_sub, eval_one, eval_pow, eval_X,
    one_pow, sub_self, WPFiniteKSource.LPsrc_eval, WPFiniteNC122.L,
    hE, add_neg_cancel, actualLogNative] using he

private theorem actual_Sigma_origin_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSigmaNative p hp).eval 0 = 0 := by
  have h2 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 0)
    (actual_jet_twice_Sigma p hp)
  rw [WPActualNativeJetODE.nativeJetField_origin,
    eval_mul, eval_ofNat] at h
  exact ((mul_eq_zero.mp h.symm).resolve_left h2)

/-- These four values come from the original native log, jet and Taylor sources. -/
theorem actual_SB72_endpoint_data_ZMod (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualDeltaField p hp).eval (1 / 4) = WPFiniteNC122.q p ∧
      (actualDeltaField p hp).eval 4 = -WPFiniteNC122.q p ∧
      (ActualFirstGreen.CB p).eval (1 / 4) =
        WPActualGaussBottom.fieldHarmonic p (p / 6) / 10 ∧
      (ActualFirstGreen.CB p).eval 4 =
        -WPActualGaussBottom.fieldHarmonic p (p / 6) / 5 := by
  have h2 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 10
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2 h4 h5 h10
  obtain ⟨hVa, hVb⟩ := actual_V_zero_endpoints p hp
  have hlog := actual_log_origin_zero p hp
  have hSigma := actual_Sigma_origin_zero p hp
  have hLV := actual_log_V_attachment p hp
  have hLa : (WPFiniteLVSource.LV p : (ZMod p)[X]).eval (1 / 4) = 0 := by
    rw [← hLV, eval_comp, hVa, hlog]
  have hLb : (WPFiniteLVSource.LV p : (ZMod p)[X]).eval 4 = 0 := by
    rw [← hLV, eval_comp, hVb, hlog]
  have hFa : ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).eval (1 / 4) = 1 := by
    rw [eval_comp, hVa, ← coeff_zero_eq_eval_zero, actualF_origin p hp]
  have hFb : ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).eval 4 = 1 := by
    rw [eval_comp, hVb, ← coeff_zero_eq_eval_zero, actualF_origin p hp]
  have hSa : ((actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p)).eval
      (1 / 4) = 0 := by rw [eval_comp, hVa, hSigma]
  have hSb : ((actualSigmaNative p hp).comp (WPHasseIntegralTransport.fieldV p)).eval
      4 = 0 := by rw [eval_comp, hVb, hSigma]
  have hca := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 4))
    (actual_Sigma_V_source p hp)
  have hcb := congrArg (fun P : (ZMod p)[X] => P.eval 4)
    (actual_Sigma_V_source p hp)
  have hqp : (1 / 4 : ZMod p) ^ p = 1 / 4 := by
    rw [div_pow, one_pow, ZMod.pow_card]
  simp only [hSa, eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow, eval_X,
    hFa, hLa, hqp, one_mul, zero_sub, mul_one_div_cancel h4] at hca
  simp only [hSb, eval_sub, eval_mul, eval_C, eval_ofNat, eval_pow, eval_X,
    hFb, hLb, ZMod.pow_card, one_mul, zero_sub] at hcb
  have hCBa : (ActualFirstGreen.CB p).eval (1 / 4) =
      WPActualGaussBottom.fieldHarmonic p (p / 6) / 10 := by
    apply (eq_div_iff h10).mpr
    linear_combination -hca
  have hCBb : (ActualFirstGreen.CB p).eval 4 =
      -WPActualGaussBottom.fieldHarmonic p (p / 6) / 5 := by
    apply (eq_div_iff h5).mpr
    linear_combination hcb
  let v := ActualChiEndpoints.fourUnit (K := ZMod p) p hp
  have hv : (v : ZMod p) = 4 := rfl
  have hvi : ((v⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 / 4 := by
    rw [Units.val_inv_eq_inv_val, hv]
    exact (one_div (4 : ZMod p)).symm
  have hχ := ActualChiEndpoints.actual_chi_field_endpoints p hp
  have hTa := congrArg (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) v⁻¹)
    (actual_chi_Sigma_Taylor p hp)
  have hTb := congrArg (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) v)
    (actual_chi_Sigma_Taylor p hp)
  have hχa : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) v⁻¹
      (halfChiField p hp) = WPFiniteNC122.q p := hχ.2
  have hχb : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) v
      (halfChiField p hp) = -WPFiniteNC122.q p := hχ.1
  rw [hχa] at hTa
  rw [hχb] at hTb
  simp only [map_add, map_mul, map_sub, LaurentPolynomial.eval₂_C, RingHom.id_apply,
    WPFiniteJWeightedResidue.inversion_eval, eval₂_toLaurent, Polynomial.eval₂_id,
    inv_inv, hvi, hv, hSa, hSb,
    mul_zero, sub_zero, add_zero] at hTa
  simp only [map_add, map_mul, map_sub, LaurentPolynomial.eval₂_C, RingHom.id_apply,
    WPFiniteJWeightedResidue.inversion_eval, eval₂_toLaurent, Polynomial.eval₂_id,
    hvi, hv, hSa, hSb,
    mul_zero, sub_zero, add_zero] at hTb
  exact ⟨hTa.symm, hTb.symm, hCBa, hCBb⟩

theorem actual_SB72_endpoint_data (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualDeltaK (K := K) p hp).eval (1 / 4) = WPFiniteNC122.q p ∧
      (actualDeltaK (K := K) p hp).eval 4 = -WPFiniteNC122.q p ∧
      (ActualThreePhase.CBK (K := K) p).eval (1 / 4) = WPFiniteNC122.h p / 10 ∧
      (ActualThreePhase.CBK (K := K) p).eval 4 = -WPFiniteNC122.h p / 5 := by
  obtain ⟨hδa, hδb, hCa, hCb⟩ := actual_SB72_endpoint_data_ZMod p hp
  rw [actual_harmonic_is_finite_h p hp] at hCa hCb
  have hev (P : (ZMod p)[X]) (z : ZMod p) :
      (P.map (ActualThreePhase.φ (K := K) p)).eval (ActualThreePhase.φ p z) =
        ActualThreePhase.φ p (P.eval z) := by rw [eval_map, eval₂_at_apply]
  have hq : ActualThreePhase.φ (K := K) p (WPFiniteNC122.q p) = WPFiniteNC122.q p := by
    simp only [WPFiniteNC122.q, map_intCast]
  have hh : ActualThreePhase.φ (K := K) p (WPFiniteNC122.h p) = WPFiniteNC122.h p := by
    simp only [WPFiniteNC122.h, WPFiniteNC122.q, map_sub, map_neg,
      map_mul, map_div₀, map_ofNat, map_intCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [actualDeltaK, map_div₀, map_one, map_ofNat, hδa, hq] using
      hev (actualDeltaField p hp) (1 / 4)
  · simpa only [actualDeltaK, map_ofNat, hδb, map_neg, hq] using
      hev (actualDeltaField p hp) 4
  · simpa only [ActualThreePhase.CBK, map_div₀, map_one, map_ofNat, hCa, hh] using
      hev (ActualFirstGreen.CB p) (1 / 4)
  · simpa only [ActualThreePhase.CBK, map_ofNat, hCb, map_div₀, map_neg, hh] using
      hev (ActualFirstGreen.CB p) 4

private theorem zeta_phase (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ActualChiEndpoints.zeta (K := K) p =
      LaurentPolynomial.C (1 / 3 : K) * WPFiniteZSource.phase p := by
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  rw [ActualChiEndpoints.zeta, WPFiniteZSource.phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1 / 3 : K) * WPFiniteZSource.phase p * ht

private theorem zeta_invert (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (ActualChiEndpoints.zeta (K := K) p) = ActualChiEndpoints.zeta p := by
  rw [zeta_phase p hp]
  simp only [WPFiniteZSource.phase, map_mul, map_sub, map_ofNat, invert_C,
    invert_T, neg_neg]
  ring

noncomputable def SB72Numerator (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  2 * T (p : ℤ) * (3 - 2 * T (p : ℤ)) * WPFiniteZSource.P p u +
    (4 - 11 * T (p : ℤ)) * invert (WPFiniteZSource.P p u) -
    LaurentPolynomial.C (1 / 3 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent ^ p *
      ((actualAK (K := K) p).toLaurent - invert (actualAK (K := K) p).toLaurent)

/-- Actual Taylor and anti-reciprocity give the original cleared SB72 numerator. -/
theorem actual_SB72_cleared (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ p *
      ((actualDeltaK (K := K) p hp).toLaurent +
        LaurentPolynomial.C (5 / 3 : K) * (ActualThreePhase.CBK (K := K) p).toLaurent) =
      (ActualThreePhase.fK (K := K) p hp).toLaurent * SB72Numerator p u := by
  let N : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  let f := (ActualThreePhase.fK (K := K) p hp).toLaurent
  let A := (actualAK (K := K) p).toLaurent
  let B := (ActualThreePhase.CBK (K := K) p).toLaurent
  let Bv := T N * invert B
  let P := WPFiniteZSource.P (K := K) p u
  let Xp : K[T;T⁻¹] := T (p : ℤ)
  let Xm : K[T;T⁻¹] := T (-(p : ℤ))
  let q : K[T;T⁻¹] := LaurentPolynomial.C (1 / 3 : K)
  let ph : K[T;T⁻¹] := 4 * Xm - 11
  have ht : Xp * Xm = 1 := by
    dsimp only [Xp, Xm]
    rw [← T_add, add_neg_cancel, T_zero]
  have hG : (WPFiniteZSource.Abar : K[X]).toLaurent ^ p =
      Xp * (17 - 4 * Xp - 4 * Xm) := WPFiniteZSource.phase_factorization p hp
  have hz : ActualChiEndpoints.zeta (K := K) p = q * (17 - 4 * Xp - 4 * Xm) :=
    zeta_phase p hp
  have hs : (actualSigmaK (K := K) p hp).toLaurent = f * A - (4 * Xp - 11) * B := by
    rw [actual_SigmaK_source p hp]
    simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.toLaurent_X, T_pow, mul_one]
    rfl
  have hsref : T N * invert (actualSigmaK (K := K) p hp).toLaurent =
      f * invert A - ph * Bv := by
    rw [hs]
    dsimp only [Xp]
    simp only [map_sub, map_mul, map_ofNat, invert_T]
    have hf : T N * invert f = f := (actual_fK_SB72_reflection p hp).symm
    dsimp only [Bv, ph, Xm]
    linear_combination invert A * hf
  have hc := ActualGreenResidue.actual_chi_finite_P (K := K) p hp u hu
  change ActualThreePhase.χK p hp = f * P + ActualChiEndpoints.zeta p * B at hc
  have hcref : T N * invert (ActualThreePhase.χK (K := K) p hp) =
      f * invert P + ActualChiEndpoints.zeta p * Bv := by
    rw [hc]
    simp only [map_add, map_mul, zeta_invert p hp]
    have hf : T N * invert f = f := (actual_fK_SB72_reflection p hp).symm
    dsimp only [Bv]
    linear_combination invert P * hf
  have ha := actual_chiK_SB72_anti (K := K) p hp
  change ActualThreePhase.χK p hp + T N * invert (ActualThreePhase.χK p hp) = 0 at ha
  rw [hcref, hc, hz] at ha
  have hT := actual_chiK_Sigma_Taylor (K := K) p hp
  change ActualThreePhase.χK p hp = (actualDeltaK p hp).toLaurent +
    q * ((actualSigmaK p hp).toLaurent - T N * invert (actualSigmaK p hp).toLaurent) at hT
  rw [hsref, hs, hc, hz] at hT
  have h5 : LaurentPolynomial.C (5 / 3 : K) = 5 * q := by
    dsimp only [q]
    simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  have hδ : (actualDeltaK (K := K) p hp).toLaurent + 5 * q * B =
      f * (P - q * (A - invert A)) - q * ph * (B + Bv) := by
    dsimp only [ph]
    linear_combination -hT
  change _ = f * _
  rw [h5, hδ, hG]
  dsimp only [SB72Numerator]
  rw [hG]
  change Xp * (17 - 4 * Xp - 4 * Xm) *
    (f * (P - q * (A - invert A)) - q * ph * (B + Bv)) =
      f * (2 * Xp * (3 - 2 * Xp) * P + (4 - 11 * Xp) * invert P -
        q * (Xp * (17 - 4 * Xp - 4 * Xm)) * (A - invert A))
  dsimp only [ph]
  linear_combination -Xp * (4 * Xm - 11) * ha + 4 * f * invert P * ht

private theorem SB72_R_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (T (-2) : K[T;T⁻¹]) * invert (WPFiniteZSource.R p) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * WPFiniteZSource.R p := by
  have ht : (T (-2) : K[T;T⁻¹]) * T (p : ℤ) * T (-2) ^ (p - 1) *
      T (-1) ^ ((p - 1) / 2) = T (-(((p - 1) / 2 : ℕ) : ℤ)) * T (-(p : ℤ)) := by
    simp only [T_pow, ← T_add]
    congr 1
    have := WPFiniteWSource.half_exponent p hp
    omega
  simp only [WPFiniteZSource.R, map_mul, map_pow, invert_C, invert_T,
    neg_neg, WPFiniteZSource.invert_Abar,
    WPFiniteZSource.invert_squaredCoordinate, mul_pow]
  linear_combination LaurentPolynomial.C (1 / 2 : K) *
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ (p - 1) *
    (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) * ht

private theorem SB72_invert_P_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    D (invert (WPFiniteZSource.P p u)) =
      -T (-(((p - 1) / 2 : ℕ) : ℤ)) * WPFiniteZSource.R p +
        LaurentPolynomial.C (1 / 2 : K) * T (-1) := by
  have ht : (T (-2) : K[T;T⁻¹]) * T 1 = T (-1) := by
    rw [← T_add]
    norm_num
  rw [D_invert, WPFiniteZSource.P_derivative p hp u]
  simp only [map_sub, map_mul, invert_C, invert_T, neg_neg]
  linear_combination -SB72_R_reflection (K := K) p hp +
    LaurentPolynomial.C (1 / 2 : K) * ht

theorem actual_AK_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (actualAK (K := K) p).toLaurent =
      LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T 1 - 11) -
          (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) *
            (4 * T (p : ℤ) - 11)) := by
  rw [D_toLaurent, actual_AK_source p hp, derivative_sub, derivative_C, sub_zero]
  have h := congrArg (fun P : K[X] => P.toLaurent)
    (WPFiniteLVSource.LV_cleared_source (K := K) p hp)
  simpa only [WPFiniteZSource.Abar, map_mul, map_sub, map_pow, map_ofNat,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, T_pow, mul_one] using h

theorem actual_AQ_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert (actualAK (K := K) p).toLaurent) =
      -LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T (-1) - 11) -
          T (-(((p - 1) / 2 : ℕ) : ℤ)) *
            (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2) *
              (4 * T (-(p : ℤ)) - 11)) := by
  have h := congrArg invert (actual_AK_cleared_derivative (K := K) p hp)
  simp only [map_mul, map_sub, map_ofNat, invert_C, invert_T,
    WPFiniteZSource.invert_Abar, WPFiniteZSource.invert_squared_power] at h
  rw [D_invert]
  linear_combination -h

/-- The whole cleared numerator has precisely the finite Dstar derivative. -/
theorem SB72Numerator_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (SB72Numerator (K := K) p u) =
      (WPFiniteZSource.Abar : K[X]).toLaurent ^ p * LaurentPolynomial.C (5 / 2 : K) *
        (1 - (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2)) := by
  let g := (WPFiniteZSource.Abar : K[X]).toLaurent
  let G := g ^ p
  let Xp : K[T;T⁻¹] := T (p : ℤ)
  let Xm : K[T;T⁻¹] := T (-(p : ℤ))
  let x : K[T;T⁻¹] := T 1
  let xm : K[T;T⁻¹] := T (-1)
  let Nm : K[T;T⁻¹] := T (-(((p - 1) / 2 : ℕ) : ℤ))
  let S := (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ^ ((p - 1) / 2)
  let phase := 17 - 4 * Xp - 4 * Xm
  let q2 : K[T;T⁻¹] := LaurentPolynomial.C (1 / 2 : K)
  let q3 : K[T;T⁻¹] := LaurentPolynomial.C (1 / 3 : K)
  let A := (actualAK (K := K) p).toLaurent
  let P := WPFiniteZSource.P (K := K) p u
  let c0 := 2 * Xp * (3 - 2 * Xp)
  let c1 := 4 - 11 * Xp
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3
  have h32 : q3 * LaurentPolynomial.C (3 / 2 : K) = q2 := by
    dsimp only [q3, q2]
    rw [← map_mul]
    congr 1
    field_simp [h3]
  have h52 : LaurentPolynomial.C (5 / 2 : K) = 5 * q2 := by
    dsimp only [q2]
    simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  have ht : Xp * Xm = 1 := by
    dsimp only [Xp, Xm]
    rw [← T_add, add_neg_cancel, T_zero]
  have ht1 : x * xm = 1 := by
    dsimp only [x, xm]
    rw [← T_add]
    norm_num
  have hG : G = Xp * phase := WPFiniteZSource.phase_factorization p hp
  have hg : g * xm = 17 - 4 * x - 4 * xm := by
    dsimp only [g, xm, x, WPFiniteZSource.Abar]
    simp only [map_mul, map_sub, map_ofNat, map_one, Polynomial.toLaurent_X]
    linear_combination (17 - 4 * T 1) * ht1
  have hDX : D Xp = 0 := by
    have h1 : D (1 : K[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : K)
    simpa only [mul_one, h1, mul_zero] using
      D_frobenius_shift p (1 : K[T;T⁻¹]) (p : ℤ) (dvd_refl _)
  have hDG : D G = 0 := by
    dsimp only [G, g]
    rw [← map_pow, D_toLaurent]
    simp [derivative_pow]
  have hDP : D P = WPFiniteZSource.R p - q2 * xm := WPFiniteZSource.P_derivative p hp u
  have hDPv : D (invert P) = -Nm * WPFiniteZSource.R p + q2 * xm :=
    SB72_invert_P_derivative p hp u
  have hN : D (SB72Numerator (K := K) p u) =
      c0 * D P + c1 * D (invert P) - q3 * G * (D A - D (invert A)) := by
    have hD2 : D (2 : K[T;T⁻¹]) = 0 := D_C (2 : K)
    have hD3 : D (3 : K[T;T⁻¹]) = 0 := D_C (3 : K)
    have hD4 : D (4 : K[T;T⁻¹]) = 0 := D_C (4 : K)
    have hD11 : D (11 : K[T;T⁻¹]) = 0 := D_C (11 : K)
    dsimp only [SB72Numerator, c0, c1, Xp, G, g, q3, A, P] at *
    simp only [map_sub, map_add, D_mul, D_C, hDX, hDG, hD2, hD3, hD4, hD11,
      zero_mul, zero_add, mul_zero, add_zero, sub_self]
  have hR : g * WPFiniteZSource.R p = q2 * phase * S := WPFiniteZSource.R_cleared p hp
  have hA : g * D A = LaurentPolynomial.C (3 / 2 : K) *
      ((4 * x - 11) - S * (4 * Xp - 11)) := actual_AK_cleared_derivative p hp
  have hAQ : g * D (invert A) = -LaurentPolynomial.C (3 / 2 : K) *
      ((4 * xm - 11) - Nm * S * (4 * Xm - 11)) := actual_AQ_cleared_derivative p hp
  change g * D (SB72Numerator p u) = G * LaurentPolynomial.C (5 / 2 : K) * (1 - S)
  calc
    _ = c0 * (g * WPFiniteZSource.R p) - c0 * q2 * (g * xm) -
        c1 * Nm * (g * WPFiniteZSource.R p) + c1 * q2 * (g * xm) -
        q3 * G * (g * D A) + q3 * G * (g * D (invert A)) := by
      rw [hN, hDP, hDPv]
      ring
    _ = c0 * q2 * phase * S - c0 * q2 * (17 - 4 * x - 4 * xm) -
        c1 * Nm * q2 * phase * S + c1 * q2 * (17 - 4 * x - 4 * xm) -
        G * (q3 * LaurentPolynomial.C (3 / 2 : K)) *
          ((4 * x - 11) - S * (4 * Xp - 11)) -
        G * (q3 * LaurentPolynomial.C (3 / 2 : K)) *
          ((4 * xm - 11) - Nm * S * (4 * Xm - 11)) := by
      rw [hR, hg, hA, hAQ]
      ring
    _ = _ := by
      rw [h32, hG, h52]
      dsimp only [c0, c1, phase]
      linear_combination 4 * q2 *
        ((17 - 4 * Xp - 4 * Xm) * Nm * S - (17 - 4 * x - 4 * xm)) * ht

theorem SB72Numerator_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    D (SB72Numerator (K := K) p u) =
      (WPFiniteZSource.Abar : K[X]).toLaurent ^ p * D (Dstar p : K[X]).toLaurent := by
  apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := K) p hp)
  rw [SB72Numerator_cleared_derivative p hp]
  have h := congrArg (fun P : K[X] => P.toLaurent) (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_one, map_pow, Polynomial.toLaurent_C,
    ← D_toLaurent] at h
  linear_combination -(WPFiniteZSource.Abar : K[X]).toLaurent ^ p * h

noncomputable def actualSB72Error (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] :=
  actualDeltaK p hp + Polynomial.C (5 / 3 : K) * ActualThreePhase.CBK p -
    ActualThreePhase.fK p hp * Dstar p

set_option maxHeartbeats 6400000 in
theorem actual_SB72_error_Wronskian (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    ActualThreePhase.fK p hp * (actualSB72Error (K := K) p hp).derivative -
      (ActualThreePhase.fK p hp).derivative * actualSB72Error p hp = 0 := by
  let G := (WPFiniteZSource.Abar : K[X]).toLaurent ^ p
  let f := ActualThreePhase.fK (K := K) p hp
  let E1 := actualDeltaK (K := K) p hp +
    Polynomial.C (5 / 3 : K) * ActualThreePhase.CBK p
  have hE : actualSB72Error (K := K) p hp = E1 - f * Dstar p := rfl
  have hc : G * E1.toLaurent = f.toLaurent * SB72Numerator p u := by
    simpa only [E1, map_add, map_mul, Polynomial.toLaurent_C] using
      actual_SB72_cleared (K := K) p hp u hu
  have hDG : D G = 0 := by
    dsimp only [G]
    rw [← map_pow, D_toLaurent]
    simp [derivative_pow]
  have hd := congrArg D hc
  rw [D_mul, hDG, zero_mul, zero_add, D_toLaurent, D_mul,
    D_toLaurent, SB72Numerator_derivative p hp u, D_toLaurent] at hd
  have hz : G *
      (f * (actualSB72Error (K := K) p hp).derivative -
        f.derivative * actualSB72Error p hp).toLaurent = 0 := by
    rw [hE]
    simp only [derivative_mul, map_sub, map_mul, map_add]
    linear_combination f.toLaurent * hd - f.derivative.toLaurent * hc
  have hG : G ≠ 0 := pow_ne_zero p (WPFiniteZSource.Abar_nonzero (K := K) p hp)
  have hzero := (mul_eq_zero.mp hz).resolve_left hG
  apply Polynomial.toLaurent_injective
  simpa only [map_zero] using hzero

theorem actual_SB72_error_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualSB72Error (K := K) p hp).natDegree ≤ p - 2 := by
  have hN := WPFiniteWSource.half_exponent p hp
  have hδ := actual_deltaK_degree (K := K) p hp
  have hCB := actual_CBK_degree (K := K) p hp
  have hf := actual_fK_degree_half (K := K) p hp
  have hD := Dstar_degree (K := K) p hp
  unfold actualSB72Error
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_add_le _ _).trans
      (max_le (hδ.trans (by omega)) ((natDegree_C_mul_le _ _).trans hCB))
  · exact (natDegree_mul_le_of_le hf hD).trans (by omega)

private theorem actual_SB72_error_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (actualSB72Error (K := K) p hp).eval (1 / 4) = 0 := by
  obtain ⟨hδ, _, hCB, _⟩ := actual_SB72_endpoint_data (K := K) p hp
  have hf := (ActualGreenResidue.actual_native_pullback_facts (K := K) p hp).2.1
  have hD := (Dstar_endpoints (K := K) p hp).1
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 := WPFiniteField.denominator_ne_zero (K := K) p 6
    (Finset.mem_Ico.mpr (by omega))
  have h10 := WPFiniteField.denominator_ne_zero (K := K) p 10
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3 h6 h10
  simp only [actualSB72Error, eval_sub, eval_add, eval_mul, eval_C,
    hδ, hCB, hf, hD, one_mul]
  field_simp [h3, h6, h10]
  ring

theorem actual_SB72_error_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) : actualSB72Error (K := K) p hp = 0 := by
  obtain ⟨hfd, hfa, _, _, _⟩ := ActualGreenResidue.actual_native_pullback_facts (K := K) p hp
  have hf : ActualThreePhase.fK (K := K) p hp ≠ 0 := by
    intro hz
    rw [hz, eval_zero] at hfa
    exact zero_ne_one hfa
  exact flat_small_degree_endpoint_zero p (actualSB72Error p hp)
    (ActualThreePhase.fK p hp) hf ((actual_SB72_error_degree p hp).trans_lt (by omega))
    hfd (actual_SB72_error_Wronskian p hp u hu) (1 / 4)
    (actual_SB72_error_endpoint p hp) hfa

/-- The original actual delta polynomial has the retained SB72 primitive. -/
theorem actual_SB72 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    actualDeltaK (K := K) p hp = ActualThreePhase.fK p hp * Dstar p -
      Polynomial.C (5 / 3 : K) * ActualThreePhase.CBK p := by
  have h := actual_SB72_error_zero (K := K) p hp u hu
  unfold actualSB72Error at h
  linear_combination h

theorem actual_SB72_closed (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (hp : 19 ≤ p) :
    actualDeltaK (K := K) p hp = ActualThreePhase.fK p hp * Dstar p -
      Polynomial.C (5 / 3 : K) * ActualThreePhase.CBK p := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (1 / 5 : K) (by norm_num : 0 < (2 : ℕ))
  exact actual_SB72 p hp u hu

private theorem Dstar_map {L : Type*} [Field L] (p : ℕ) (φ : K →+* L) :
    (Dstar p : K[X]).map φ = (Dstar p : L[X]) := by
  simp only [Dstar, WPFiniteWSource.deltaE, WPFiniteWSource.squaredCoordinate,
    Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_div₀, map_sub, map_one, map_ofNat, map_natCast,
    map_pow, map_mul, map_inv₀]

theorem actual_SB72_ZMod (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualDeltaField p hp = halfPullbackField p hp * (Dstar p : (ZMod p)[X]) -
      Polynomial.C (5 / 3 : ZMod p) * ActualFirstGreen.CB p := by
  let K := AlgebraicClosure (ZMod p)
  let φ : ZMod p →+* K := ActualThreePhase.φ p
  apply Polynomial.map_injective φ φ.injective
  have h := actual_SB72_closed (K := K) p hp
  simpa only [actualDeltaK, ActualThreePhase.fK, ActualThreePhase.CBK,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Dstar_map,
    map_div₀, map_ofNat] using h

/-- This is SB72 for the residue of the original rational deltaTerm itself. -/
theorem actual_deltaTerm_residue_SB72 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueLaurent p ⟨WPActualNativeChiTaylor.deltaTerm p,
      WPActualNativeChiTaylor.actual_deltaTerm_integral p (by omega)⟩ =
      (halfPullbackField p hp).toLaurent * (Dstar p : (ZMod p)[X]).toLaurent -
        LaurentPolynomial.C (5 / 3 : ZMod p) * (ActualFirstGreen.CB p).toLaurent := by
  rw [← actual_deltaTerm_attachment p hp, actual_SB72_ZMod p hp]
  simp only [map_sub, map_mul, Polynomial.toLaurent_C]

noncomputable def actualZ52 (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[T;T⁻¹] :=
  ((actualAK (K := K) p).toLaurent - invert (actualAK (K := K) p).toLaurent) ^ 2 +
    6 * invert (actualAK (K := K) p).toLaurent *
      (WPFiniteZSource.P p u - (Dstar p : K[X]).toLaurent)

noncomputable def actualR52 (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  -(4 * T (-(p : ℤ)) - 11) * invert (actualAK (K := K) p).toLaurent -
    (4 * T (p : ℤ) - 11) * (actualAK (K := K) p).toLaurent

private theorem actual_reflected_Sigma_SB72 (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    T (((p - 1) / 2 : ℕ) : ℤ) * invert (actualSigmaK (K := K) p hp).toLaurent =
      (ActualThreePhase.fK (K := K) p hp).toLaurent *
        ((actualAK (K := K) p).toLaurent - 3 * WPFiniteZSource.P p u +
          3 * (Dstar p : K[X]).toLaurent) +
        (4 * T (-(p : ℤ)) - 11) * (ActualThreePhase.CBK (K := K) p).toLaurent := by
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3
  have hq : (3 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 3 : K) = 1 := by
    change LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 3 : K) = 1
    rw [← map_mul, mul_one_div_cancel h3, map_one]
  have hq5 : (3 : K[T;T⁻¹]) * LaurentPolynomial.C (5 / 3 : K) = 5 := by
    change LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (5 / 3 : K) =
      LaurentPolynomial.C (5 : K)
    rw [← map_mul]
    congr 1
    field_simp [h3]
  have hT := congrArg (fun L : K[T;T⁻¹] => 3 * L)
    (actual_chiK_Sigma_Taylor (K := K) p hp)
  rw [mul_add, ← mul_assoc, hq, one_mul] at hT
  rw [ActualGreenResidue.actual_chi_finite_P p hp u hu, zeta_phase p hp,
    actual_SB72 p hp u hu] at hT
  have hs := congrArg (fun P : K[X] => P.toLaurent) (actual_SigmaK_source (K := K) p hp)
  simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one, WPFiniteZSource.phase] at hT hs
  linear_combination hT + hs -
    (ActualThreePhase.CBK (K := K) p).toLaurent * hq5 -
    (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) *
      (ActualThreePhase.CBK (K := K) p).toLaurent * hq

/-- The complete reciprocal Xi difference keeps every Frobenius phase and CB term. -/
theorem actual_DeltaXi (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (actualXiK (K := K) p hp).toLaurent - T (((p - 1) / 2 : ℕ) : ℤ) *
      invert (actualXiK (K := K) p hp).toLaurent =
      (ActualThreePhase.fK (K := K) p hp).toLaurent * actualZ52 p u +
        2 * (ActualThreePhase.CBK (K := K) p).toLaurent * actualR52 p := by
  let N : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  let f := (ActualThreePhase.fK (K := K) p hp).toLaurent
  let A := (actualAK (K := K) p).toLaurent
  let S := (actualSigmaK (K := K) p hp).toLaurent
  have hXi : (actualXiK (K := K) p hp).toLaurent = 2 * A * S - f * A ^ 2 := by
    rw [actual_XiK_source p hp]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    rfl
  have hXiv : T N * invert (actualXiK (K := K) p hp).toLaurent =
      2 * invert A * (T N * invert S) - f * invert A ^ 2 := by
    rw [hXi]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    have hf : T N * invert f = f := (actual_fK_SB72_reflection p hp).symm
    linear_combination -invert A ^ 2 * hf
  change _ - T N * invert _ = _
  rw [hXiv, hXi]
  dsimp only [S]
  rw [actual_reflected_Sigma_SB72 p hp u hu, actual_SigmaK_source p hp]
  simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.toLaurent_X, T_pow, mul_one]
  dsimp only [actualZ52, actualR52, A, f]
  ring

theorem actual_Dstar_reciprocal_sum (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (ActualThreePhase.fK (K := K) p hp).toLaurent *
      ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent) =
      LaurentPolynomial.C (5 / 3 : K) *
        ((ActualThreePhase.CBK (K := K) p).toLaurent +
          T (((p - 1) / 2 : ℕ) : ℤ) * invert (ActualThreePhase.CBK (K := K) p).toLaurent) := by
  have hδ := actual_deltaK_anti (K := K) p hp
  rw [actual_SB72 p hp u hu] at hδ
  simp only [map_sub, map_mul, Polynomial.toLaurent_C, invert_C] at hδ
  have hf := actual_fK_SB72_reflection (K := K) p hp
  linear_combination hδ + invert (Dstar p : K[X]).toLaurent * hf

theorem actual_P_minus_Dstar (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteZSource.P (K := K) p u - (Dstar p : K[X]).toLaurent =
      LaurentPolynomial.C (1 / 3 : K) *
        ((actualAK (K := K) p).toLaurent - invert (actualAK (K := K) p).toLaurent) +
      LaurentPolynomial.C (1 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
        ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent) := by
  let N : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  let f := (ActualThreePhase.fK (K := K) p hp).toLaurent
  let A := (actualAK (K := K) p).toLaurent
  let B := (ActualThreePhase.CBK (K := K) p).toLaurent
  let Bv := T N * invert B
  let ph : K[T;T⁻¹] := 4 * T (-(p : ℤ)) - 11
  let d := (Dstar p : K[X]).toLaurent
  let q3 : K[T;T⁻¹] := LaurentPolynomial.C (1 / 3 : K)
  let q5 : K[T;T⁻¹] := LaurentPolynomial.C (1 / 5 : K)
  have h5 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h5
  have hq : q5 * LaurentPolynomial.C (5 / 3 : K) = q3 := by
    dsimp only [q5, q3]
    rw [← map_mul]
    congr 1
    field_simp [h5]
  have hs : (actualSigmaK (K := K) p hp).toLaurent =
      f * A - (4 * T (p : ℤ) - 11) * B := by
    rw [actual_SigmaK_source p hp]
    simp only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.toLaurent_X, T_pow, mul_one]
    rfl
  have hsref : T N * invert (actualSigmaK (K := K) p hp).toLaurent =
      f * invert A - ph * Bv := by
    rw [hs]
    simp only [map_sub, map_mul, map_ofNat, invert_T]
    have hf : T N * invert f = f := (actual_fK_SB72_reflection p hp).symm
    dsimp only [Bv, ph]
    linear_combination invert A * hf
  have hT := actual_chiK_Sigma_Taylor (K := K) p hp
  rw [ActualGreenResidue.actual_chi_finite_P p hp u hu, zeta_phase p hp,
    actual_SB72 p hp u hu] at hT
  simp only [map_sub, map_mul, Polynomial.toLaurent_C] at hT
  rw [hsref, hs] at hT
  have hDsum := actual_Dstar_reciprocal_sum (K := K) p hp u hu
  change f * (d + invert d) = LaurentPolynomial.C (5 / 3 : K) * (B + Bv) at hDsum
  have hz : f * (WPFiniteZSource.P p u - d - q3 * (A - invert A) -
      q5 * ph * (d + invert d)) = 0 := by
    have h53 : LaurentPolynomial.C (5 / 3 : K) = 5 * q3 := by
      dsimp only [q3]
      simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
    rw [h53] at hT
    change f * WPFiniteZSource.P p u +
      q3 * (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) * B =
        (f * d - 5 * q3 * B) + q3 *
          ((f * A - (4 * T (p : ℤ) - 11) * B) - (f * invert A - ph * Bv)) at hT
    have he : f * (WPFiniteZSource.P p u - d - q3 * (A - invert A)) =
        q3 * ph * (B + Bv) := by
      dsimp only [ph]
      linear_combination hT
    calc
      _ = f * (WPFiniteZSource.P p u - d - q3 * (A - invert A)) -
          q5 * ph * (f * (d + invert d)) := by ring
      _ = 0 := by rw [he, hDsum]; linear_combination -ph * (B + Bv) * hq
  have hf : f ≠ 0 := by
    intro hzero
    have hfp : ActualThreePhase.fK (K := K) p hp = 0 :=
      Polynomial.toLaurent_injective (by simpa only [map_zero] using hzero)
    have hfa := (ActualGreenResidue.actual_native_pullback_facts (K := K) p hp).2.1
    rw [hfp, eval_zero] at hfa
    exact zero_ne_one hfa
  have he := (mul_eq_zero.mp hz).resolve_left hf
  change WPFiniteZSource.P p u - d = q3 * (A - invert A) + q5 * ph * (d + invert d)
  linear_combination he

/-- NC123a follows with both complete A/AQ halves and both Dstar halves. -/
theorem actual_Z52_NC123a (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    actualZ52 (K := K) p u =
      (actualAK (K := K) p).toLaurent ^ 2 - invert (actualAK (K := K) p).toLaurent ^ 2 +
      LaurentPolynomial.C (6 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
        invert (actualAK (K := K) p).toLaurent *
        ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent) := by
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3
  have h6 : (6 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 3 : K) = 2 := by
    change LaurentPolynomial.C (6 : K) * LaurentPolynomial.C (1 / 3 : K) =
      LaurentPolynomial.C (2 : K)
    rw [← map_mul]
    congr 1
    field_simp [h3]
    ring
  have h65 : (6 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 5 : K) =
      LaurentPolynomial.C (6 / 5 : K) := by
    change LaurentPolynomial.C (6 : K) * LaurentPolynomial.C (1 / 5 : K) = _
    rw [← map_mul]
    congr 1
    ring
  rw [actualZ52, actual_P_minus_Dstar p hp u hu]
  linear_combination invert (actualAK (K := K) p).toLaurent *
      ((actualAK (K := K) p).toLaurent - invert (actualAK (K := K) p).toLaurent) * h6 +
    (4 * T (-(p : ℤ)) - 11) * invert (actualAK (K := K) p).toLaurent *
      ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent) * h65

end ActualComparison

end WPFieldAssembly.ActualBpairContraction
