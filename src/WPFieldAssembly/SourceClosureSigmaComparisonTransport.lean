import WPFieldAssembly.SourceClosureSigmaLogCarry
import WPFieldAssembly.SourceClosureSigmaWholeSupport
import WPFieldAssembly.ActualSigmaSourceAttachment

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction WPActualRankTwoHatLift
  WPFieldAssembly.ActualSigmaFiniteEvenSource WPFieldAssembly.ActualSigmaNormCarrySource
  WPFieldAssembly.ActualSigmaClearedSource WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.SourceClosureSigmaKCarry WPFieldAssembly.SourceClosureSigmaWholePrimitive
  WPFieldAssembly.SourceClosureSigmaLogCarry WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.ActualSigmaSourceAttachment WPFieldAssembly.ActualComparisonKwAttachment
  WPFieldAssembly.ActualBalancedTrace

namespace WPFieldAssembly.SourceClosureSigmaComparisonTransport

set_option maxHeartbeats 1500000

noncomputable def originalLiteralCQ (p : ℕ) : ℚ :=
  (finiteEvenSquaredQ p).eval (4 / 5) - (finiteEvenSquaredQ p).eval (1 / 5)

noncomputable def originalEndpointPhaseQ (p : ℕ) : ℚ :=
  17 - 4 * ((1 / 4 : ℚ) ^ p + (4 : ℚ) ^ p)

noncomputable def originalComparisonBranchQ (p : ℕ) : ℚ :=
  originalEndpointPhaseQ p / 15 *
    ((finiteEvenSquaredQ p).eval (1 / 4) - (finiteEvenSquaredQ p).eval 4)

theorem originalWbarQ_moving (p : ℕ) [Fact p.Prime] :
    originalWbarQ p = Polynomial.C (2 * (5 : ℚ) ^ ((p - 1) / 2) / 15) *
      (originalMovingQ p - Polynomial.C (originalLiteralCQ p)) := by
  simp only [originalWbarQ, originalE4CenteredQ, originalE1CenteredQ,
    originalMovingQ, originalLiteralCQ, _root_.map_sub]
  ring

theorem originalWbarQ_degree (p : ℕ) [Fact p.Prime] :
    (originalWbarQ p).natDegree ≤ (p - 1) / 2 := by
  exact SourceClosureSigmaWholeSupport.originalWbarQ_degree p

/-- These two actual rational product holes vanish before the degree-N band is reduced. -/
theorem originalKbarWbarQ_holes (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (originalKbarQ p * (originalWbarQ p).toLaurent).coeff 0 = 0 ∧
      (originalKbarQ p * (originalWbarQ p).toLaurent).coeff (p : ℤ) = 0 := by
  let W := (originalWbarQ p).toLaurent
  have h0 : W.coeff 0 = 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, WPFiniteJCarrier.toLaurent_coeff_nat,
      coeff_zero_eq_eval_zero, originalWbarQ_origin]
  have hout (j : ℤ) (hj : j < 0 ∨ ((p - 1) / 2 : ℕ) < j) : W.coeff j = 0 := by
    exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (hj.imp_right (by
      intro hj
      have := originalWbarQ_degree p
      omega))
  have hphase (j : ℤ) : (normPhase p * W : ℚ[T;T⁻¹]).coeff j =
      17 * W.coeff j - 4 * W.coeff (j - p) - 4 * W.coeff (j + p) := by
    simp only [normPhase, sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [show (17 : ℚ[T;T⁻¹]) * W = LaurentPolynomial.C (17 : ℚ) * T 0 * W by
      simp only [T_zero, mul_one, _root_.map_ofNat],
      show (4 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (4 : ℚ) by
        simp only [_root_.map_ofNat]]
    simp only [WPFiniteJCarrier.shifted_coeff, sub_zero, sub_neg_eq_add]
  constructor
  · rw [originalKbarQ, mul_assoc, SourceClosureSigmaProperJ.C_mul_coeff, hphase]
    rw [h0, hout _ (Or.inl (by omega)), hout _ (Or.inr (by omega))]
    ring
  · rw [originalKbarQ, mul_assoc, SourceClosureSigmaProperJ.C_mul_coeff, hphase,
      sub_self, h0, hout _ (Or.inr (by omega)), hout _ (Or.inr (by omega))]
    ring

theorem originalKbarWbarQ_can (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalCanQ p (originalKbarQ p * (originalWbarQ p).toLaurent) =
      originalKbarQ p * (originalWbarQ p).toLaurent := by
  obtain ⟨h0, hp0⟩ := originalKbarWbarQ_holes p hp
  simp only [originalCanQ, h0, hp0, _root_.map_zero, zero_mul, sub_zero]

theorem originalKbarWbarQ_moving (p : ℕ) [Fact p.Prime] :
    originalKbarQ p * (originalWbarQ p).toLaurent = originalPhaseQ p *
      ((originalMovingQ p).toLaurent - LaurentPolynomial.C (originalLiteralCQ p)) := by
  have h5 : (5 : ℚ) ^ ((p - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc : (1 / (2 * (5 : ℚ) ^ ((p - 1) / 2))) *
      (2 * (5 : ℚ) ^ ((p - 1) / 2) / 15) = 1 / 15 := by
    field_simp [h5]
  have hC := congrArg (fun c : ℚ => (LaurentPolynomial.C c : ℚ[T;T⁻¹])) hc
  simp only [_root_.map_mul] at hC
  rw [originalKbarQ, originalWbarQ_moving]
  simp only [_root_.map_mul, _root_.map_sub, Polynomial.toLaurent_C,
    originalPhaseQ, normPhase]
  linear_combination
    (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) *
      ((originalMovingQ p).toLaurent - LaurentPolynomial.C (originalLiteralCQ p)) * hC

theorem phase_endpoints (p : ℕ) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ (originalPhaseQ p) =
      originalEndpointPhaseQ p / 15 ∧
    LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹ (originalPhaseQ p) =
      originalEndpointPhaseQ p / 15 := by
  have hv : (fourUnitQ : ℚ) = 4 := rfl
  constructor <;>
    simp only [originalPhaseQ, _root_.map_mul, _root_.map_sub,
      LaurentPolynomial.eval₂_C, RingHom.id_apply, _root_.map_ofNat,
      LaurentPolynomial.eval₂_T_n, LaurentPolynomial.eval₂_T_neg_n,
      Units.val_inv_eq_inv_val, hv, inv_pow, inv_inv,
      originalEndpointPhaseQ, one_div] <;> ring

theorem phase_inversion (p : ℕ) : invert (originalPhaseQ p) = originalPhaseQ p := by
  simp only [originalPhaseQ, _root_.map_mul, _root_.map_sub, invert_C, invert_T,
    neg_neg, _root_.map_ofNat]
  ring

theorem phase_endpoint_difference (p : ℕ) :
    originalPhaseQ p + LaurentPolynomial.C (4 / 15 : ℚ) * originalZpQ p =
      LaurentPolynomial.C (originalEndpointPhaseQ p / 15) := by
  have hv : (fourUnitQ : ℚ) = 4 := rfl
  simp only [originalPhaseQ, originalZpQ, endSym, invert_T,
    LaurentPolynomial.eval₂_T_n,
    Units.val_inv_eq_inv_val, hv, inv_pow,
    originalEndpointPhaseQ, _root_.map_sub, _root_.map_add, _root_.map_mul,
    _root_.map_ofNat, one_mul, div_eq_mul_inv]
  ring

theorem moving_endpoints (p : ℕ) [Fact p.Prime] :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ (originalMovingQ p).toLaurent +
      LaurentPolynomial.eval₂ (RingHom.id ℚ) fourUnitQ⁻¹ (originalMovingQ p).toLaurent =
      (finiteEvenSquaredQ p).eval 4 - (finiteEvenSquaredQ p).eval (1 / 4) := by
  have hv : (fourUnitQ : ℚ) = 4 := rfl
  simp only [LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
    Units.val_inv_eq_inv_val, hv, originalMovingQ, eval_sub, eval_comp,
    eval_mul, eval_ofNat, WPFiniteWSource.squaredCoordinate, eval_C,
    eval_add, eval_X, eval_one]
  norm_num

/-- The literal C and actual endpoint phases cancel only after the whole rational EndSym. -/
theorem originalSbarQ_comparison_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalSbarQ p (originalLiteralCQ p) (originalKbarQ p) =
      originalComparisonQ p (originalComparisonBranchQ p) := by
  rw [originalSbarQ, originalKbarWbarQ_can p hp, originalKbarWbarQ_moving]
  have hph := phase_endpoints p
  have hm := moving_endpoints p
  have he := phase_endpoint_difference p
  generalize hM : (originalMovingQ p).toLaurent = M at hm ⊢
  generalize hC : originalLiteralCQ p = c
  simp only [endSym, _root_.map_mul, _root_.map_sub,
    invert_C, phase_inversion, LaurentPolynomial.eval₂_C, RingHom.id_apply,
    hph.1, hph.2]
  rw [originalComparisonQ, originalEvenSumQ, hM, originalComparisonBranchQ]
  have hmC := congrArg (fun q : ℚ => (LaurentPolynomial.C q : ℚ[T;T⁻¹])) hm
  have h8 : (LaurentPolynomial.C (8 * c / 15) : ℚ[T;T⁻¹]) =
      2 * LaurentPolynomial.C c * LaurentPolynomial.C (4 / 15 : ℚ) := by
    simpa only [_root_.map_mul, _root_.map_ofNat] using
      congrArg (fun q : ℚ => (LaurentPolynomial.C q : ℚ[T;T⁻¹]))
        (show 8 * c / 15 = (2 : ℚ) * c * (4 / 15 : ℚ) by ring)
  rw [h8]
  simp only [_root_.map_add, _root_.map_sub, _root_.map_mul] at hmC ⊢
  linear_combination
    -2 * LaurentPolynomial.C c * he -
      LaurentPolynomial.C (originalEndpointPhaseQ p / 15) * hmC

theorem comparisonBranchQ_original (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    comparisonBranchQ p = originalComparisonBranchQ p := by
  have h4 : (integralRationals p).subtype (smallIntegralInverse p 4) = (1 / 4 : ℚ) :=
    smallIntegralInverse_value p 4 (by omega) (by omega)
  have h15 : (integralRationals p).subtype (smallIntegralInverse p 15) = (1 / 15 : ℚ) :=
    smallIntegralInverse_value p 15 (by omega) (by omega)
  have hE : (ActualJointGreen.finiteEvenSquaredIntegral p).map
      (integralRationals p).subtype = finiteEvenSquaredQ p := by
    rw [actualFiniteEvenSquaredIntegral_original p hp, finiteEvenSquaredIntegral_value p hp]
  have hend : (integralRationals p).subtype (comparisonEndIntegral p) =
      (finiteEvenSquaredQ p).eval (1 / 4) - (finiteEvenSquaredQ p).eval 4 := by
    rw [comparisonEndIntegral, _root_.map_sub, ← eval_map_apply, ← eval_map_apply,
      hE, h4, _root_.map_ofNat]
  change (integralRationals p).subtype
    (smallIntegralInverse p 15 * (17 - 4 * ((smallIntegralInverse p 4) ^ p + 4 ^ p)) *
      comparisonEndIntegral p) = _
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_add, _root_.map_pow,
    _root_.map_ofNat, h4, h15, hend, originalComparisonBranchQ, originalEndpointPhaseQ]
  ring

/-- The full Sbar is the existing actual comparison, with its actual branch constant. -/
theorem originalSbarQ_actual_comparison (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originalSbarQ p (originalLiteralCQ p) (originalKbarQ p) = comparisonRational p hp := by
  rw [originalSbarQ_comparison_source p hp, actual_comparison_original p hp,
    comparisonBranchQ_original p hp]

end WPFieldAssembly.SourceClosureSigmaComparisonTransport
