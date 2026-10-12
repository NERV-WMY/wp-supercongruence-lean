import WPFieldAssembly.SourceClosureHFNativeTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualKwFieldTrace WPFieldAssembly.SourceClosureCommonWholeSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.SourceClosureBalancedOriginalDensity
  WPFieldAssembly.SourceClosureHFNativeTransport
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.ActualBpairContraction
  WPFieldAssembly.ActualNormCrossAttachment

namespace WPFieldAssembly.SourceClosureSigmaNativeKernel

/- IR60 uses the same whole original norm as actualProperLowNumerator.
   Its reflected Sigma is the native Jacobi source, distinct from the
   p-divided comparison derivative called commonSigmaField. -/

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

noncomputable def originalZW (p : ℕ) : K[T;T⁻¹] :=
  (WPFiniteWSource.W p : K[X]).toLaurent +
    invert (WPFiniteWSource.W p : K[X]).toLaurent +
    LaurentPolynomial.C (4 * WPFiniteABSourceTail.epsilon p * descendedC p / 15 : K)

/-- IR60's pure whole Laurent kernel, with the entire W band and original fifth constant. -/
noncomputable def originalNativeKSigma (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1 / WPFiniteABSourceTail.epsilon p : K) *
    (4 * T (-(p : ℤ)) - 11) * originalZW p

theorem originalZW_moving (p : ℕ) :
    (originalZW p : K[T;T⁻¹]) =
      LaurentPolynomial.C (2 * WPFiniteABSourceTail.epsilon p / 15 : K) *
        ((movingEvenField p : K[X]).toLaurent + invert (movingEvenField p).toLaurent) := by
  simp only [originalZW, WPFiniteWSource.W, map_mul, map_sub,
    Polynomial.toLaurent_C, invert_C, descendedC, movingEvenField,
    div_eq_mul_inv, map_ofNat]
  ring

/-- The actual comparison is K0 times the full original W reflection, without a root premise. -/
theorem actual_comparison_whole_W (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    comparisonField (K := K) p =
      LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
        WPFiniteZSource.phase p * originalZW p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hc : (1 / (2 * WPFiniteABSourceTail.epsilon p : K)) *
      (2 * WPFiniteABSourceTail.epsilon p / 15) = 1 / 15 := by
    field_simp [h2, heps]
  have hC := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul] at hC
  rw [originalZW_moving, comparisonField]
  linear_combination -WPFiniteZSource.phase p *
    ((movingEvenField p : K[X]).toLaurent + invert (movingEvenField p).toLaurent) * hC

/-- IR60a--b's whole cancellation is polynomial; no new end or added-point pole is used. -/
theorem actual_native_kernel_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ p * originalNativeKSigma p =
      2 * (4 - 11 * T 1) ^ p * comparisonField p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hc : (1 / WPFiniteABSourceTail.epsilon p : K) =
      2 * (1 / (2 * WPFiniteABSourceTail.epsilon p)) := by field_simp [h2, heps]
  have hC := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul, map_ofNat] at hC
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hphase := native_added_point_phase (K := K) p
  rw [WPFiniteZSource.phase_factorization p hp, originalNativeKSigma,
    actual_comparison_whole_W p hp, hC]
  linear_combination
    2 * LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      WPFiniteZSource.phase p * originalZW p *
      ((4 - 11 * T 1) ^ p * ht - T (p : ℤ) * hphase)

theorem actual_comparison_invert (p : ℕ) :
    invert (comparisonField (K := K) p) = comparisonField p := by
  simp only [comparisonField, WPFiniteZSource.phase, map_mul, map_sub, map_add,
    map_ofNat, invert_C, invert_T, neg_neg]
  rw [LaurentPolynomial.involutive_invert ((movingEvenField p : K[X]).toLaurent)]
  ring

/-- The pure IR60 kernel is the existing whole native kernel, before taking any residue. -/
theorem originalNativeKSigma_identification (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (originalNativeKSigma p : K[T;T⁻¹]) = nativeKSigma p := by
  have heps : (WPFiniteABSourceTail.epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hc : (1 / WPFiniteABSourceTail.epsilon p : K) *
      (2 * WPFiniteABSourceTail.epsilon p / 15) = (2/5 : K) * (1/3 : K) := by
    field_simp [heps]
    ring
  have hC := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul] at hC
  rw [originalNativeKSigma, originalZW_moving]
  simp only [nativeKSigma, ActualBpairContraction.Dstar, map_mul, map_neg,
    Polynomial.toLaurent_C, invert_C, movingEvenField]
  linear_combination
    (4 * T (-(p : ℤ)) - 11) *
      (((WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate).toLaurent +
        invert ((WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate).toLaurent) * hC

variable (p : ℕ) [Fact p.Prime]

/-- This is precisely the reflected Sigma summand in the existing proper numerator. -/
noncomputable def actualReflectedSigmaNumerator (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  -2 * coefficientMap (residueHom p) (comparisonIntegral p) *
    (T (((p-1)/2 : ℕ) : ℤ) * invert (actualSigmaPullback p hp).toLaurent)

noncomputable def actualProperSquaresNumerator : (ZMod p)[T;T⁻¹] :=
  3 * ActualChiEndpoints.zeta p ^ 2 * LaurentPolynomial.C (1/25 : ZMod p) *
    (actualProperSquareCarrier p).toLaurent + actualProperSquareLocal p +
    T (((p-1)/2 : ℕ) : ℤ) * invert (actualProperSquareLocal p)

theorem actual_proper_low_whole_source (hp : 19 ≤ p) :
    actualProperLowNumerator p hp = actualProperSquaresNumerator p +
      actualReflectedSigmaNumerator p hp := by
  unfold actualProperLowNumerator actualProperSquaresNumerator actualReflectedSigmaNumerator
  ring

noncomputable def actualReflectedSigmaWeightedNumerator (hp : 19 ≤ p) :
    (ZMod p)[T;T⁻¹] :=
  (3 * (ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) ^ p * dlogQNumerator *
    T (-(((p-1)/2 : ℕ) : ℤ))) *
    (LaurentPolynomial.C (1/6 : ZMod p) * actualReflectedSigmaNumerator p hp)

theorem actual_reflected_sigma_original_weight (hp : 19 ≤ p) :
    actualReflectedSigmaWeightedNumerator p hp =
      -(ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) ^ p * dlogQNumerator *
        comparisonField p * invert (actualSigmaPullback p hp).toLaurent := by
  have h6 : (6 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 6
    (by omega) (by omega)
  have hc : (6 : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (1/6 : ZMod p) = 1 := by
    change LaurentPolynomial.C (6 : ZMod p) * LaurentPolynomial.C (1/6 : ZMod p) = 1
    rw [← map_mul, mul_one_div_cancel h6, map_one]
  have ht : (T (-(((p-1)/2 : ℕ) : ℤ)) * T (((p-1)/2 : ℕ) : ℤ) :
      (ZMod p)[T;T⁻¹]) = 1 := by rw [← T_add, neg_add_cancel, T_zero]
  unfold actualReflectedSigmaWeightedNumerator actualReflectedSigmaNumerator
  rw [comparisonIntegral_field p hp]
  linear_combination
    -(ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) ^ p * dlogQNumerator *
      comparisonField p * invert (actualSigmaPullback p hp).toLaurent *
      (LaurentPolynomial.C (1/6 : ZMod p) * 6 * ht + hc)

private theorem inverse_kw_R : invert (ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) =
    T (-2) * (4 - 11 * T 1) := by
  simp only [ActualKwFieldTrace.R, map_mul, map_sub, map_ofNat, invert_T]
  have h1 : (T (-2) * T 1 : (ZMod p)[T;T⁻¹]) = T (-1) := by rw [← T_add]; norm_num
  have h2 : (T (-1) * T (-1) : (ZMod p)[T;T⁻¹]) = T (-2) := by rw [← T_add]; norm_num
  linear_combination 4 * h2 + 11 * h1

private theorem inverse_dlogQ : invert (dlogQNumerator : (ZMod p)[T;T⁻¹]) =
    3 * (4 * T 1 - 11) := by
  simp only [dlogQNumerator, map_mul, map_sub, map_ofNat, invert_T, neg_neg]
  have ht : (T 1 * T (-1) : (ZMod p)[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
  linear_combination -33 * ht

/-- Direct differential inversion includes the original minus sign and full shift 2p. -/
theorem actual_reflected_sigma_origin_numerator (hp : 19 ≤ p) :
    LaurentPolynomial.C (-2/3 : ZMod p) * T (2 * (p : ℤ)) *
        invert (actualReflectedSigmaWeightedNumerator p hp) =
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p *
        originalNativeKSigma p * (4 * T 1 - 11) * (actualSigmaPullback p hp).toLaurent := by
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hc : LaurentPolynomial.C (-2/3 : ZMod p) * (-3) = (2 : (ZMod p)[T;T⁻¹]) := by
    have hs : (-2/3 : ZMod p) * (-3) = 2 := by
      field_simp [h3]
    simpa only [map_mul, map_neg, map_ofNat] using
      congrArg (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) hs
  have ht : (T (2 * (p : ℤ)) * T (-2) ^ p : (ZMod p)[T;T⁻¹]) = 1 := by
    have hpow : (T (-2) : (ZMod p)[T;T⁻¹]) ^ p = T (-(2 * (p : ℤ))) := by
      rw [T_pow]
      congr 1
      ring
    rw [hpow, ← T_add, add_neg_cancel, T_zero]
  rw [actual_reflected_sigma_original_weight p hp]
  simp only [map_mul, map_neg, map_pow, inverse_kw_R, inverse_dlogQ,
    actual_comparison_invert, mul_pow]
  rw [LaurentPolynomial.involutive_invert ((actualSigmaPullback p hp).toLaurent)]
  rw [actual_native_kernel_cleared p hp]
  calc
    _ = (LaurentPolynomial.C (-2/3 : ZMod p) * (-3)) *
        (T (2 * (p : ℤ)) * T (-2) ^ p) * (4 - 11 * T 1) ^ p *
        comparisonField p * (4 * T 1 - 11) * (actualSigmaPullback p hp).toLaurent := by ring
    _ = _ := by rw [hc, ht]; ring

/-- The actual reflected carrier uses exactly the same KSigma as the whole HF source. -/
theorem actual_reflected_sigma_native_kernel (hp : 19 ≤ p) :
    LaurentPolynomial.C (-2/3 : ZMod p) * T (2 * (p : ℤ)) *
        invert (actualReflectedSigmaWeightedNumerator p hp) =
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p *
        nativeKSigma p * (4 * T 1 - 11) * (actualSigmaPullback p hp).toLaurent := by
  rw [actual_reflected_sigma_origin_numerator p hp,
    originalNativeKSigma_identification p hp]

/-- All native Sigma indices are actual unit pivots; its zero slot comes from the literal jet. -/
theorem actual_native_Sigma_unit_band (hp : 19 ≤ p) :
    (actualSigmaNative p hp).natDegree ≤ (p-1)/2 ∧
      (actualSigmaNative p hp).coeff 0 = 0 := by
  refine ⟨?_, ?_⟩
  · simpa only [actualSigmaNative] using actual_Sigma_native_degree p hp
  · have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2
      (by omega) (by omega)
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0)
      (actual_jet_twice_Sigma p hp)
    rw [WPActualNativeJetODE.nativeJetField_origin, eval_mul, eval_ofNat] at he
    rw [coeff_zero_eq_eval_zero]
    exact ((mul_eq_zero.mp he.symm).resolve_left h2)

/-- The literal full degree-N Euler primitive, rather than an assigned Sigma moment. -/
noncomputable def actualNativeHSigma (hp : 19 ≤ p) : (ZMod p)[X] :=
  WPActualPositivePair.eulerPrimitive p (actualSigmaNative p hp)

theorem actualNativeHSigma_source (hp : 19 ≤ p) :
    X * (actualNativeHSigma p hp).derivative = actualSigmaNative p hp := by
  obtain ⟨hd, h0⟩ := actual_native_Sigma_unit_band p hp
  exact WPActualPositivePair.eulerPrimitive_derivative p _ (by omega) h0

theorem actualNativeHSigma_degree_origin (hp : 19 ≤ p) :
    (actualNativeHSigma p hp).natDegree ≤ (p-1)/2 ∧
      (actualNativeHSigma p hp).eval 0 = 0 := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [actualNativeHSigma, WPActualPositivePair.eulerPrimitive_coeff,
      coeff_eq_zero_of_natDegree_lt (by
        have hd := (actual_native_Sigma_unit_band p hp).1
        omega), zero_div]
  · rw [← coeff_zero_eq_eval_zero, actualNativeHSigma,
      WPActualPositivePair.eulerPrimitive_coeff, Nat.cast_zero, div_zero]

/-- Clearing the actual cubic keeps the original end multiplicities 2 and 1. -/
theorem actual_V_logarithmic_clearing :
    (WPFiniteZSource.Abar : (ZMod p)[X]) * (WPHasseIntegralTransport.fieldV p).derivative =
      3 * (11 - 4 * X) * WPHasseIntegralTransport.fieldV p := by
  simp only [WPFiniteZSource.Abar, WPHasseIntegralTransport.fieldV,
    pow_two, derivative_mul, derivative_C, derivative_X,
    derivative_sub, derivative_ofNat, derivative_one, zero_mul, zero_add,
    sub_zero, zero_sub, mul_one]
  ring

theorem actualNativeHSigma_pullback_source (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
      D (((actualNativeHSigma p hp).comp (WPHasseIntegralTransport.fieldV p)).toLaurent) =
        3 * (11 - 4 * T 1) * (actualSigmaPullback p hp).toLaurent := by
  let V := WPHasseIntegralTransport.fieldV p
  have hV : V ≠ 0 := by
    intro hz
    apply WPActualCanonicalProjection.fieldVx_evaluate_ne_zero p hp
    change WPRationalCartier.evaluate p V.toLaurent = 0
    rw [hz, map_zero, map_zero]
  have hE := congrArg (fun P : (ZMod p)[X] => P.comp V)
    (actualNativeHSigma_source p hp)
  rw [mul_comp, X_comp] at hE
  have hpoly : (WPFiniteZSource.Abar : (ZMod p)[X]) *
      ((actualNativeHSigma p hp).comp V).derivative =
        3 * (11 - 4 * X) * actualSigmaPullback p hp := by
    apply mul_left_cancel₀ hV
    rw [derivative_comp]
    calc
      _ = ((WPFiniteZSource.Abar : (ZMod p)[X]) * V.derivative) *
          (V * (actualNativeHSigma p hp).derivative.comp V) := by ring
      _ = (3 * (11 - 4 * X) * V) * actualSigmaPullback p hp := by
        rw [actual_V_logarithmic_clearing, hE]
        rfl
      _ = _ := by ring
  have h := congrArg (fun P : (ZMod p)[X] => P.toLaurent) hpoly
  simpa only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X, D_toLaurent, V] using h

/-- IR60b is attached to the full unit-pivot primitive before any residue selection. -/
theorem actual_reflected_sigma_native_differential (hp : 19 ≤ p) :
    LaurentPolynomial.C (-2/3 : ZMod p) * T (2 * (p : ℤ)) *
        invert (actualReflectedSigmaWeightedNumerator p hp) =
      -LaurentPolynomial.C (1/3 : ZMod p) *
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ (p+1) * nativeKSigma p *
          D (((actualNativeHSigma p hp).comp (WPHasseIntegralTransport.fieldV p)).toLaurent) := by
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hc : LaurentPolynomial.C (1/3 : ZMod p) * 3 = (1 : (ZMod p)[T;T⁻¹]) := by
    change LaurentPolynomial.C (1/3 : ZMod p) * LaurentPolynomial.C (3 : ZMod p) = 1
    rw [← map_mul, one_div_mul_cancel h3, map_one]
  have hE := actualNativeHSigma_pullback_source p hp
  rw [actual_reflected_sigma_native_kernel p hp, pow_succ]
  linear_combination
    LaurentPolynomial.C (1/3 : ZMod p) *
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * nativeKSigma p * hE +
    -(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * nativeKSigma p *
      (4 * T 1 - 11) * (actualSigmaPullback p hp).toLaurent * hc

/-- The two proper square halves remain whole in their original weight. -/
noncomputable def actualProperSquaresOriginNumerator : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (-2/3 : ZMod p) * T (2 * (p : ℤ)) *
    invert ((3 * (ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹]) ^ p * dlogQNumerator *
      T (-(((p-1)/2 : ℕ) : ℤ))) *
      (LaurentPolynomial.C (1/6 : ZMod p) * actualProperSquaresNumerator p))

/-- The actual period is carried through inversion with the same pole denominator. -/
noncomputable def actualPeriodOriginNumerator (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (2/3 : ZMod p) * T (2 * (p : ℤ)) *
    invert ((LaurentPoleField.fieldAbar p).toLaurent ^ p *
      (dlogQNumerator * periodField p hp))

/-- The entire actual low density, including the period, has the IR60 reflected kernel. -/
theorem actual_whole_low_native_kernel (hp : 19 ≤ p) :
    LaurentPolynomial.C (-2/3 : ZMod p) * T (2 * (p : ℤ)) *
        invert (actualOriginalLowDensity p hp) =
      nativeHFOriginNumerator p hp + actualProperSquaresOriginNumerator p +
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p *
          nativeKSigma p * (4 * T 1 - 11) * (actualSigmaPullback p hp).toLaurent +
        actualPeriodOriginNumerator p hp := by
  have hH := actual_HF_infinity_origin_numerator (K := ZMod p) p hp
  have hid : ActualThreePhase.φ (K := ZMod p) p = RingHom.id (ZMod p) :=
    Subsingleton.elim _ _
  have hmap (F : (ZMod p)[T;T⁻¹]) : coefficientMap (RingHom.id (ZMod p)) F = F := by
    ext j
    rw [coefficientMap_coeff]
    rfl
  rw [hid, hmap] at hH
  have hS := actual_reflected_sigma_native_kernel p hp
  have hc : (LaurentPolynomial.C (-2/3 : ZMod p) : (ZMod p)[T;T⁻¹]) =
      -LaurentPolynomial.C (2/3 : ZMod p) := by rw [neg_div, map_neg]
  rw [actualOriginalLowDensity, actual_proper_low_whole_source p hp]
  simp only [mul_add, map_sub, map_add, map_mul]
  unfold actualProperSquaresOriginNumerator actualPeriodOriginNumerator
  change _ = nativeHFOriginNumerator p hp + _ + _ + _
  linear_combination (norm :=
    (simp only [actualReflectedSigmaWeightedNumerator, map_mul]; ring))
    hH + hS - T (2 * (p : ℤ)) *
    invert ((LaurentPoleField.fieldAbar p).toLaurent ^ p *
      (dlogQNumerator * periodField p hp)) * hc

end WPFieldAssembly.SourceClosureSigmaNativeKernel
