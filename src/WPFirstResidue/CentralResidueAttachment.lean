import WPFirstResidue.CentralResidue.LaurentField
import WPFirstResidue.LiteralNormalization
import WPActualNativeJacobiJet
import WPMomentPrecision.ConicCoordinates

open scoped BigOperators Polynomial LaurentPolynomial LaurentSeries RatFunc
open Polynomial LaurentPolynomial WPPIntegralReduction
  WPActualPullbackSource WPActualEtaPole WPActualEtaPrimitive WPActualEtaIntegrality
  WPActualPositiveResidueSource WPActualCentralResidueSource WPActualCentralNativeJet
  WPActualChiSource WPLaurentIntegralResidue WPActualNativeParameter WPActualNativeFirstJet
  WPActualNativeJetODE WPHasseIntegralTransport WPActualNativeJacobiJet
  WPActualRankTwoLegendreField WPActualRankTwoResidueSource
  WPMomentPrecision.ConicCoordinates WPFirstResidue.CentralResidue

namespace WPFirstResidue.CentralResidueAttachment

set_option maxHeartbeats 1200000

variable (p : ℕ) [Fact p.Prime]

/-- The original full-cutoff rational central residue, before any scalar lift or division. -/
noncomputable def actualR0 : ℚ :=
  WPFirstResidue.LiteralNormalization.actualFirstResidue p

/-- The literal Fermat-quotient lift is fixed over Q before reduction.
It is distinct from the harmonic rational representative. -/
noncomputable def literalR0 : ℚ :=
  WPFirstResidue.LiteralNormalization.literalR0 p

theorem actual_R0_integral (hp : 19 ≤ p) : actualR0 p ∈ integralRationals p := by
  exact WPFirstResidue.LiteralNormalization.actualFirstResidue_integral p hp

noncomputable def integralNativeJet (hp : 19 ≤ p) : (integralRationals p)[X] :=
  ∑ n : Fin ((p - 1) / 2 + 1), monomial n.val
    (integralParameterJet p n.val (by omega) (by
      have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
      have hn := n.isLt
      omega))

theorem integralNativeJet_rational (hp : 19 ≤ p) :
    (integralNativeJet p hp).map (integralRationals p).subtype = nativeJetPolynomial p := by
  unfold integralNativeJet
  rw [Polynomial.map_sum]
  calc
    _ = ∑ n : Fin ((p - 1) / 2 + 1),
        monomial n.val (parameterJet n.val (-(p : ℚ) / 6)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Polynomial.map_monomial]
      congr 1
      have hn : n.val < p := by
        have hn' := n.isLt
        omega
      change (integralParameterJet p n.val (by omega) hn).val = _
      exact integralParameterJet_value p n.val (by omega) hn
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun n => monomial n (parameterJet n (-(p : ℚ) / 6))) ((p - 1) / 2 + 1)

theorem integralNativeJet_field (hp : 19 ≤ p) :
    (integralNativeJet p hp).map (residueHom p) = nativeJetField p := by
  unfold integralNativeJet nativeJetField
  rw [Polynomial.map_sum]
  calc
    _ = ∑ n : Fin ((p - 1) / 2 + 1),
        monomial n.val (parameterJet n.val (-(p : ℚ) / 6) : ZMod p) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Polynomial.map_monomial]
      congr 1
      have hn : n.val < p := by
        have hn' := n.isLt
        omega
      change ((integralParameterJet p n.val (by omega) hn).val : ZMod p) = _
      rw [integralParameterJet_value p n.val (by omega) hn]
    _ = _ := Fin.sum_univ_eq_sum_range
      (fun n => monomial n (parameterJet n (-(p : ℚ) / 6) : ZMod p)) ((p - 1) / 2 + 1)

/-- Original reciprocal native pullback in the proved integral coefficient ring. -/
noncomputable def integralNativeJetPullback (hp : 19 ≤ p) : (integralRationals p)[T;T⁻¹] :=
  T (((p - 1) / 2 : ℕ) : ℤ) *
    invert (Polynomial.toLaurent ((integralNativeJet p hp).comp (integralV p (by omega))))

theorem integralNativeJetPullback_rational (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (integralNativeJetPullback p hp) =
      nativeJetPullback p := by
  simp only [integralNativeJetPullback, map_mul, coefficientMap_T, coefficientMap_invert,
    coefficientMap_toLaurent, Polynomial.map_comp, integralNativeJet_rational,
    integralV_map_rational]
  rw [← substituteOver_toLaurent, substituteOver_invert]
  change T (((p - 1) / 2 : ℕ) : ℤ) *
    substituteOver (nativeJetPolynomial p) (invert Vx) = nativeJetPullback p
  rw [actual_Vx_reciprocal]
  rfl

noncomputable def nativeQField : (ZMod p)[T;T⁻¹] :=
  invert (Polynomial.toLaurent (fieldV p))

noncomputable def nativeJetPullbackField : (ZMod p)[T;T⁻¹] :=
  T (((p - 1) / 2 : ℕ) : ℤ) * substituteOver (nativeJetField p) (nativeQField p)

theorem integralNativeJetPullback_field (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (integralNativeJetPullback p hp) = nativeJetPullbackField p := by
  simp only [integralNativeJetPullback, map_mul, coefficientMap_T, coefficientMap_invert,
    coefficientMap_toLaurent, Polynomial.map_comp, integralNativeJet_field,
    integralV_map_field]
  rw [← substituteOver_toLaurent, substituteOver_invert]
  rfl

noncomputable def integralNativeJetDensity (hp : 19 ≤ p) : (integralRationals p)[T;T⁻¹] :=
  integralLift p ⟨weightedDifference (nativeJetPullback p),
    weightedDifference_integral p (by omega) _
      (actual_nativeJetPullback_integral p (by omega))⟩

noncomputable def nativeJetDensityField (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  coefficientMap (residueHom p) (integralNativeJetDensity p hp)

theorem native_jet_density_original_coefficient (hp : 19 ≤ p) (j : ℤ) :
    (nativeJetDensityField p hp).coeff j =
      ((weightedDifference (nativeJetPullback p)).coeff j : ZMod p) := by
  rw [nativeJetDensityField, coefficientMap_coeff, integralNativeJetDensity, integralLift_coeff]
  rfl

omit [Fact p.Prime] in
/-- The two original end poles vanish at the actual full native jet, before reduction. -/
theorem actual_native_jet_cleared_density :
    (T 1 - LaurentPolynomial.C (1 / 4 : ℚ)) *
      (T 1 - LaurentPolynomial.C (4 : ℚ)) *
        weightedDifference (nativeJetPullback p) =
      (LaurentPolynomial.C (2 : ℚ) * (T 1 - LaurentPolynomial.C (4 : ℚ)) +
        (T 1 - LaurentPolynomial.C (1 / 4 : ℚ))) *
        nativeJetPullback p := by
  have ha := dividedDifference_identity (1 / 4) (by norm_num) (nativeJetPullback p)
  have hb := dividedDifference_identity 4 (by norm_num) (nativeJetPullback p)
  rw [(actual_nativeJetPullback_endpoints p).1, map_zero, sub_zero] at ha
  rw [(actual_nativeJetPullback_endpoints p).2, map_zero, sub_zero] at hb
  rw [weightedDifference_apply]
  linear_combination LaurentPolynomial.C (2 : ℚ) *
    (T 1 - LaurentPolynomial.C (4 : ℚ)) * ha +
    (T 1 - LaurentPolynomial.C (1 / 4 : ℚ)) * hb

noncomputable def integralQuarter (hp : 19 ≤ p) : integralRationals p :=
  ⟨1 / 4, WPFiniteConductorPolynomial.small_inverse_integral p 4 (by norm_num) (by omega)⟩

theorem integralQuarter_rational (hp : 19 ≤ p) :
    (integralRationals p).subtype (integralQuarter p hp) = (1 / 4 : ℚ) := rfl

theorem integralQuarter_field (hp : 19 ≤ p) :
    residueHom p (integralQuarter p hp) = (1 / 4 : ZMod p) := by
  change ((1 / 4 : ℚ) : ZMod p) = _
  norm_num [Rat.cast_def]

theorem actual_integral_native_jet_cleared_density (hp : 19 ≤ p) :
    (T 1 - LaurentPolynomial.C (integralQuarter p hp)) *
      (T 1 - (4 : (integralRationals p)[T;T⁻¹])) * integralNativeJetDensity p hp =
      (2 * (T 1 - (4 : (integralRationals p)[T;T⁻¹])) +
        (T 1 - LaurentPolynomial.C (integralQuarter p hp))) *
        integralNativeJetPullback p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective _
    (Subring.subtype_injective (integralRationals p))
  simp only [map_mul, map_add, map_sub, map_ofNat, coefficientMap_T, coefficientMap_C,
    integralNativeJetDensity, integralLift_rational, integralNativeJetPullback_rational,
    integralQuarter_rational]
  simpa only [map_ofNat] using actual_native_jet_cleared_density p

theorem actual_field_native_jet_cleared_density (hp : 19 ≤ p) :
    (T 1 - LaurentPolynomial.C (1 / 4 : ZMod p)) *
      (T 1 - (4 : (ZMod p)[T;T⁻¹])) * nativeJetDensityField p hp =
      (2 * (T 1 - (4 : (ZMod p)[T;T⁻¹])) +
        (T 1 - LaurentPolynomial.C (1 / 4 : ZMod p))) * nativeJetPullbackField p := by
  have h := congrArg (coefficientMap (residueHom p))
    (actual_integral_native_jet_cleared_density p hp)
  simpa only [map_mul, map_add, map_sub, map_ofNat, coefficientMap_T, coefficientMap_C,
    integralQuarter_field, integralNativeJetPullback_field, nativeJetDensityField] using h

theorem native_Q_field_rational :
    fieldRatify (nativeQField p) = Q (variableRat : RatFunc (ZMod p)) := by
  rw [nativeQField, fieldRatify_invert, reciprocalRatify_toLaurent]
  have h := fieldV_eval p (algebraMap (ZMod p) (RatFunc (ZMod p)))
    (variableRat : RatFunc (ZMod p))⁻¹
  rw [Polynomial.eval_map] at h
  rw [h, native_inverse _ variableRat_ne_zero]

theorem native_jet_pullback_field_rational :
    fieldRatify (nativeJetPullbackField p) =
      (variableRat : RatFunc (ZMod p)) ^ ((p - 1) / 2) *
        (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
          (Q (variableRat : RatFunc (ZMod p))) := by
  rw [nativeJetPullbackField, map_mul, fieldRatify_T, zpow_natCast,
    fieldRatify_substitute, native_Q_field_rational]

/-- The actual full native rational differential on the original x line. -/
noncomputable def nativeJetRationalDensity : RatFunc (ZMod p) :=
  (variableRat : RatFunc (ZMod p)) ^ ((p - 1) / 2) *
    (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
      (Q (variableRat : RatFunc (ZMod p))) *
    (2 / ((variableRat : RatFunc (ZMod p)) - 1 / 4) + 1 / (variableRat - 4))

/-- No endpoint residue is supplied: the exact endpoint zeros above prove this rational source. -/
theorem actual_native_jet_rational_density (hp : 19 ≤ p) :
    fieldRatify (nativeJetDensityField p hp) = nativeJetRationalDensity p := by
  have h := congrArg (fieldRatify (K := ZMod p))
    (actual_field_native_jet_cleared_density p hp)
  simp only [map_mul, map_add, map_sub, map_ofNat, fieldRatify_T, fieldRatify_C,
    zpow_one, map_div₀, map_one] at h
  rw [native_jet_pullback_field_rational] at h
  have ha : (variableRat : RatFunc (ZMod p)) - 1 / 4 ≠ 0 := by
    simpa only [map_div₀, map_one, map_ofNat] using
      (variableRat_sub_constant_ne_zero (1 / 4 : ZMod p))
  have hb : (variableRat : RatFunc (ZMod p)) - 4 ≠ 0 := by
    simpa only [map_ofNat] using (variableRat_sub_constant_ne_zero (4 : ZMod p))
  unfold nativeJetRationalDensity
  field_simp [ha, hb]
  linear_combination h

/-- Literal Laurent coefficient equals the residue of the original rational native density. -/
theorem actual_native_jet_density_residue_attachment (hp : 19 ≤ p) :
    (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
        (nativeJetRationalDensity p)).coeff (-1) =
      ((weightedDifference (nativeJetPullback p)).coeff (-1) : ZMod p) := by
  rw [← actual_native_jet_rational_density p hp]
  exact (rationalSeries_coefficient (nativeJetDensityField p hp) (-1)).trans
    (native_jet_density_original_coefficient p hp (-1))

/-- The checked literal high-band source and the checked full native jet
give the same actual first coefficient. No residue value is assigned. -/
theorem actual_central_first_source_native_coefficient (hp : 19 ≤ p) :
    ((weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1) : ZMod p) =
      (1 / 6 : ZMod p) *
        ((weightedDifference (nativeJetPullback p)).coeff (-1) : ZMod p) := by
  have hfirst := literal_central_first_source p hp
  have hnative := literal_central_native_jet p hp
  linear_combination hfirst - hnative

/-- NC44's original high-band coefficient is attached to the whole
native rational density, retaining the coefficientwise integral reduction. -/
theorem actual_central_first_source_rational_attachment (hp : 19 ≤ p) :
    ((weightedDifference (negativeFirstSource p ((p - 1) / 2))).coeff (-1) : ZMod p) =
      (1 / 6 : ZMod p) *
        (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
          (nativeJetRationalDensity p)).coeff (-1) := by
  rw [actual_native_jet_density_residue_attachment p hp]
  exact actual_central_first_source_native_coefficient p hp

theorem native_Q_field_reciprocal_rational :
    reciprocalRatify (nativeQField p) = V (variableRat : RatFunc (ZMod p)) := by
  rw [nativeQField, reciprocalRatify_invert, fieldRatify_toLaurent]
  have h := fieldV_eval p (algebraMap (ZMod p) (RatFunc (ZMod p)))
    (variableRat : RatFunc (ZMod p))
  rwa [Polynomial.eval_map] at h

theorem native_jet_pullback_field_reciprocal_rational :
    reciprocalRatify (nativeJetPullbackField p) =
      (variableRat : RatFunc (ZMod p))⁻¹ ^ ((p - 1) / 2) *
        (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
          (V (variableRat : RatFunc (ZMod p))) := by
  rw [nativeJetPullbackField, map_mul, reciprocalRatify_T, zpow_natCast,
    reciprocalRatify_substitute, native_Q_field_reciprocal_rational]

theorem actual_native_jet_reciprocal_density (hp : 19 ≤ p) :
    reciprocalRatify (nativeJetDensityField p hp) =
      (variableRat : RatFunc (ZMod p))⁻¹ ^ ((p - 1) / 2) *
        (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
          (V (variableRat : RatFunc (ZMod p))) *
        (2 / ((variableRat : RatFunc (ZMod p))⁻¹ - 1 / 4) +
          1 / (variableRat⁻¹ - 4)) := by
  have h := congrArg (reciprocalRatify (K := ZMod p))
    (actual_field_native_jet_cleared_density p hp)
  simp only [map_mul, map_add, map_sub, map_ofNat, reciprocalRatify_T, reciprocalRatify_C,
    zpow_one, map_div₀, map_one] at h
  rw [native_jet_pullback_field_reciprocal_rational] at h
  have ha : (variableRat : RatFunc (ZMod p))⁻¹ - 1 / 4 ≠ 0 := by
    simpa only [map_div₀, map_one, map_ofNat] using
      (inverse_variableRat_sub_constant_ne_zero (1 / 4 : ZMod p))
  have hb : (variableRat : RatFunc (ZMod p))⁻¹ - 4 ≠ 0 := by
    simpa only [map_ofNat] using (inverse_variableRat_sub_constant_ne_zero (4 : ZMod p))
  rw [div_add_div _ _ ha hb, ← mul_div_assoc]
  apply (eq_div_iff (mul_ne_zero ha hb)).mpr
  linear_combination h

/-- The reciprocal logarithmic differential has its complete -3/x term. -/
theorem inversion_logarithmic_density {K : Type*} [Field K]
    (x : K) (hx : x ≠ 0) (h4 : (4 : K) ≠ 0)
    (ha : x - 1 / 4 ≠ 0) (hb : x - 4 ≠ 0)
    (_hai : x⁻¹ - 1 / 4 ≠ 0) (_hbi : x⁻¹ - 4 ≠ 0) :
    -x⁻¹ ^ 2 * (2 / (x⁻¹ - 1 / 4) + 1 / (x⁻¹ - 4)) =
      1 / (x - 1 / 4) + 2 / (x - 4) - 3 / x := by
  have h4minus : 4 - x ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  have h4x : 4 * x - 1 ≠ 0 := by
    have he : 4 * x - 1 = 4 * (x - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hminus1 : -1 + x * 4 ≠ 0 := by
    convert h4x using 1; ring
  have h1minus : 1 - x * 4 ≠ 0 := by
    convert neg_ne_zero.mpr h4x using 1; ring
  field_simp [hx, h4, ha, hb, _hai, _hbi, h4minus, h4x, hminus1, h1minus]
  field_simp [hminus1]; ring

noncomputable def nativeJetInvertedRationalDensity : RatFunc (ZMod p) :=
  (variableRat : RatFunc (ZMod p))⁻¹ ^ ((p - 1) / 2) *
    (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
      (V (variableRat : RatFunc (ZMod p))) *
    (1 / ((variableRat : RatFunc (ZMod p)) - 1 / 4) + 2 / (variableRat - 4) -
      3 / variableRat)

/-- Original x=1/u differential, with every native coefficient and the negative Jacobian. -/
theorem actual_native_jet_inverted_rational_density (hp : 19 ≤ p) :
    fieldRatify (-T (-2) * invert (nativeJetDensityField p hp)) =
      nativeJetInvertedRationalDensity p := by
  have h4field : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h4 : (4 : RatFunc (ZMod p)) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap (ZMod p) (RatFunc (ZMod p)))).mpr h4field
  have ha : (variableRat : RatFunc (ZMod p)) - 1 / 4 ≠ 0 := by
    simpa only [map_div₀, map_one, map_ofNat] using
      (variableRat_sub_constant_ne_zero (1 / 4 : ZMod p))
  have hb : (variableRat : RatFunc (ZMod p)) - 4 ≠ 0 := by
    simpa only [map_ofNat] using (variableRat_sub_constant_ne_zero (4 : ZMod p))
  have hai : (variableRat : RatFunc (ZMod p))⁻¹ - 1 / 4 ≠ 0 := by
    simpa only [map_div₀, map_one, map_ofNat] using
      (inverse_variableRat_sub_constant_ne_zero (1 / 4 : ZMod p))
  have hbi : (variableRat : RatFunc (ZMod p))⁻¹ - 4 ≠ 0 := by
    simpa only [map_ofNat] using (inverse_variableRat_sub_constant_ne_zero (4 : ZMod p))
  rw [signed_reciprocal_rational_source, actual_native_jet_reciprocal_density p hp,
    nativeJetInvertedRationalDensity]
  have hlog := inversion_logarithmic_density (variableRat : RatFunc (ZMod p))
    variableRat_ne_zero h4 ha hb hai hbi
  linear_combination (variableRat : RatFunc (ZMod p))⁻¹ ^ ((p - 1) / 2) *
    (nativeJetField p).eval₂ (algebraMap (ZMod p) (RatFunc (ZMod p)))
      (V (variableRat : RatFunc (ZMod p))) * hlog

/-- The sign I_x=-I_u is proved coefficientwise, including the logarithmic slot. -/
theorem actual_native_jet_inversion_residue (hp : 19 ≤ p) :
    (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
        (nativeJetInvertedRationalDensity p)).coeff (-1) =
      -((weightedDifference (nativeJetPullback p)).coeff (-1) : ZMod p) := by
  rw [← actual_native_jet_inverted_rational_density p hp]
  exact (differential_inverse_residue (nativeJetDensityField p hp)).trans
    (congrArg Neg.neg (native_jet_density_original_coefficient p hp (-1)))

/-- NC44/45/62's actual full-cutoff r0 is attached to the entire rational native density. -/
theorem actual_central_native_density (hp : 19 ≤ p) :
    (actualR0 p : ZMod p) =
      -(1 / 2 : ZMod p) * (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) -
      (1 / 6 : ZMod p) *
        (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
          (nativeJetRationalDensity p)).coeff (-1) := by
  rw [actual_native_jet_density_residue_attachment p hp]
  exact literal_central_native_jet p hp

/-- NC59's actual I_u orientation, still before the CM finite-part evaluation. -/
theorem actual_central_inverted_native_density (hp : 19 ≤ p) :
    (actualR0 p : ZMod p) =
      (1 / 6 : ZMod p) *
        (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
          (nativeJetInvertedRationalDensity p)).coeff (-1) -
      (1 / 2 : ZMod p) * (((Hpolynomial (p / 6)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) := by
  rw [actual_native_jet_inversion_residue p hp]
  have h := literal_central_native_jet p hp
  change (actualR0 p : ZMod p) = _ at h
  linear_combination h

/-- The entire original Q-coordinate native jet on either conic branch. -/
theorem actual_native_Q_conic_jet {K : Type*} [Field K]
    (hp : 19 ≤ p) (f : ZMod p →+* K) (t w : K)
    (h5 : (5 : K) ≠ 0) (hw : w ≠ 0) (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    (nativeJetField p).eval₂ f (Q (w ^ 2)) =
      2 * (actualLegendreJacobi p).eval₂ f (cubic (t / w)) *
        (actualRankDividedField p (by omega)).eval₂ f (cubic (t / w)) := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval₂ f (cubic (t / w)))
    (actual_native_Jacobi_jet p hp)
  have hq : 1 - cubic (t / w) ^ 2 = q (t / w) := by
    linear_combination -(cubic_square (t / w))
  simp only [nativeJacobiJet, Polynomial.eval₂_comp, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
    Polynomial.eval₂_ofNat] at h
  rw [hq] at h
  rw [native_Q_on_conic t w h5 hw hc]
  exact h

/-- NC56's complete conic differential, retaining the original x^N and dx/dt. -/
theorem actual_native_jet_conic_density {K : Type*} [Field K]
    (hp : 19 ≤ p) (f : ZMod p →+* K) (t w : K)
    (h5 : (5 : K) ≠ 0) (hw : w ≠ 0)
    (ha : 1 - t ^ 2 ≠ 0) (hb : 4 * t ^ 2 - 1 ≠ 0)
    (hc : w ^ 2 = 5 * t ^ 2 - 1) :
    (w ^ 2) ^ ((p - 1) / 2) * (nativeJetField p).eval₂ f (Q (w ^ 2)) *
        (10 * t * (8 / (4 * w ^ 2 - 1) + 1 / (w ^ 2 - 4))) =
      -12 * w ^ (2 * ((p - 1) / 2)) *
        (actualLegendreJacobi p).eval₂ f (cubic (t / w)) *
        (actualRankDividedField p (by omega)).eval₂ f (cubic (t / w)) *
        cubic t / A t := by
  rw [actual_native_Q_conic_jet p hp f t w h5 hw hc,
    conic_dlog_V t w h5 ha hb hc, ← pow_mul]
  ring

/-- The checked complete native first integral is the NC55 load-bearing
source for the ratio J/F, including the entire (1-z)^N term. -/
theorem actual_native_first_ratio_cleared_source {K : Type*} [Field K]
    (hp : 19 ≤ p) (f : ZMod p →+* K) (z : K) :
    z * ((WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z *
          (nativeJetField p).derivative.eval₂ f z -
        (WPActualNativeHasse.nativeField p (p / 6)).derivative.eval₂ f z *
          (nativeJetField p).eval₂ f z) =
      (WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z *
        ((1 - z) ^ ((p - 1) / 2) -
          (WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z) := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval₂ f z)
    (WPActualNativeFirstIntegral.actual_native_first_integral p hp)
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_one, Polynomial.eval₂_X] using h

/-- Quotient differentiation at any actual unit point, obtained from the
native polynomial source above rather than a supplied differential identity. -/
theorem actual_native_first_ratio_differential_source {K : Type*} [Field K]
    (hp : 19 ≤ p) (f : ZMod p →+* K) (z dz : K) (hz : z ≠ 0)
    (hF : (WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z ≠ 0) :
    (((WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z *
          (nativeJetField p).derivative.eval₂ f z -
        (WPActualNativeHasse.nativeField p (p / 6)).derivative.eval₂ f z *
          (nativeJetField p).eval₂ f z) /
      ((WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z) ^ 2) * dz =
      ((1 - z) ^ ((p - 1) / 2) /
          (WPActualNativeHasse.nativeField p (p / 6)).eval₂ f z - 1) * (dz / z) := by
  have h := actual_native_first_ratio_cleared_source p hp f z
  field_simp [hz, hF]
  linear_combination dz * h

/- The scalar boundary is exact: signed inversion and the complete native
ratio differential source are attached above. The remaining global
integration-by-parts comparison must identify I_u with -3 beta-C using the
actual native CM rational function, including its nonzero odd simple pole
and coordinate correction. Root owns NC57/58 and that CM evaluation.
No actualR0=literalR0
field equality, divided rho, or harmonic rational lift is assumed here. -/

end WPFirstResidue.CentralResidueAttachment
