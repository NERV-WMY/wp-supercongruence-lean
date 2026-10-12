import WPFieldAssembly.NativeClosureMetricValue
import WPFieldAssembly.ActualSB72Attachment
import WPFieldAssembly.NativeClosureProperMetricGreen
import WPFieldAssembly.NativeClosureJointConic
import WPFieldAssembly.NativeClosureMetricRationalIdentities

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2200000

private theorem actual_metric_laurent_frobenius (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHandMetric p).toLaurent *
        (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent ^ ((p - 1) / 2) =
      LaurentPolynomial.C (1 / 5 : ZMod p) * (T (p : ℤ) + 1) *
        (actualMetricCore p).toLaurent := by
  have h := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (actual_metric_frobenius_source p hp)
  rw [map_mul, map_pow] at h
  simpa only [map_mul, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X_pow] using h

/-- The complete positive numerator belongs to the original actual logarithmic polynomial. -/
theorem actual_metric_du_cleared (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHandMetric p).toLaurent * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
        D (actualAK (K := ZMod p) p).toLaurent =
      metricDuCleared p (actualHandMetric p) (actualMetricCore p) := by
  have hu := actual_AK_cleared_derivative (K := ZMod p) p hp
  have hf := actual_metric_laurent_frobenius p hp
  rw [metricDuCleared_raw]
  linear_combination (actualHandMetric p).toLaurent * hu -
    LaurentPolynomial.C (3 / 2 : ZMod p) * (4 * T (p : ℤ) - 11) * hf

/-- The reciprocal attachment retains its two distinct half bands from the same actual u. -/
theorem actual_metric_dv_cleared (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHandMetric p).toLaurent * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
        D (invert (actualAK (K := ZMod p) p).toLaurent) =
      metricDvCleared p (actualHandMetric p) (actualMetricCore p) := by
  have hv := actual_AQ_cleared_derivative (K := ZMod p) p hp
  have hf := actual_metric_laurent_frobenius p hp
  rw [metricDvCleared_raw]
  simp only [neg_div, map_neg]
  linear_combination (actualHandMetric p).toLaurent * hv +
    LaurentPolynomial.C (3 / 2 : ZMod p) *
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * (4 * T (-(p : ℤ)) - 11) * hf

/-- The original actual metric has both logarithmic derivatives and its literal origin term. -/
noncomputable def actualMetricDensity (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  (- (actualHandMetric p).toLaurent *
      (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ)))) *
        D (literalKB (K := ZMod p) p) -
    (LaurentPolynomial.C (5 / 24 : ZMod p) * T (p : ℤ) * (4 * T (p : ℤ) - 11) +
      LaurentPolynomial.C (1 / 9 : ZMod p) * (4 * T (-(p : ℤ)) - 11)) *
        (actualHandMetric p).toLaurent * D (actualAK (K := ZMod p) p).toLaurent -
    LaurentPolynomial.C (25 / 18 : ZMod p) * (actualHandMetric p).toLaurent *
      D (invert (actualAK (K := ZMod p) p).toLaurent) +
    LaurentPolynomial.C (55 / 24 : ZMod p) * T (p : ℤ) * (actualHandMetric p).toLaurent *
      D (invert (actualAK (K := ZMod p) p).toLaurent) +
    (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) * T (-1) *
      (actualHandMetric p).toLaurent)

/-- Clearing the actual quadratic denominator transports every full metric term. -/
theorem actual_metric_density_cleared_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualMetricDensity p).coeff (-1) =
      metricClearedOrigin p (actualHandMetric p) (actualMetricCore p) := by
  let W : (ZMod p)[T;T⁻¹] :=
    LaurentPolynomial.C (5 / 24 : ZMod p) * T (p : ℤ) * (4 * T (p : ℤ) - 11) +
      LaurentPolynomial.C (1 / 9 : ZMod p) * (4 * T (-(p : ℤ)) - 11)
  have hu : originPole (W * metricDuCleared p (actualHandMetric p) (actualMetricCore p)) =
      (W * (actualHandMetric p).toLaurent * D (actualAK (K := ZMod p) p).toLaurent).coeff (-1) := by
    rw [← actual_metric_du_cleared p hp]
    rw [show W * ((actualHandMetric p).toLaurent *
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * D (actualAK p).toLaurent) =
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
        (W * (actualHandMetric p).toLaurent * D (actualAK p).toLaurent) by ring]
    exact originPole_cleared p hp _
  have hv (F : (ZMod p)[T;T⁻¹]) :
      originPole (F * metricDvCleared p (actualHandMetric p) (actualMetricCore p)) =
        (F * (actualHandMetric p).toLaurent *
          D (invert (actualAK (K := ZMod p) p).toLaurent)).coeff (-1) := by
    rw [← actual_metric_dv_cleared p hp]
    rw [show F * ((actualHandMetric p).toLaurent *
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * D (invert (actualAK p).toLaurent)) =
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent *
        (F * (actualHandMetric p).toLaurent * D (invert (actualAK p).toLaurent)) by ring]
    exact originPole_cleared p hp _
  have hv0 := hv 1
  simp only [one_mul] at hv0
  have hvp := hv (T (p : ℤ))
  dsimp only [metricClearedOrigin]
  change (actualMetricDensity p).coeff (-1) =
    (- (actualHandMetric p).toLaurent *
      (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ))) * D (literalKB p)).coeff (-1) -
    originPole (W * metricDuCleared p (actualHandMetric p) (actualMetricCore p)) -
    (25 / 18 : ZMod p) * originPole (metricDvCleared p (actualHandMetric p) (actualMetricCore p)) +
    (55 / 24 : ZMod p) * originPole (T (p : ℤ) *
      metricDvCleared p (actualHandMetric p) (actualMetricCore p)) +
    (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) * T (-1) *
      (actualHandMetric p).toLaurent).coeff (-1)
  rw [hu, hv0, hvp]
  have hs : actualMetricDensity p =
      (- (actualHandMetric p).toLaurent *
        (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ)))) * D (literalKB p) -
      W * (actualHandMetric p).toLaurent * D (actualAK p).toLaurent -
      LaurentPolynomial.C (25 / 18 : ZMod p) *
        ((actualHandMetric p).toLaurent * D (invert (actualAK p).toLaurent)) +
      LaurentPolynomial.C (55 / 24 : ZMod p) *
        (T (p : ℤ) * (actualHandMetric p).toLaurent * D (invert (actualAK p).toLaurent)) +
      (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) * T (-1) *
        (actualHandMetric p).toLaurent) := by
    dsimp only [actualMetricDensity, W]
    ring
  rw [hs]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, GreenLaurentOperators.C_mul_coeff]

/-- The whole actual metric value still names the original M(1) endpoint. -/
theorem actual_metric_density_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualMetricDensity p).coeff (-1) =
      -(1177 / 1500 : ZMod p) * (ActualFirstGreen.M p).eval 1 := by
  rw [actual_metric_density_cleared_origin p hp, actual_metric_cleared_value p hp]

/-- The same complete metric coefficient transports to the field used for the native conic. -/
theorem actual_metric_density_coefficientMap_value {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (g : ZMod p →+* K) :
    (WPActualChiSource.coefficientMap g (actualMetricDensity p)).coeff (-1) =
      -(1177 / 1500 : K) * g ((ActualFirstGreen.M p).eval 1) := by
  rw [WPActualChiSource.coefficientMap_coeff, actual_metric_density_value p hp]
  simp only [map_mul, map_neg, map_div₀, map_ofNat]

/-- Every original metric term is evaluated using the same actual Gauss primitive. -/
theorem actual_metric_density_gauss_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualMetricDensity p).coeff (-1) =
      -(1177 / 750 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 := by
  rw [actual_metric_density_cleared_origin p hp, actual_metric_cleared_gauss_value p hp]

/-- The complete actual Gauss metric value reaches the same faithful native field. -/
theorem actual_metric_density_coefficientMap_gauss_value {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (g : ZMod p →+* K) :
    (WPActualChiSource.coefficientMap g (actualMetricDensity p)).coeff (-1) =
      -(1177 / 750 : K) * g (WPActualGaussBottom.fieldHarmonic p (p / 6)) ^ 2 := by
  rw [WPActualChiSource.coefficientMap_coeff, actual_metric_density_gauss_value p hp]
  simp only [map_mul, map_neg, map_div₀, map_ofNat, map_pow]

/-- The logarithmic polynomial remains the same actual source in the native field. -/
theorem actual_metric_AK_coefficientMap {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
        (actualAK (K := ZMod p) p).toLaurent =
      (actualAK (K := K) p).toLaurent := by
  have hid : ActualThreePhase.φ (K := ZMod p) p = RingHom.id (ZMod p) :=
    Subsingleton.elim _ _
  simp only [WPActualChiSource.coefficientMap_toLaurent, actualAK, hid,
    Polynomial.map_id]

/-- Every original metric source term transports with the actual half-scale CMK.
The kernel, positive 2p phase, reciprocal phases and origin logarithm are all literal. -/
private theorem metric_D_coefficientMap {K L : Type*} [Field K] [Field L]
    (g : K →+* L) (U : K[T;T⁻¹]) :
    WPActualChiSource.coefficientMap g (D U) =
      D (WPActualChiSource.coefficientMap g U) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, map_mul, map_intCast]

theorem actual_metric_density_native_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
        (actualMetricDensity p) =
      (- (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
          (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ)))) *
            D (literalKB (K := K) p) -
        (LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) * (4 * T (p : ℤ) - 11) +
          LaurentPolynomial.C (1 / 9 : K) * (4 * T (-(p : ℤ)) - 11)) *
          (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
            D (actualAK (K := K) p).toLaurent -
        LaurentPolynomial.C (25 / 18 : K) *
          (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
            D (invert (actualAK (K := K) p).toLaurent) +
        LaurentPolynomial.C (55 / 24 : K) * T (p : ℤ) *
          (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
            D (invert (actualAK (K := K) p).toLaurent) +
        (-LaurentPolynomial.C (1 / 6 : K) * (4 * T (-(p : ℤ)) - 11) * T (-1) *
          (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent)) := by
  have hm : WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
      (actualHandMetric p).toLaurent =
        2 * (ActualGreenResidue.CMK (K := K) p).toLaurent := by
    simp only [actualHandMetric, WPActualChiSource.coefficientMap_toLaurent,
      map_ofNat, map_mul, ActualGreenResidue.CMK]
  simp only [actualMetricDensity, map_add, map_sub, map_mul, map_neg,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    map_div₀, map_one, map_ofNat, metric_D_coefficientMap,
    coefficientMap_literalKB, WPActualChiSource.coefficientMap_invert,
    actual_metric_AK_coefficientMap, hm]

/-- The metric density is the original R52 Green row after the joint odd-source correction.
This source identity precedes its residue and retains the full origin logarithm. -/
theorem actual_metric_green_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
        (-(1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) *
            D (literalKB (K := K) p) +
          LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) * D (actualR52 (K := K) p) -
          LaurentPolynomial.C (5 / 9 : K) * D (invert (actualAK (K := K) p).toLaurent)) -
      LaurentPolynomial.C (1 / 3 : K) *
        (2 * (ActualGreenResidue.CMK (K := K) p).toLaurent) *
        (4 * T (-(p : ℤ)) - 11) *
        (LaurentPolynomial.C (1 / 2 : K) * T (-1) +
          LaurentPolynomial.C (1 / 3 : K) * D (actualAK (K := K) p).toLaurent) =
      WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)
        (actualMetricDensity p) := by
  let m : K[T;T⁻¹] := 2 * (ActualGreenResidue.CMK (K := K) p).toLaurent
  let A := (actualAK (K := K) p).toLaurent
  have hR : D (actualR52 (K := K) p) =
      -(4 * T (-(p : ℤ)) - 11) * D (invert A) -
        (4 * T (p : ℤ) - 11) * D A := by
    have hplus : D (T (p : ℤ) : K[T;T⁻¹]) = 0 := by
      have h := D_monomial (1 : K) (p : ℤ)
      simpa only [map_one, one_mul, Int.cast_natCast, CharP.cast_eq_zero,
        map_zero, zero_mul] using h
    have hminus : D (T (-(p : ℤ)) : K[T;T⁻¹]) = 0 := by
      have h := D_monomial (1 : K) (-(p : ℤ))
      simpa only [map_one, one_mul, Int.cast_neg, Int.cast_natCast,
        CharP.cast_eq_zero, neg_zero, map_zero, zero_mul] using h
    have h4 : D (4 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (4 : K)
    have h11 : D (11 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (11 : K)
    simp only [actualR52, map_sub, map_neg, D_mul, hplus, hminus, h4, h11,
      zero_mul, mul_zero, zero_add, sub_zero]
    dsimp only [A]
    ring
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (5 / 24 : K) * 4 + 5 / 9 = 25 / 18 :=
    NativeClosureMetricRationalIdentities.euler_reciprocal_coefficient h2 h3
  have h55 : (11 : K) * (5 / 24) = 55 / 24 := by ring
  have hh9 : (1 / 3 : K) * (1 / 3) = 1 / 9 :=
    NativeClosureMetricRationalIdentities.third_square_coefficient h3
  have hh6 : (1 / 3 : K) * (1 / 2) = 1 / 6 :=
    NativeClosureMetricRationalIdentities.third_half_coefficient h2 h3
  have hc25 := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h25
  have hc55 := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) h55
  have hc9 := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hh9
  have hc6 := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hh6
  simp only [map_add, map_mul, map_ofNat] at hc25 hc55 hc9 hc6
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  rw [hR, actual_metric_density_native_source]
  change m * _ - LaurentPolynomial.C (1 / 3 : K) * m * _ * _ = _
  linear_combination
    -4 * m * LaurentPolynomial.C (5 / 24 : K) * D (invert A) * ht -
      m * D (invert A) * hc25 + m * T (p : ℤ) * D (invert A) * hc55 -
      m * (4 * T (-(p : ℤ)) - 11) * D A * hc9 -
      m * (4 * T (-(p : ℤ)) - 11) * T (-1) * hc6

/-- The actual conic and metric contributions are collected before their common Gauss value.
The metric origin is canceled by its full collector, while all three conic pole slots remain. -/
theorem actual_joint_metric_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originPole (threePhaseConicDensity p (actualGreenPC p) +
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * actualMetricDensity p) =
      -(1213 / 750 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 := by
  rw [originPole_add, originPole_cleared p hp,
    actual_joint_conic_gauss_value p hp, actual_metric_density_gauss_value p hp]
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  calc
    -6 * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 / 125 +
        (-(1177 / 750 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2) =
      -(6 / 125 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 -
        (1177 / 750 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 := by ring
    _ = _ := NativeClosureMetricRationalIdentities.joint_gauss_coefficient
      h2 h3 h5 (WPActualGaussBottom.fieldHarmonic p (p / 6))

/-- The complete original joint metric contribution reaches the faithful native field. -/
theorem actual_joint_metric_coefficientMap_value {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (g : ZMod p →+* K) :
    originPole (WPActualChiSource.coefficientMap g
      (threePhaseConicDensity p (actualGreenPC p) +
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * actualMetricDensity p)) =
      -(1213 / 750 : K) * g (WPActualGaussBottom.fieldHarmonic p (p / 6)) ^ 2 := by
  rw [metric_originPole_coefficientMap, actual_joint_metric_origin p hp]
  simp only [map_mul, map_neg, map_div₀, map_ofNat, map_pow]

end WPFieldAssembly.ActualBpairContraction
