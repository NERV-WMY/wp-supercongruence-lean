import WPFieldAssembly.NativeJointSuccessorHCollector
import WPFieldAssembly.ActualChiEndpoints
import WPFieldAssembly.ActualSB72Attachment

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource

namespace WPFieldAssembly.NativeJointSuccessorEndCollector

open ActualBpairContraction ActualGreenResidue ActualThreePhase GreenLaurentOperators
  NativeClosureLowH ActualBpairLowHLocalPole
  NativeJointSuccessorRroot NativeJointSuccessorScalarSource NativeJointSuccessorHCollector

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: original P(1/4)=q and P(4)=-q determine
the original marked endpoint density, before any residue. The whole
harmonic cancellation uses the actual cleared P and AK derivatives and
all original Frobenius phases. GB retains chi0; the root slot remains
P-A/3 and its conversion is used exactly once. Neither the endpoint nor
the remaining mixed CM/HF density is replaced by a scalar premise. -/

private theorem series_two_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (2 : LaurentSeries K) ≠ 0 := by
  change HahnSeries.C (2 : K) ≠ 0
  exact HahnSeries.C_ne_zero (WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega)))

private theorem series_three_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (3 : LaurentSeries K) ≠ 0 := by
  change HahnSeries.C (3 : K) ≠ 0
  exact HahnSeries.C_ne_zero (WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega)))

/-- Both original proper ends determine the SAME whole marked endpoint source. -/
theorem actual_marked_endpoint_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    actualMarkedEndpointSource p u h4 =
      -LaurentPolynomial.C (WPFiniteNC122.q p) * (31 - 4 * T 1) := by
  have hP := ActualChiEndpoints.finite_P_endpoints (K := K) p hp u
  have ha : ev (1 / 4) (one_div_ne_zero h4) (WPFiniteZSource.P p u) = WPFiniteNC122.q p := by
    have hu : Units.mk0 (1 / 4 : K) (one_div_ne_zero h4) =
        (ActualChiEndpoints.fourUnit (K := K) p hp)⁻¹ := by
      apply Units.ext
      simp [ActualChiEndpoints.fourUnit, one_div]
    unfold ev
    rw [hu]
    exact hP.2
  have hb : ev 4 h4 (WPFiniteZSource.P p u) = -WPFiniteNC122.q p := by
    have hu : Units.mk0 (4 : K) h4 = ActualChiEndpoints.fourUnit (K := K) p hp := by
      apply Units.ext
      rfl
    unfold ev
    rw [hu]
    exact hP.1
  have hquarter : (4 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 4 : K) = 1 := by
    change LaurentPolynomial.C (4 : K) * LaurentPolynomial.C (1 / 4 : K) = 1
    rw [← map_mul, mul_one_div_cancel h4, map_one]
  rw [actualMarkedEndpointSource, ha, hb, map_neg]
  linear_combination LaurentPolynomial.C (WPFiniteNC122.q p) * hquarter

/-- The original P derivative is cleared with its positive, origin and negative phases intact. -/
theorem actual_P_cleared_endpoint_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (WPFiniteZSource.P p u) =
      LaurentPolynomial.C (1 / 2 : K) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (-4 * T (p : ℤ) + 17 - 4 * T (-(p : ℤ))) -
        LaurentPolynomial.C (1 / 2 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent * T (-1) := by
  rw [WPFiniteZSource.P_derivative p hp u, mul_sub, WPFiniteZSource.R_cleared p hp]
  dsimp only [WPFiniteZSource.phase]
  ring

/-- The one chi0 conversion changes the source origin while leaving its actual derivative equal. -/
theorem actual_chi0_root_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    D (originalChi0 p u) = D (originalRootChi p u) := by
  have he := congrArg D (actual_root_chi0_conversion (K := K) p u)
  simp only [map_add, D_C, add_zero] at he
  exact he.symm

/-- Original endpoint, harmonic and root derivative terms cancel as one complete Laurent source. -/
theorem actual_harmonic_endpoint_cancellation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (h4 : (4 : K) ≠ 0) :
    -6 * LaurentPolynomial.C (WPFiniteNC122.h p) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (1 - LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ))) * literalKB p +
      LaurentPolynomial.C (WPFiniteNC122.h p) * (WPFiniteZSource.Abar : K[X]).toLaurent *
        literalKB p * T (-1) +
      2 * LaurentPolynomial.C (WPFiniteNC122.h p) * (WPFiniteZSource.Abar : K[X]).toLaurent *
        literalKB p * D (originalRootChi p u) -
      (LaurentPolynomial.C (WPFiniteNC122.h p / 3) * (33 - 12 * T 1) +
        LaurentPolynomial.C (WPFiniteNC122.q p) * (31 - 4 * T 1) +
        actualMarkedEndpointSource p u h4) * literalKB p = 0 := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  have hfC (c : K) : f (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c :=
    localFiniteSeries_C c
  have h2S := series_two_ne_zero (K := K) p hp
  have h3S := series_three_ne_zero (K := K) p hp
  have hP := congrArg f (actual_P_cleared_endpoint_derivative (K := K) p hp u)
  have hA := congrArg f (actual_AK_cleared_derivative (K := K) p hp)
  have hE := congrArg f (actual_marked_endpoint_source (K := K) p hp u h4)
  apply lowH_whole_finiteSeries_injective
  change f _ = f 0
  dsimp only [originalRootChi]
  simp only [D_C_mul, map_mul, map_add, map_sub, map_neg, map_ofNat,
    map_zero, map_one, hfC, map_div₀] at hP hA hE ⊢
  linear_combination (norm := (simp only [hfC]; field_simp [h2S, h3S]; ring))
    (2 * f (LaurentPolynomial.C (WPFiniteNC122.h p)) * f (literalKB p)) * hP -
      (2 * f (LaurentPolynomial.C (WPFiniteNC122.h p)) * f (literalKB p) / 3) * hA -
      f (literalKB p) * hE

/-- The endpoint reduction leaves exactly the original CM/proper metric and complete quadratic eQ sources. -/
noncomputable def actualEndComplementSource (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  let eQ := invert (actualAK (K := K) p).toLaurent -
    LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p)
  let d := (Dstar p : K[X]).toLaurent
  let sN := WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2);
  -(WPFiniteZSource.Abar : K[X]).toLaurent * actualIR63B0 p * D (CMK (K := K) p).toLaurent -
    LaurentPolynomial.C (1 / 3 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
      coefficientMap (φ (K := K) p) (properMetricDensity p) +
    LaurentPolynomial.C (10 * WPFiniteNC122.h p / 3) * sN * eQ -
    LaurentPolynomial.C (2 / 3 : K) * d * eQ * (33 - 12 * T 1)

/-- The SAME original GB and G2 cancel from the actual non-H root density without pole values. -/
theorem actual_root_nonH_GB_G2_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    rootNonHDensity p hp u - originalGBDensity p u - originalG2Density p u =
      actualEndComplementSource (K := K) p := by
  let f : K[T;T⁻¹] →+* LaurentSeries K := localFiniteSeriesHom
  have hfC (c : K) : f (LaurentPolynomial.C c) = algebraMap K (LaurentSeries K) c :=
    localFiniteSeries_C c
  have h2S := series_two_ne_zero (K := K) p hp
  have h3S := series_three_ne_zero (K := K) p hp
  have h4S : (4 : LaurentSeries K) ≠ 0 := by
    convert pow_ne_zero 2 h2S using 1
    norm_num
  have h12S : (12 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero h4S h3S using 1
    norm_num
  have h24S : (24 : LaurentSeries K) ≠ 0 := by
    convert mul_ne_zero (mul_ne_zero h4S h2S) h3S using 1
    norm_num
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hV : actualRootUniversalV p u =
      -literalKB p * originalRootChi p u +
        LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) * actualZ52 p u := by
    dsimp only [actualRootUniversalV, originalRootChi]
    ring
  have hv := congrArg f hV
  have hχ := congrArg f (actual_root_chi0_conversion (K := K) p u)
  have he := congrArg f (actual_harmonic_endpoint_cancellation (K := K) p hp u h4)
  apply lowH_whole_finiteSeries_injective
  change f _ = f _
  dsimp only [rootNonHDensity, originalCBMetricBranch, originalGBDensity,
    originalG2Density, actualEndComplementSource, actualIR63B0]
  rw [actual_chi0_root_derivative p u]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero,
    map_one, hfC, map_div₀] at hv hχ he ⊢
  linear_combination (norm := (simp only [map_mul, map_sub, map_ofNat]; field_simp [h2S, h3S, h4S, h12S, h24S]; ring))
    f (33 - 12 * T 1) * hv -
      (f (33 - 12 * T 1) * f (literalKB p)) * hχ + he

/-- The previous remaining collector is reduced to the disjoint mixed j/HF/CM source obligation. -/
theorem actual_remaining_original_end_reduction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    remainingOriginalCollector p hp u =
      mixedHCompletionDensity p u + actualEndComplementSource p -
        (NativeClosureMixedSource.mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p) +
          originalJointMetricDensity p) := by
  rw [actual_remaining_original_H_reduction p hp u]
  linear_combination actual_root_nonH_GB_G2_collection (K := K) p hp u

end WPFieldAssembly.NativeJointSuccessorEndCollector
