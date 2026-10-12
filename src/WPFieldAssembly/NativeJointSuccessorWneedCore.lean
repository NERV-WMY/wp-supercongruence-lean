import WPFieldAssembly.NativeJointSuccessorCBMixed
import WPFieldAssembly.ActualBpairLowHBranchTail

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial HahnSeries

namespace WPFieldAssembly.NativeJointSuccessorWneedCore

open ActualBpairContraction ActualBpairLowHLocalPole NativeClosureMixedSource
open NativeJointSuccessorJSeries NativeJointSuccessorCBMixed
open WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The whole symmetric factor cancels the original branch denominator of j. -/
noncomputable def actualSymJCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) *
    WPFiniteWSource.squaredCoordinate.toLaurent * (branchPolynomial p).toLaurent *
      mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)

private theorem squared_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hinj : Function.Injective
      (localFiniteSeriesHom : K[T;T⁻¹] →+* LaurentSeries K) := by
    intro F G he
    ext j
    exact congrArg (fun Q : LaurentSeries K => Q.coeff j) he
  intro hz
  have hpz : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent = 0 :=
    hinj (hz.trans (map_zero _).symm)
  have hp0 : (WPFiniteWSource.squaredCoordinate : K[X]) = 0 :=
    Polynomial.toLaurent_injective (hpz.trans (map_zero _).symm)
  have hc := congrArg (fun P : K[X] => P.coeff 1) hp0
  have he : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [he, Polynomial.coeff_zero] at hc
  exact inv_ne_zero h5 hc

theorem actual_Dsym_J_Laurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (Dsym p : K[T;T⁻¹]) * actualJSeries p =
      localFiniteSeriesHom (actualSymJCarrier p) := by
  rw [lowH_Dsym_full_branch_factor p hp]
  unfold actualJSeries actualSymJCarrier
  simp only [map_mul, map_pow, pow_succ]
  field_simp [squared_series_ne_zero (K := K) p hp]

/-- This is the original corrected IR63b delta, including its reciprocal even term. -/
noncomputable def actualDeltaSeries (p : ℕ) [Fact p.Prime] [CharP K p] : LaurentSeries K :=
  (2 / 5 : LaurentSeries K) * localFiniteSeriesHom (Dsym p : K[T;T⁻¹]) * actualJSeries p +
    (2 / 3 : LaurentSeries K) * localFiniteSeriesHom (Dstar p : K[X]).toLaurent *
      localFiniteSeriesHom (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))

noncomputable def actualDeltaCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 5 : K) * actualSymJCarrier p +
    LaurentPolynomial.C (2 / 3 : K) * (Dstar p : K[X]).toLaurent *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))

theorem actual_delta_Laurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualDeltaSeries p : LaurentSeries K) = localFiniteSeriesHom (actualDeltaCarrier p) := by
  unfold actualDeltaSeries actualDeltaCarrier
  simp only [map_add, map_mul, localFiniteSeries_C, map_div₀, map_ofNat]
  linear_combination (2 / 5 : LaurentSeries K) * actual_Dsym_J_Laurent (K := K) p hp

/-- Differentiation transports the entire delta carrier, including invisible p slots. -/
theorem actual_delta_derivative_Laurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentSeries.derivative K (actualDeltaSeries p : LaurentSeries K) =
      localFiniteSeriesHom (D (actualDeltaCarrier p)) := by
  have hd : localFiniteSeriesHom (D (actualDeltaCarrier p : K[T;T⁻¹])) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (actualDeltaCarrier p : K[T;T⁻¹]) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (actualDeltaCarrier p)
  rw [actual_delta_Laurent p hp]
  exact hd.symm

/-- The three native Wneed terms precede the separately owned weighted HF source. -/
noncomputable def actualWneedCoreSeries (p : ℕ) [Fact p.Prime] [CharP K p] : LaurentSeries K :=
  actualDeltaSeries p * localFiniteSeriesHom (33 - 12 * T 1) -
    localFiniteSeriesHom (WPFiniteZSource.Abar : K[X]).toLaurent *
      localFiniteSeriesHom (ActualGreenResidue.HpullK (K := K) p).toLaurent *
      LaurentSeries.derivative K (actualDeltaSeries p) +
    localFiniteSeriesHom (ActualThreePhase.CBK (K := K) p).toLaurent *
      actualDeltaBSeries p * localFiniteSeriesHom (33 - 12 * T 1)

noncomputable def actualWneedCoreCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  actualDeltaCarrier p * (33 - 12 * T 1) -
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (ActualGreenResidue.HpullK (K := K) p).toLaurent * D (actualDeltaCarrier p) +
      actualCBDeltaBLCarrier p

theorem actual_Wneed_core_Laurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (actualWneedCoreSeries p : LaurentSeries K) =
      localFiniteSeriesHom (actualWneedCoreCarrier p) := by
  unfold actualWneedCoreSeries actualWneedCoreCarrier
  rw [actual_delta_derivative_Laurent p hp, actual_delta_Laurent p hp,
    actual_CB_DeltaB_L_Laurent p hp]
  simp only [map_add, map_sub, map_mul]

end WPFieldAssembly.NativeJointSuccessorWneedCore
