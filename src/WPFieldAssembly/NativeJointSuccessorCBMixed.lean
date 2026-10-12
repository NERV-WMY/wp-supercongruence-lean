import WPFieldAssembly.NativeJointSuccessorJSeries
import WPFieldAssembly.NativeClosureCBBranch

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorCBMixed

open ActualBpairContraction ActualBpairLowHLocalPole NativeClosureMixedSource
open NativeJointSuccessorJSeries NativeQuadraticInverse

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The quotient is extracted from the actual mapped PB source, before any residue. -/
noncomputable def actualCBBranchQuotient (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  Polynomial.C (1 / 25 : K) * (4 * X - 11) *
    ((quadraticInverse (ActualFirstGreen.B p).divX).map (ActualThreePhase.φ p)).comp
      ((WPHasseIntegralTransport.fieldV p).map (ActualThreePhase.φ p))

theorem actual_CBK_full_branch_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualThreePhase.CBK (K := K) p) =
      WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2 + 1) * actualCBBranchQuotient p := by
  have he := actual_CB_mapped_PB_source p hp (ActualThreePhase.φ (K := K) p)
  change ActualThreePhase.CBK (K := K) p = _ at he
  rw [he]
  unfold actualCBBranchQuotient
  ring

/-- The full CB times j is an actual Laurent carrier, including every residual phase. -/
noncomputable def actualCBJCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  WPFiniteWSource.squaredCoordinate.toLaurent * (actualCBBranchQuotient p).toLaurent *
    mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)

theorem actual_CB_J_Laurent (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (ActualThreePhase.CBK (K := K) p).toLaurent * actualJSeries p =
      localFiniteSeriesHom (actualCBJCarrier p) := by
  let N := (p - 1) / 2
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hS : S ≠ 0 := by
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
    have hcoef : (WPFiniteWSource.squaredCoordinate : K[X]).coeff 1 = (5 : K)⁻¹ := by
      simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
    rw [hcoef, Polynomial.coeff_zero] at hc
    exact inv_ne_zero h5 hc
  rw [actual_CBK_full_branch_factor p hp]
  simp only [map_mul, map_pow]
  unfold actualJSeries actualCBJCarrier
  simp only [map_mul]
  change S ^ (N + 1) * localFiniteSeriesHom (actualCBBranchQuotient p).toLaurent *
      (localFiniteSeriesHom
          (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) / S ^ N) =
    S * localFiniteSeriesHom (actualCBBranchQuotient p).toLaurent *
      localFiniteSeriesHom
        (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
  rw [pow_succ]
  field_simp [pow_ne_zero N hS]

noncomputable def actualDeltaBSeries (p : ℕ) [Fact p.Prime] [CharP K p] : LaurentSeries K :=
  -(2 / 3 : LaurentSeries K) * actualJSeries p -
    (10 / 9 : LaurentSeries K) * localFiniteSeriesHom
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))

/-- Only the whole weighted DeltaB product is asserted Laurent. -/
noncomputable def actualCBDeltaBLCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  (-LaurentPolynomial.C (2 / 3 : K) * actualCBJCarrier p -
    LaurentPolynomial.C (10 / 9 : K) * (ActualThreePhase.CBK (K := K) p).toLaurent *
      (invert (actualAK p).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))) * (33 - 12 * T 1)

theorem actual_CB_DeltaB_L_Laurent (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (ActualThreePhase.CBK (K := K) p).toLaurent *
        actualDeltaBSeries p * localFiniteSeriesHom (33 - 12 * T 1) =
      localFiniteSeriesHom (actualCBDeltaBLCarrier p) := by
  unfold actualCBDeltaBLCarrier actualDeltaBSeries
  simp only [map_mul, map_sub, map_neg, localFiniteSeries_C, map_div₀, map_ofNat]
  have hj := actual_CB_J_Laurent (K := K) p hp
  linear_combination -(2 / 3 : LaurentSeries K) *
    (33 - 12 * localFiniteSeriesHom (T 1 : K[T;T⁻¹])) * hj

end WPFieldAssembly.NativeJointSuccessorCBMixed
