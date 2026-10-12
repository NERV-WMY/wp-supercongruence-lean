import WPFieldAssembly.NativeJointSuccessorCBMixed
import WPFieldAssembly.NativeJointSuccessorRroot
import WPFieldAssembly.NativeClosureMetricCarrier

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential

namespace WPFieldAssembly.NativeJointSuccessorCMPrimitive

open ActualBpairContraction ActualGreenResidue ActualThreePhase NativeQuadraticInverse
  ActualBpairLowHLocalPole NativeClosureMixedSource NativeJointSuccessorJSeries
  NativeJointSuccessorCBMixed NativeJointSuccessorRroot

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: the actual PM factor of the SAME CMK is mapped
as a complete polynomial. Its s^(N+1) factor cancels only the s^N
denominator of the full original j. The whole mixedResidual retains all
odd and reciprocal native phases. CMhand=2*CMK remains literal. The
full CMK*(B0+DeltaB) carrier supplies the original total derivative;
there is no component pole value or independent CM normalization. -/

/-- The checked actual PM factor maps to any characteristic-p field as a whole polynomial source. -/
theorem actual_CM_mapped_PM_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (g : ZMod p →+* K) :
    (ActualFirstGreen.CM p).map g = Polynomial.C (1 / 50 : K) *
      (WPFiniteWSource.squaredCoordinate : K[X]) ^ (((p - 1) / 2) + 1) * (4 * X - 11) *
      ((quadraticInverse (ActualFirstGreen.M p).divX).map g).comp
        ((WPHasseIntegralTransport.fieldV p).map g) := by
  have hs : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).map g =
      (WPFiniteWSource.squaredCoordinate : K[X]) := by
    simp only [WPFiniteWSource.squaredCoordinate, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, map_inv₀, map_ofNat]
  have he := congrArg (fun P : (ZMod p)[X] => P.map g) (actual_CM_PM_source p hp)
  simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_comp, map_div₀, map_one, map_ofNat, hs] using he

/-- This quotient keeps the original coefficient 1/50 and the SAME mapped PM(V). -/
noncomputable def actualCMBranchQuotient (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  Polynomial.C (1 / 50 : K) * (4 * X - 11) *
    ((quadraticInverse (ActualFirstGreen.M p).divX).map (φ p)).comp
      ((WPHasseIntegralTransport.fieldV p).map (φ p))

/-- The actual CMK retains its entire original s^(N+1) branch factor. -/
theorem actual_CMK_full_branch_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    CMK (K := K) p = WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2 + 1) *
      actualCMBranchQuotient p := by
  have he := actual_CM_mapped_PM_source (K := K) p hp (φ p)
  change CMK (K := K) p = _ at he
  rw [he]
  dsimp only [actualCMBranchQuotient]
  ring

/-- The mapped human metric remains exactly twice the actual Lean CMK. -/
theorem actual_CMhand_half_scale (p : ℕ) [Fact p.Prime] [CharP K p] :
    (actualHandMetric p).map (φ (K := K) p) = Polynomial.C (2 : K) * CMK p := by
  change (Polynomial.C (2 : ZMod p) * ActualFirstGreen.CM p).map (φ p) =
    Polynomial.C (2 : K) * (ActualFirstGreen.CM p).map (φ p)
  rw [Polynomial.map_mul, Polynomial.map_C, map_ofNat]

private theorem squared_series_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  intro hz
  have hc := congrArg (fun Q : LaurentSeries K => Q.coeff 1) hz
  change (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent.coeff 1 = 0 at hc
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent.coeff 1 = (5 : K)⁻¹ := by
    change (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent.coeff ((1 : ℕ) : ℤ) = _
    rw [WPFiniteJCarrier.toLaurent_coeff_nat]
    simp [WPFiniteWSource.squaredCoordinate, Polynomial.coeff_one]
  rw [hs] at hc
  exact inv_ne_zero h5 hc

/-- The full CMK times j is the actual finite Laurent source, with no residual phase omitted. -/
noncomputable def actualCMJCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  WPFiniteWSource.squaredCoordinate.toLaurent * (actualCMBranchQuotient p).toLaurent *
    mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)

theorem actual_CM_J_Laurent (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (CMK (K := K) p).toLaurent * actualJSeries p =
      localFiniteSeriesHom (actualCMJCarrier p) := by
  let N := (p - 1) / 2
  let S : LaurentSeries K := localFiniteSeriesHom WPFiniteWSource.squaredCoordinate.toLaurent
  have hS : S ≠ 0 := squared_series_ne_zero (K := K) p hp
  rw [actual_CMK_full_branch_factor p hp]
  simp only [map_mul, map_pow]
  unfold actualJSeries actualCMJCarrier
  simp only [map_mul]
  change S ^ (N + 1) * localFiniteSeriesHom (actualCMBranchQuotient p).toLaurent *
      (localFiniteSeriesHom
          (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) / S ^ N) =
    S * localFiniteSeriesHom (actualCMBranchQuotient p).toLaurent *
      localFiniteSeriesHom
        (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))
  rw [pow_succ]
  field_simp [pow_ne_zero N hS]

/-- Derivative transport uses this same full weighted j carrier. -/
theorem actual_CM_J_derivative_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (D (actualCMJCarrier (K := K) p)) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (CMK (K := K) p).toLaurent *
          actualJSeries (K := K) p : LaurentSeries K) := by
  rw [actual_CM_J_Laurent p hp]
  exact lowHFiniteSeries_derivative (actualCMJCarrier p)

/-- The complete original CMK*(B0+DeltaB) is retained as one actual finite primitive. -/
noncomputable def actualCMBnewCarrier (p : ℕ) [Fact p.Prime] [CharP K p] : K[T;T⁻¹] :=
  (CMK (K := K) p).toLaurent * actualIR63B0 p -
    LaurentPolynomial.C (2 / 3 : K) * actualCMJCarrier p -
    LaurentPolynomial.C (10 / 9 : K) * (CMK (K := K) p).toLaurent *
      (invert (actualAK p : K[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p - WPFiniteNC122.h p))

/-- This expression is the SAME actual Bnew series used by the complete Green collector. -/
theorem actual_CM_Bnew_Laurent (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    localFiniteSeriesHom (CMK (K := K) p).toLaurent *
        (localFiniteSeriesHom (actualIR63B0 p) + actualDeltaBSeries p) =
      localFiniteSeriesHom (actualCMBnewCarrier p) := by
  unfold actualCMBnewCarrier actualDeltaBSeries
  simp only [map_mul, map_sub, localFiniteSeries_C, map_div₀, map_ofNat]
  have hj := actual_CM_J_Laurent (K := K) p hp
  linear_combination -(2 / 3 : LaurentSeries K) * hj

/-- The derivative of the full CMK*Bnew product is the derivative of its actual finite primitive. -/
theorem actual_CM_Bnew_derivative_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (D (actualCMBnewCarrier (K := K) p)) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (CMK (K := K) p).toLaurent *
          (localFiniteSeriesHom (actualIR63B0 p) + actualDeltaBSeries p) : LaurentSeries K) := by
  rw [actual_CM_Bnew_Laurent p hp]
  exact lowHFiniteSeries_derivative (actualCMBnewCarrier p)

/-- Product differentiation keeps the entire original B0 and DeltaB derivatives together. -/
theorem actual_CM_Bnew_derivative_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    localFiniteSeriesHom (D (actualCMBnewCarrier (K := K) p)) =
      localFiniteSeriesHom (D (CMK (K := K) p).toLaurent) *
          (localFiniteSeriesHom (actualIR63B0 p) + actualDeltaBSeries p) +
        localFiniteSeriesHom (CMK (K := K) p).toLaurent *
          (localFiniteSeriesHom (D (actualIR63B0 p)) +
            LaurentSeries.derivative K (actualDeltaBSeries (K := K) p : LaurentSeries K)) := by
  have hdB0 : localFiniteSeriesHom (D (actualIR63B0 p : K[T;T⁻¹])) =
      LaurentSeries.derivative K
        (localFiniteSeriesHom (actualIR63B0 p : K[T;T⁻¹]) : LaurentSeries K) :=
    lowHFiniteSeries_derivative (actualIR63B0 p : K[T;T⁻¹])
  rw [actual_CM_Bnew_derivative_transport p hp, finite_series_derivative_product]
  rw [map_add, ← hdB0]

/-- The cleared derivative of this actual finite primitive has zero origin pole by its coefficient. -/
theorem actual_CM_Bnew_total_derivative_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ActualSimplePoleResidue.originPole
      ((WPFiniteZSource.Abar : K[X]).toLaurent * D (actualCMBnewCarrier p)) = 0 := by
  rw [ActualSimplePoleResidue.originPole_cleared p hp, D_coeff]
  norm_num

end WPFieldAssembly.NativeJointSuccessorCMPrimitive
