import WPFieldAssembly.ActualBpairLowHWholeAlgebra
import WPFieldAssembly.ActualCubicNativeSource
import WPFieldAssembly.NativeClosureLowHLog

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualCubicNativeSource

namespace WPFieldAssembly.NativeClosureLowH

variable {K : Type*} [Field K]
set_option maxHeartbeats 2200000

/- STATEMENT_FIDELITY: The H and u below are the original terminating Euler
carrier and the actualLogMinusH pullback, mapped from ZMod p. No arbitrary
native-u premise is supplied. The reciprocal is the full signed Laurent
source. This is a source attachment for IR71, not an evaluation of the full
nativeRemainder or the all-prime scalar. -/

noncomputable def nativeH (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (ActualLowEuler.actualH p).map (ActualThreePhase.φ p)

theorem actualH_eq_nativeHField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualLowEuler.actualH p = NativeEulerPrimitive.nativeHField p := by
  rw [ActualLowEuler.actualH, ActualLowEuler.actualF_eq_native p hp,
    NativeEulerPrimitive.nativeHField]
  ext n
  rw [ActualR0Node.unitEuler_coeff, WPActualPositivePair.eulerPrimitive_coeff]
  by_cases hn : n < p
  · rw [if_pos hn]
  · rw [if_neg hn, WPActualNativeHasse.nativeField_coeff,
      if_neg (by omega : ¬ n < p / 6 + 1), zero_div]

theorem nativeH_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (nativeH (K := K) p).natDegree ≤ p / 6 := by
  calc
    _ ≤ (ActualLowEuler.actualH p).natDegree := Polynomial.natDegree_map_le
    _ ≤ p / 6 := ActualLowEuler.actualH_degree p hp

theorem nativeH_origin (p : ℕ) [Fact p.Prime] [CharP K p] :
    (nativeH (K := K) p).coeff 0 = 0 := by
  simp [nativeH, ActualLowEuler.actualH, ActualR0Node.unitEuler_coeff]

theorem nativeH_original_Hpull (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    lowHCubicY (nativeH (K := K) p) = ActualGreenResidue.HpullK p := by
  rw [lowHCubicY, nativeH, actualH_eq_nativeHField p hp,
    ActualGreenResidue.HpullK, ActualGreenResidue.Hpull, Polynomial.map_comp]
  congr 1
  rw [← ActualLowEuler.Qrev_eq_fieldV p, WPFiniteNC122Residue.Qrev_factored]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one,
    Polynomial.map_ofNat, map_inv₀, map_ofNat]
  rw [WPFiniteNC122Residue.VP]
  ring

/-- The original native positive carrier is identified before any residue or p-division. -/
theorem native_u_affine (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK (K := K) p).toLaurent =
      LaurentPolynomial.C (3 / 5 : K) * (4 * T (p : ℤ) - 11) * (Dstar p).toLaurent +
      LaurentPolynomial.C (2 / 5 : K) *
        (4 * (lowHLog p 4).toLaurent -
          LaurentPolynomial.C (1 / 4 : K) * (lowHLog p (1 / 4)).toLaurent) +
      LaurentPolynomial.C (nativeConstant p) -
      LaurentPolynomial.C (4 * WPFiniteNC122.q p / 5) * T (p : ℤ) := by
  rw [actual_AK_Laurent_source p hp]
  have hlogs : (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent =
      4 * (lowHLog p 4).toLaurent -
        LaurentPolynomial.C (1 / 4 : K) * (lowHLog p (1 / 4)).toLaurent := by
    simp only [WPFiniteABSourceTail.logTrace, lowHLog, div_eq_mul_inv,
      map_add, map_mul, map_neg, map_ofNat, Polynomial.toLaurent_C,
      one_mul, inv_inv]
    ring
  rw [hlogs]
  simp only [map_mul, map_ofNat, div_eq_mul_inv]
  ring

/-- The second source is the actual reciprocal of the same complete native polynomial. -/
theorem native_v_affine (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (actualAK (K := K) p).toLaurent =
      LaurentPolynomial.C (3 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
        invert (Dstar p).toLaurent +
      LaurentPolynomial.C (2 / 5 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) +
      LaurentPolynomial.C (nativeConstant p) -
      LaurentPolynomial.C (4 * WPFiniteNC122.q p / 5) * T (-(p : ℤ)) := by
  have hi := actual_AK_reciprocal_source (K := K) p hp
  have hlog : invert (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent =
      T (-(p : ℤ)) * ((lowHLog p 4).toLaurent -
        (lowHLog p (1 / 4)).toLaurent) := by
    exact native_log_pair_inversion p hp
  rw [hi, hlog]
  simp only [map_mul, map_ofNat, div_eq_mul_inv]
  ring

/-- Both native derivatives are paired with the complete actual y/Abar source. -/
theorem native_u_density (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * D (actualAK (K := K) p).toLaurent =
      LaurentPolynomial.C (3 / 5 : K) * (4 * T (p : ℤ) - 11) *
        ((lowHCubicY H).toLaurent * D (Dstar p).toLaurent) -
      LaurentPolynomial.C (1 / 2 : K) * (lowHqCubicDensity H).toLaurent -
      LaurentPolynomial.C (3 / 2 : K) * (4 * T (p : ℤ) - 11) *
        (lowHBranchYQuotient H).toLaurent := by
  have hA := actual_AK_cleared_derivative (K := K) p hp
  have hD := congrArg (fun P : K[X] => P.toLaurent) (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_one, map_pow, Polynomial.toLaurent_C,
    ← D_toLaurent] at hD
  rw [lowHBranchYQuotient_source H h0, map_mul, lowH_linear_ylog_polynomial]
  simp only [map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 / 5 : K) * (5 / 2) = 3 / 2 := by field_simp [h5]
  have hcL := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul] at hcL
  have hhalf : LaurentPolynomial.C (1 / 2 : K) * 3 =
      LaurentPolynomial.C (3 / 2 : K) := by
    change LaurentPolynomial.C (1 / 2 : K) * LaurentPolynomial.C (3 : K) = _
    rw [← map_mul]; congr 1; ring
  linear_combination (lowHBranchYQuotient H).toLaurent * hA -
    LaurentPolynomial.C (3 / 5 : K) * (4 * T (p : ℤ) - 11) *
      (lowHBranchYQuotient H).toLaurent * hD -
    (4 * T (p : ℤ) - 11) * (lowHBranchYQuotient H).toLaurent *
      (1 - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) * hcL -
    (4 * T 1 - 11) * (lowHBranchYQuotient H).toLaurent * hhalf

end WPFieldAssembly.NativeClosureLowH
