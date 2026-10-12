import WPFieldAssembly.NativeJointSuccessorActualPhase
import WPFieldAssembly.NativeJointSuccessorMixedPrimitive
import WPFieldAssembly.NativeClosureReflectionSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorOddSource

open ActualBpairContraction NativeClosureMixedSource NativeJointSuccessorActualPhase
open ActualCubicNativeSource WPFiniteLaurentDifferential
open NativeJointSuccessorMixedPrimitive GreenLaurentOperators

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The numerator of the original reciprocal cubic logarithmic derivative.
Its denominator is s*(4-11x); no branch is deleted. -/
noncomputable def oddLogCleared : K[T;T⁻¹] :=
  LaurentPolynomial.C (3 / 10 : K) * T (-1) * (T 1 - 4)

/-- The complete odd density after multiplication by s^(N+1)*Abar. -/
noncomputable def oddDensityCleared (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (3 / 2 : K) * T (-(((p - 1) / 2 : ℕ) : ℤ)) *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ (2 * ((p - 1) / 2) + 1) *
      frobeniusPhi p ^ 2 -
    LaurentPolynomial.C (75 / 2 : K) * T ((((p - 1) / 2 + 1 : ℕ) : ℤ))

/-- The full normalized primitive cancels the original logarithmic branch denominator. -/
noncomputable def oddLogLaurentCarrier (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (3 / 2 : K) * DD (-1) (-1) (calL p) *
    T (-(p : ℤ) - 1) * (4 - 11 * T 1) ^ (p - 1) * (T 1 - 4)

theorem actual_calL_log_Laurent_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    WPFiniteWSource.squaredCoordinate.toLaurent * (4 - 11 * T 1) *
      (oddLogLaurentCarrier p : K[T;T⁻¹]) = calL p * frobeniusPhi p * oddLogCleared := by
  have hd := DD_identity (-1 : K) (neg_ne_zero.mpr one_ne_zero) (calL p)
  simp only [inv_neg, inv_one, map_neg, map_one, calL_branch_origin, map_zero,
    sub_zero, sub_neg_eq_add] at hd
  have hphase := native_added_point_phase (K := K) p
  have ht : (T (-1) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
    omega
  have hf : (T (-(p : ℤ) - 1) * (4 - 11 * T 1) ^ p : K[T;T⁻¹]) =
      T (-1) * frobeniusPhi p := by
    rw [← ht]
    rw [mul_assoc, mul_comm (T (-(p : ℤ))), hphase]
    rfl
  have hpw : (4 - 11 * T 1 : K[T;T⁻¹]) ^ p =
      (4 - 11 * T 1) ^ (p - 1) * (4 - 11 * T 1) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have hc : LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) =
      LaurentPolynomial.C (3 / 10 : K) := by
    rw [← map_mul]
    congr 1
    field_simp [h2, h5, h10]
    ring
  have hs : WPFiniteWSource.squaredCoordinate.toLaurent =
      LaurentPolynomial.C (1 / 5 : K) * (T 1 + 1) := by
    simp only [WPFiniteWSource.squaredCoordinate, map_mul, Polynomial.toLaurent_C,
      map_add, Polynomial.toLaurent_X, map_one, one_div]
  unfold oddLogLaurentCarrier oddLogCleared
  rw [hs]
  calc
    _ = (LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K)) *
        ((T 1 + 1) * DD (-1) (-1) (calL p)) *
          (T (-(p : ℤ) - 1) * (4 - 11 * T 1) ^ p) * (T 1 - 4) := by
      rw [hpw]
      ring
    _ = _ := by rw [hc, hd, hf]; ring

/-- Frobenius and the full reciprocal cubic factor identify the actual log term. -/
theorem actual_odd_log_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentPolynomial.C (75 / 2 : K) * T (2 - (p : ℤ)) *
        (4 - 11 * T 1) ^ (p - 1) * (4 - 11 * T 1) -
      WPFiniteWSource.squaredCoordinate.toLaurent * frobeniusPhi p *
        LaurentPolynomial.C (3 / 2 : K) * (4 * T (-1) - 11) * (4 - 11 * T 1) =
      -frobeniusPhi p * oddLogCleared * (WPFiniteZSource.Abar : K[X]).toLaurent := by
  let x : K[T;T⁻¹] := T 1
  let xi : K[T;T⁻¹] := T (-1)
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have hx : x * xi = 1 := by dsimp [x, xi]; rw [← T_add]; norm_num
  have hwp : (4 - 11 * T 1 : K[T;T⁻¹]) ^ p = T (p : ℤ) * frobeniusPhi p := by
    have he := native_added_point_phase (K := K) p
    change (4 - 11 * T 1) ^ p * T (-(p : ℤ)) = frobeniusPhi p at he
    have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
      rw [← T_add]; simp
    linear_combination T (p : ℤ) * he - (4 - 11 * T 1) ^ p * ht
  have hf : (T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) *
      (4 - 11 * T 1) : K[T;T⁻¹]) = x ^ 2 * frobeniusPhi p := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), hwp,
      ← mul_assoc, ← T_add]
    dsimp [x]
    rw [T_pow]
    norm_num
  have hc : LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) =
      LaurentPolynomial.C (3 / 10 : K) := by
    rw [← map_mul]
    congr 1
    field_simp [h2, h5, h10]
    ring
  have h75 : LaurentPolynomial.C (75 / 2 : K) =
      LaurentPolynomial.C (3 / 10 : K) * 125 := by
    change LaurentPolynomial.C (75 / 2 : K) =
      LaurentPolynomial.C (3 / 10 : K) * LaurentPolynomial.C (125 : K)
    rw [← map_mul]
    congr 1
    field_simp [h2, h10]
    ring
  rw [show LaurentPolynomial.C (75 / 2 : K) * T (2 - (p : ℤ)) *
      (4 - 11 * T 1) ^ (p - 1) * (4 - 11 * T 1) =
        LaurentPolynomial.C (75 / 2 : K) *
          (T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) * (4 - 11 * T 1))
    by ring, hf]
  have hs : WPFiniteWSource.squaredCoordinate.toLaurent =
      LaurentPolynomial.C (1 / 5 : K) * (x + 1) := by
    simp only [WPFiniteWSource.squaredCoordinate, map_mul, Polynomial.toLaurent_C,
      map_add, Polynomial.toLaurent_X, map_one, one_div, x]
  have ha : (WPFiniteZSource.Abar : K[X]).toLaurent = (4 - x) * (4 * x - 1) := by
    simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one, x]
  rw [hs, ha, h75]
  unfold oddLogCleared
  change _ = -frobeniusPhi p * (LaurentPolynomial.C (3 / 10 : K) * xi * (x - 4)) *
    ((4 - x) * (4 * x - 1))
  dsimp [x, xi] at *
  linear_combination (norm := ring_nf)
    -frobeniusPhi p * (T 1 + 1) * (4 * T (-1) - 11) * (4 - 11 * T 1) * hc +
      LaurentPolynomial.C (3 / 10 : K) * frobeniusPhi p *
        (-4 * (T 1) ^ 2 + 77 * T 1 - 44) * hx

/-- The SAME full residual has the odd/log/native derivative split before residues. -/
theorem actual_J_full_odd_log_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
        (WPFiniteWSource.squaredCoordinate.toLaurent *
          D (mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) +
          LaurentPolynomial.C (1 / 10 : K) *
            mixedResidual p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) *
        (4 - 11 * T 1) =
      oddDensityCleared p * (4 - 11 * T 1) -
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          frobeniusPhi p * oddLogCleared * (WPFiniteZSource.Abar : K[X]).toLaurent +
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
          frobeniusPhi p * LaurentPolynomial.C (1 / 3 : K) *
            ((WPFiniteZSource.Abar : K[X]).toLaurent * D (actualAK p : K[X]).toLaurent) *
          (4 - 11 * T 1) := by
  have hr := actual_R_cleared_source (K := K) p hp
  have ha := actual_AK_cleared_derivative (K := K) p hp
  have ho := actual_odd_log_cleared_source (K := K) p hp
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : LaurentPolynomial.C (1 / 3 : K) * LaurentPolynomial.C (3 / 2 : K) =
      LaurentPolynomial.C (1 / 2 : K) := by
    rw [← map_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul]
    rw [← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  unfold oddDensityCleared
  have hpow : (WPFiniteWSource.squaredCoordinate.toLaurent : K[T;T⁻¹]) ^
      (2 * ((p - 1) / 2) + 1) =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) := by
    rw [show 2 * ((p - 1) / 2) + 1 = ((p - 1) / 2 + 1) + ((p - 1) / 2) by omega,
      pow_add]
  rw [hpow]
  linear_combination (norm := ring_nf)
    (4 - 11 * T 1) * hr +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * ho -
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
        frobeniusPhi p * LaurentPolynomial.C (1 / 3 : K) * (4 - 11 * T 1) * ha -
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) * frobeniusPhi p *
        ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (p : ℤ) - 11)) * (4 - 11 * T 1) * hc

end WPFieldAssembly.NativeJointSuccessorOddSource
