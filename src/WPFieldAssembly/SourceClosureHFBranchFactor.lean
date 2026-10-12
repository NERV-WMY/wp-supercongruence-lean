import WPFieldAssembly.ActualBpairLowHBranchTail
import Mathlib.Algebra.CharP.Algebra

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
  WPFieldAssembly.ActualBpairContraction

namespace WPFieldAssembly.SourceClosureHFNativeTransport

set_option maxHeartbeats 1600000

/- STATEMENT_FIDELITY: cancel the original added-point and branch factors
   in Abar*KSigma*dlog(sqrt(x)*Tvee). The quotient below is a literal
   Laurent polynomial, retaining the complete branchPolynomial and both
   Frobenius phases. This supplies the Laurent membership needed by Wneed;
   it does not identify or evaluate the full HF/common-trace source. -/

variable {K : Type*} [Field K]

noncomputable def nativeZlogNumerator : K[T;T⁻¹] := -11 * T 2 - 4 * T 1 - 8

noncomputable def nativeZlogDenominator : K[T;T⁻¹] :=
  2 * T 1 * (T 1 + 1) * (4 - 11 * T 1)

noncomputable def nativeKSigma (p : ℕ) : K[T;T⁻¹] :=
  -LaurentPolynomial.C (2 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
    ((Dstar p : K[X]).toLaurent + invert (Dstar p : K[X]).toLaurent)

noncomputable def nativeHFSigmaNumerator (p : ℕ) : K[T;T⁻¹] :=
  -LaurentPolynomial.C (1 / 25 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
    nativeZlogNumerator * (4 - 11 * T 1) ^ (p - 1) *
    T (-(p : ℤ) - (((p - 1) / 2 : ℕ) : ℤ)) *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
    (branchPolynomial p).toLaurent

/-- The original logarithmic denominator is nonzero without a Hasse-root premise. -/
theorem nativeZlogDenominator_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (nativeZlogDenominator : K[T;T⁻¹]) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h2L : (2 : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have he : (2 : K[X]) = 0 := Polynomial.toLaurent_injective
      (by simpa only [map_ofNat, map_zero] using hz)
    have hc := congrArg (fun P : K[X] => P.coeff 0) he
    exact h2 (by simpa using hc)
  have hx : (T 1 : K[T;T⁻¹]) ≠ 0 := by
    have ht : (T 1 * T (-1) : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
    intro hz
    rw [hz, zero_mul] at ht
    exact zero_ne_one ht
  have hm : (T 1 + 1 : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have he : (X + 1 : K[X]) = 0 := Polynomial.toLaurent_injective
      (by simpa only [map_add, Polynomial.toLaurent_X, map_one, map_zero] using hz)
    have hc := congrArg (fun P : K[X] => P.coeff 1) he
    simp [Polynomial.coeff_one] at hc
  have hb : (4 - 11 * T 1 : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have he : (4 - 11 * X : K[X]) = 0 := Polynomial.toLaurent_injective
      (by simpa only [map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X, map_zero] using hz)
    have hc := congrArg (fun P : K[X] => P.coeff 0) he
    exact h4 (by simpa using hc)
  unfold nativeZlogDenominator
  exact mul_ne_zero (mul_ne_zero
    (mul_ne_zero h2L hx) hm) hb

/-- The complete HF Sigma quotient is Laurent before taking any residue. -/
theorem actual_HF_sigma_Laurent_clearing (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    nativeZlogDenominator * nativeHFSigmaNumerator p =
      (WPFiniteZSource.Abar : K[X]).toLaurent * nativeKSigma p * nativeZlogNumerator := by
  let N := (p - 1) / 2
  let s := (WPFiniteWSource.squaredCoordinate : K[X]).toLaurent
  let B : K[T;T⁻¹] := 4 - 11 * T 1
  let beta := (branchPolynomial p : K[X]).toLaurent
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 * 5 by ring]
    exact mul_ne_zero h5 h5
  have hscalar : -2 * LaurentPolynomial.C (1 / 25 : K) * 5 =
      -LaurentPolynomial.C (2 / 5 : K) := by
    have he : (-2 : K) * (1 / 25) * 5 = -(2 / 5) := by
      field_simp [h5, h25]
      ring
    simpa only [map_mul, map_neg, map_ofNat] using congrArg LaurentPolynomial.C he
  have hs : (T 1 + 1 : K[T;T⁻¹]) = 5 * s := by
    dsimp only [s, WPFiniteWSource.squaredCoordinate]
    simp only [map_mul, map_add, Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_one]
    have hc : (5 : K[T;T⁻¹]) * LaurentPolynomial.C ((5 : K)⁻¹) = 1 := by
      change LaurentPolynomial.C (5 : K) * LaurentPolynomial.C ((5 : K)⁻¹) = 1
      rw [← map_mul, mul_inv_cancel₀ h5, map_one]
    rw [← mul_assoc, hc, one_mul]
  have hphase : B ^ p * T (-(p : ℤ)) = 4 * T (-(p : ℤ)) - 11 := by
    have hC : Function.Injective (LaurentPolynomial.C : K →+* K[T;T⁻¹]) := by
      intro a b hab
      have hc := congrArg (fun F : K[T;T⁻¹] => F.coeff 0) hab
      simpa only [LaurentPolynomial.C_apply, if_true] using hc
    have : CharP K[T;T⁻¹] p :=
      charP_of_injective_ringHom (f := LaurentPolynomial.C) hC p
    have h4 : (4 : K) ^ p = 4 := by
      simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
    have h11 : (11 : K) ^ p = 11 := by
      simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 11
    have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
      rw [← T_add, add_neg_cancel, T_zero]
    have ht1 : (T 1 : K[T;T⁻¹]) ^ p = T (p : ℤ) := by
      rw [T_pow]
      congr 1
      ring
    have he : B ^ p = 4 - 11 * T (p : ℤ) := by
      change (LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T 1) ^ p =
        LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T (p : ℤ)
      rw [sub_pow_char (p := p), mul_pow, ← map_pow, ← map_pow, h4, h11, ht1]
    rw [he, sub_mul, mul_assoc, ht, mul_one]
  have hD : (Dsym p : K[T;T⁻¹]) = T (1 - (N : ℤ)) * s ^ (N + 1) * beta := by
    have he := lowH_Dsym_full_branch_factor (K := K) p hp
    change Dsym p = T (-((N - 1 : ℕ) : ℤ)) * s ^ (N + 1) * beta at he
    rw [show -((N - 1 : ℕ) : ℤ) = 1 - (N : ℤ) by omega] at he
    exact he
  have ht : (T 1 * T (-(p : ℤ) - (N : ℤ)) : K[T;T⁻¹]) =
      T (-(p : ℤ)) * T (1 - (N : ℤ)) := by
    rw [← T_add, ← T_add]
    congr 1
    ring
  have hB : B * B ^ (p - 1) = B ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [nativeZlogDenominator, nativeHFSigmaNumerator, nativeKSigma]
  change (2 * T 1 * (T 1 + 1) * B) *
    (-LaurentPolynomial.C (1 / 25 : K) * (WPFiniteZSource.Abar : K[X]).toLaurent *
      nativeZlogNumerator * B ^ (p - 1) * T (-(p : ℤ) - (N : ℤ)) * s ^ N * beta) =
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (-LaurentPolynomial.C (2 / 5 : K) * (4 * T (-(p : ℤ)) - 11) * Dsym p) *
      nativeZlogNumerator
  rw [hs, hD]
  calc
    _ = (-2 * LaurentPolynomial.C (1 / 25 : K) * 5) *
        (WPFiniteZSource.Abar : K[X]).toLaurent * nativeZlogNumerator *
        (B * B ^ (p - 1)) * (T 1 * T (-(p : ℤ) - (N : ℤ))) *
        s ^ (N + 1) * beta := by rw [pow_succ]; ring
    _ = (WPFiniteZSource.Abar : K[X]).toLaurent *
        (-LaurentPolynomial.C (2 / 5 : K) * (B ^ p * T (-(p : ℤ))) *
          (T (1 - (N : ℤ)) * s ^ (N + 1) * beta)) * nativeZlogNumerator := by
      rw [hscalar, hB, ht]
      ring
    _ = _ := by rw [hphase]

end WPFieldAssembly.SourceClosureHFNativeTransport
