import WPFieldAssembly.NativeClosureReflectionPhase

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2000000

variable {K : Type*} [Field K]

theorem native_zeta_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (ActualChiEndpoints.zeta (K := K) p) = ActualChiEndpoints.zeta p := by
  rw [native_zeta_phase p hp]
  simp only [WPFiniteZSource.phase, map_mul, map_sub, map_ofNat, invert_C,
    invert_T, neg_neg]
  ring

/-- Actual reflected defects fix the whole P sum; matching derivatives would not suffice. -/
theorem actual_P_reflection_fixed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteZSource.P (K := K) p u + invert (WPFiniteZSource.P p u) =
      -LaurentPolynomial.C (3 / 5 : K) * ActualChiEndpoints.zeta p *
        ((WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent +
          invert (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent) := by
  let n : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  let f := (ActualThreePhase.fK (K := K) p hp).toLaurent
  let P := WPFiniteZSource.P (K := K) p u
  let B := (ActualThreePhase.CBK (K := K) p).toLaurent
  let Bv := T n * invert B
  let Dsym := (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent +
    invert (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent
  let z := ActualChiEndpoints.zeta (K := K) p
  let a := LaurentPolynomial.C (3 / 5 : K)
  have hz : invert z = z := native_zeta_reflection (K := K) p hp
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hcoef : a * LaurentPolynomial.C (5 / 3 : K) = 1 := by
    dsimp only [a]
    rw [← map_mul]
    have h : (3 / 5 : K) * (5 / 3) = 1 := by field_simp [h3, h5]
    rw [h, map_one]
  have hc := ActualGreenResidue.actual_chi_finite_P (K := K) p hp u hu
  change ActualThreePhase.χK p hp = f * P + z * B at hc
  have hcr : T n * invert (ActualThreePhase.χK (K := K) p hp) =
      f * invert P + z * Bv := by
    rw [hc]
    simp only [map_add, map_mul, hz]
    have hf := actual_fK_SB72_reflection (K := K) p hp
    change f = T n * invert f at hf
    dsimp only [Bv]
    linear_combination -(invert P) * hf
  have ha := actual_chiK_SB72_anti (K := K) p hp
  change ActualThreePhase.χK p hp + T n * invert (ActualThreePhase.χK p hp) = 0 at ha
  rw [hcr, hc] at ha
  have hD := actual_Dstar_reciprocal_sum (K := K) p hp u hu
  change f * Dsym = LaurentPolynomial.C (5 / 3 : K) * (B + Bv) at hD
  have he : f * (P + invert P + a * z * Dsym) = 0 := by
    linear_combination ha + (a * z) * hD + z * (B + Bv) * hcoef
  have hf : f ≠ 0 := by
    intro hz
    have hpz : ActualThreePhase.fK (K := K) p hp = 0 :=
      Polynomial.toLaurent_injective (by simpa only [map_zero] using hz)
    have h := (ActualGreenResidue.actual_native_pullback_facts (K := K) p hp).2.1
    rw [hpz, eval_zero] at h
    exact zero_ne_one h
  have hs := (mul_eq_zero.mp he).resolve_left hf
  change P + invert P = -a * z * Dsym
  linear_combination hs

/-- The full added-point p phase is retained before the original kernel cancellation. -/
theorem native_added_point_phase (p : ℕ) [Fact p.Prime] [CharP K p] :
    (4 - 11 * T 1 : K[T;T⁻¹]) ^ p * T (-(p : ℤ)) = 4 * T (-(p : ℤ)) - 11 := by
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
  have he : (4 - 11 * T 1 : K[T;T⁻¹]) ^ p = 4 - 11 * T (p : ℤ) := by
    change (LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T 1) ^ p =
      LaurentPolynomial.C (4 : K) - LaurentPolynomial.C (11 : K) * T (p : ℤ)
    rw [sub_pow_char, mul_pow, ← map_pow, h4, ← map_pow, h11, ht1]
  rw [he, sub_mul, mul_assoc, ht, mul_one]

/-- IR65's kernel is normalized by the actual P reflection, with no CM inverse. -/
theorem actual_KSigma_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ p *
        (-LaurentPolynomial.C (2 / 5 : K) * (4 * T (-(p : ℤ)) - 11) *
          ((WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent +
            invert (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent)) =
      2 * (4 - 11 * T 1) ^ p *
        (WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u)) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : (3 / 5 : K) * (1 / 3) * 2 = 2 / 5 := by
    field_simp [h3]
  have hL := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
  simp only [map_mul, map_ofNat] at hL
  rw [actual_P_reflection_fixed p hp u hu, ActualChiEndpoints.zeta]
  have hphase := native_added_point_phase (K := K) p
  linear_combination
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ p *
      ((WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent +
        invert (WPFieldAssembly.ActualBpairContraction.Dstar p : K[X]).toLaurent) *
      (LaurentPolynomial.C (2 / 5 : K) * hphase +
        (4 - 11 * T 1) ^ p * T (-(p : ℤ)) * hL)

end WPFieldAssembly.ActualBpairContraction
