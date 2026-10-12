import WPFieldAssembly.ActualCubicSourceAttachment
import WPFieldAssembly.ActualSB72Attachment

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteAffineLog WPFiniteCubicLog WPFiniteKSource WPFiniteABSourceTail
  WPFieldAssembly.ActualCubicSourceAttachment
  WPFieldAssembly.ActualBpairContraction
open LaurentPolynomial (T invert invert_C invert_T)

namespace WPFieldAssembly.ActualCubicNativeSource

variable {K : Type*} [Field K]

/-- The harmonic term is the original native value mapped to the same field. -/
theorem actual_harmonic_map (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFieldAssembly.ActualThreePhase.φ (K := K) p)
      (WPActualGaussBottom.fieldHarmonic p (p / 6)) = (WPFiniteNC122.h p : K) := by
  rw [actual_harmonic_is_finite_h p hp]
  simp only [WPFiniteNC122.h, WPFiniteNC122.q, map_sub, map_neg, map_mul,
    map_ofNat, map_div₀, map_intCast]

noncomputable def nativeConstant (p : ℕ) : K :=
  3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
    11 * WPFiniteNC122.q p / 5 - WPFiniteNC122.h p

/-- The genuine native origin is the same cubic a0, including its fifth carrier. -/
theorem actual_AK_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (actualAK p : K[X]).eval 0 = WPFiniteNC122.a0 p u := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc : (WPFiniteJHighCoefficient.conic : K[X]).eval u = 0 := by
    simp only [WPFiniteJHighCoefficient.conic, eval_sub, eval_mul, eval_ofNat,
      eval_pow, eval_X, eval_one, hu, mul_one_div_cancel h5, sub_self]
  have ht : (WPFiniteCubicLog.Tc : K[X]).eval u = WPFiniteNC122.T0 u := by
    have hu3 : u ^ 3 = (1 / 5 : K) * u := by
      calc
        u ^ 3 = u ^ 2 * u := by ring
        _ = _ := by rw [hu]
    simp only [WPFiniteCubicLog.Tc, eval_sub, eval_mul, eval_ofNat,
      eval_pow, eval_X, hu3, WPFiniteNC122.T0]
    field_simp [h5]
    ring
  have hL := congrArg (fun P : K[X] => P.eval u) (WPFiniteLVSource.LV_conic p hp)
  rw [eval_comp, hc, eval_comp, ht] at hL
  rw [actual_AK_source p hp, actual_harmonic_map p hp, eval_sub, eval_C, hL]
  simp only [LPsrc, eval_add, eval_C, EP, eval_mul, eval_comp, eval_neg,
    eval_X, WPFiniteAffineLog.LP_eval_eq, WPFiniteNC122.a0, WPFiniteNC122.L,
    WPFiniteField.E, div_eq_mul_inv]
  ring

/-- NC126a belongs to the original native polynomial, before any tail projection. -/
theorem actual_AK_two_band (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK p : K[X]) =
      X ^ p * (C (12 / 5 : K) * Dstar p - C (4 * WPFiniteNC122.q p / 5)) -
        C (33 / 5 : K) * Dstar p + C (2 / 5 : K) * logTrace p + C (nativeConstant p) := by
  rw [actual_AK_source p hp, actual_harmonic_map p hp, LV_two_band_source p hp]
  simp only [nativeConstant, C_sub]
  ring

/-- The whole positive Laurent source retains its Frobenius phase and its origin. -/
theorem actual_AK_Laurent_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK p : K[X]).toLaurent =
      T (p : ℤ) * (LaurentPolynomial.C (12 / 5 : K) * (Dstar p).toLaurent -
        LaurentPolynomial.C (4 * WPFiniteNC122.q p / 5)) -
      LaurentPolynomial.C (33 / 5 : K) * (Dstar p).toLaurent +
      LaurentPolynomial.C (2 / 5 : K) * (logTrace p).toLaurent +
      LaurentPolynomial.C (nativeConstant p) := by
  simpa only [map_add, map_sub, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X_pow] using
      congrArg (Polynomial.toLaurent : K[X] → K[T;T⁻¹]) (actual_AK_two_band p hp)

/-- The reciprocal source is derived from the same complete native polynomial. -/
theorem actual_AK_reciprocal_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    invert (actualAK p : K[X]).toLaurent =
      T (-(p : ℤ)) * (LaurentPolynomial.C (12 / 5 : K) * invert (Dstar p).toLaurent -
        LaurentPolynomial.C (4 * WPFiniteNC122.q p / 5)) -
      LaurentPolynomial.C (33 / 5 : K) * invert (Dstar p).toLaurent +
      LaurentPolynomial.C (2 / 5 : K) * invert (logTrace p).toLaurent +
      LaurentPolynomial.C (nativeConstant p) := by
  simpa only [map_add, map_sub, map_mul, invert_C, invert_T] using
    congrArg invert (actual_AK_Laurent_source (K := K) p hp)

/-- Squaring the actual source retains the full shifted band before projection. -/
theorem actual_AK_square_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (actualAK p : K[X]) ^ 2 =
      X ^ (2 * p) * (C (12 / 5 : K) * Dstar p - C (4 * WPFiniteNC122.q p / 5)) ^ 2 +
      2 * X ^ p * (C (12 / 5 : K) * Dstar p - C (4 * WPFiniteNC122.q p / 5)) *
        (C (nativeConstant p) - C (33 / 5 : K) * Dstar p + C (2 / 5 : K) * logTrace p) +
      (C (nativeConstant p) - C (33 / 5 : K) * Dstar p + C (2 / 5 : K) * logTrace p) ^ 2 := by
  rw [actual_AK_two_band p hp]
  have hx : (X : K[X]) ^ (2 * p) = (X ^ p) ^ 2 := by
    rw [Nat.mul_comm 2 p, pow_mul]
  rw [hx]
  ring

end WPFieldAssembly.ActualCubicNativeSource
