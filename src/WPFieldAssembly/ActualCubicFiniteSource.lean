import WPFiniteCubicLog
import WPFifthEntropy
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators Polynomial
open Polynomial WPFiniteAffineLog WPFiniteKSource WPFiniteCubicLog

namespace WPFieldAssembly.ActualCubicFiniteSource

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

private theorem LP_map {F : Type*} [Field F] (phi : K →+* F) (p : ℕ) :
    (LP p : K[X]).map phi = (LP p : F[X]) := by
  simp only [LP, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, map_inv₀, map_natCast]

private theorem EP_map {F : Type*} [Field F] (phi : K →+* F) (p : ℕ) :
    (EP p : K[X]).map phi = (EP p : F[X]) := by
  simp only [EP, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, map_inv₀,
    map_ofNat, LP_map]

private theorem OP_map {F : Type*} [Field F] (phi : K →+* F) (p : ℕ) :
    (OP p : K[X]).map phi = (OP p : F[X]) := by
  simp only [OP, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
    Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X, map_inv₀,
    map_ofNat, LP_map]

private theorem EP_value (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) :
    (EP p : K[X]).eval t = WPFiniteField.E p t := by
  simp only [EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg, eval_X,
    LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
  ring

/-- The full square logarithm identity retains its entire upper Frobenius band. -/
theorem LP_square_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LP p : K[X]).comp (X ^ 2) = 2 * EP p + 2 * X ^ p * OP p := by
  let F := AlgebraicClosure K
  let phi : K →+* F := algebraMap K F
  apply Polynomial.map_injective phi phi.injective
  simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_ofNat, LP_map,
    EP_map, OP_map]
  apply Polynomial.funext
  intro t
  simp only [eval_comp, eval_pow, eval_X, eval_add, eval_mul, eval_ofNat,
    LP_eval_eq, EP_value, OP_eval]
  have he := WPFifthEntropy.ell_square_even_odd (K := F) p hp t
  have h2 : (2 : F) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have he' : 2 * WPFiniteField.E p t + 2 * t ^ p * WPFiniteField.O p t =
      WPFiniteField.ell p (t ^ 2) := by
    calc
      _ = (WPFiniteField.E p t + t ^ p * WPFiniteField.O p t) * 2 := by ring
      _ = _ := by rw [he, div_mul_cancel₀ _ h2]
  linear_combination -he'

/-- IR69's complete cubic polynomial keeps the literal degree-2p carry. -/
theorem cubic_even_entropy_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (EP p : K[X]).comp Tc =
      (4 * (X ^ p) ^ 2 - 3) * (EP p - (EP p).comp (2 * X)) +
        2 * (LP p).comp (X ^ 2) - C (1 / 2 : K) * (LP p).comp (4 * X ^ 2) -
          C (4 * WPFiniteNC122.q p) * (X ^ p) ^ 2 := by
  have hs := LP_square_polynomial (K := K) p hp
  have hs2 := congrArg (fun Q : K[X] => Q.comp (2 * X)) hs
  have h2p : (2 : K[X]) ^ p = 2 := by
    change (C (2 : K)) ^ p = C (2 : K)
    rw [← map_pow]
    congr 1
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 2
  simp only [comp_assoc, pow_comp, X_comp, add_comp, mul_comp, ofNat_comp] at hs2
  simp only [mul_pow, h2p, show (2 : K[X]) ^ 2 = 4 by norm_num] at hs2
  have hcu := UW1_polynomial (K := K) p hp
  rw [LPsrc, add_comp, C_comp] at hcu
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hunit : (2 : K[X]) * C (1 / 2 : K) = 1 := by
    change C (2 : K) * C (1 / 2 : K) = C (1 : K)
    rw [← C_mul]
    congr 1
    field_simp [h2]
  simp only [UW1rhs, map_mul, map_ofNat] at hcu ⊢
  linear_combination hcu - 2 * hs + C (1 / 2 : K) * hs2 +
    ((EP p).comp (2 * X) + 2 * X ^ p * (OP p).comp (2 * X)) * hunit

theorem cubic_even_entropy_literal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) :
    WPFiniteField.E p (4 * t ^ 3 - 3 * t) =
      (4 * (t ^ p) ^ 2 - 3) * (WPFiniteField.E p t - WPFiniteField.E p (2 * t)) +
        2 * WPFiniteField.ell p (t ^ 2) - WPFiniteField.ell p (4 * t ^ 2) / 2 -
          4 * WPFiniteNC122.q p * (t ^ p) ^ 2 := by
  have he := congrArg (fun Q : K[X] => Q.eval t)
    (cubic_even_entropy_polynomial (K := K) p hp)
  simp only [eval_comp, Tc, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X,
    eval_add, eval_C, EP_value, LP_eval_eq] at he
  linear_combination (norm := (field_simp; ring)) he

end WPFieldAssembly.ActualCubicFiniteSource
