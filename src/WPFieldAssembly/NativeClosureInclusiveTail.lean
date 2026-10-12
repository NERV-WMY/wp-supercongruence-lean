import WPFieldAssembly.ActualBpairMixedTail

open scoped Polynomial LaurentPolynomial BigOperators
open Polynomial WPFiniteAffineLog WPFiniteProductTail
open LaurentPolynomial (T)

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- The whole band at or above p, including the coefficient at p, shifted down by p. -/
noncomputable def inclusivePositive (p : ℕ) (P : K[X]) : K[X] :=
  LaurentPolynomial.trunc (T (-(p : ℤ)) * P.toLaurent)

theorem inclusivePositive_coeff (p : ℕ) (P : K[X]) (j : ℕ) :
    (inclusivePositive p P).coeff j = P.coeff (p + j) := by
  rw [inclusivePositive, WPFiniteJWeightedResidue.trunc_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) (j : ℤ) P.toLaurent
  simp only [map_one, one_mul] at hs
  rw [hs, show (j : ℤ) - -(p : ℤ) = ((p + j : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]

theorem inclusivePositive_strict_origin (p : ℕ) (P : K[X]) :
    inclusivePositive p P = fullStrictPositive p 1 P.toLaurent + C (P.coeff p) := by
  rw [fullStrictPositive, one_mul, WPFiniteJCarrier.toLaurent_coeff_nat]
  change inclusivePositive p P = inclusivePositive p P - C (P.coeff p) + C (P.coeff p)
  ring

/-- Literal reversal includes the diagonal p term; its denominator becomes -i. -/
theorem inclusive_log_product_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (c : K) (hc : c ≠ 0) :
    (W * (LP p).comp (C c * X)).coeff p =
      -(c ^ p) * originPrimitive p W c⁻¹ := by
  let W0 : K[X] := W - C (W.coeff 0)
  let L : K[X] := (LP p).comp (C c * X)
  have hp := (Fact.out : p.Prime).pos
  have hW0 : W0.natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hW (by simpa using hp))
  have hW00 : W0.coeff 0 = 0 := by simp [W0]
  have hci (i : ℕ) (hi : i ∈ Finset.Ico 1 p) : W0.coeff i = W.coeff i := by
    simp only [W0, coeff_sub, coeff_C]
    rw [if_neg (show i ≠ 0 by have := (Finset.mem_Ico.mp hi).1; omega), sub_zero]
  have he : W * L = W0 * L + C (W.coeff 0) * L := by dsimp only [W0]; ring
  have hlp : L.coeff p = 0 := by
    dsimp only [L]
    rw [LP_scaled_coeff, if_neg (by omega : ¬ (1 ≤ p ∧ p < p))]
  rw [he, coeff_add, coeff_C_mul, hlp, mul_zero, add_zero,
    W_full_cutoff p W0 hW0 hW00, Finset.sum_mul, finsetSum_coeff]
  rw [originPrimitive, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hit := (Finset.mem_Ico.mp hi).2
  have hir : p - i ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by
    have := (Finset.mem_Ico.mp hi).1
    omega)
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]
  dsimp only [L]
  rw [LP_scaled_coeff, if_pos (Finset.mem_Ico.mp hir), hci i hi,
    div_eq_mul_inv, reversed_unit p i hi]
  have hpow : c ^ (p - i) = c ^ p * (c⁻¹) ^ i := by
    rw [pow_sub₀ c hc (by omega), ← inv_pow]
  rw [hpow]
  ring

/-- The full >=p tail is the whole finite primitive, with no origin subtraction. -/
theorem inclusive_log_product_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (c : K) (hc : c ≠ 0) (z : K) :
    (inclusivePositive p (W * (LP p).comp (C c * X))).eval z =
      -(c ^ p) * unitPrimitive p W z c⁻¹ := by
  rw [inclusivePositive_strict_origin, eval_add, eval_C,
    fullStrictPositive_log_product_value p W hW c hc z,
    inclusive_log_product_diagonal p W hW c hc]
  ring

/-- Restoring the original p phase preserves both actual Frobenius factors. -/
theorem inclusive_log_high_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (c : K) (hc : c ≠ 0) (z : K) :
    z ^ p * (inclusivePositive p (W * (LP p).comp (C c * X))).eval z =
      -((c * z) ^ p) * unitPrimitive p W z c⁻¹ := by
  rw [inclusive_log_product_value p W hW c hc z, mul_pow]
  ring

/-- The SB107f field reduction applies only after the original full tail is attached. -/
theorem inclusive_log_high_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (c : K) (hc : c ≠ 0) (z : K)
    (hcp : c ^ p = c) (hzp : z ^ p = z) :
    z ^ p * (inclusivePositive p (W * (LP p).comp (C c * X))).eval z =
      -(c * z) * unitPrimitive p W z c⁻¹ := by
  rw [inclusive_log_high_value p W hW c hc z, mul_pow, hcp, hzp]

end WPFieldAssembly.ActualBpairContraction
