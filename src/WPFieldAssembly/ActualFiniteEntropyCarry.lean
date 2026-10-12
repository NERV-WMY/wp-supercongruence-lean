import WPFiniteCarry.FiniteProduct
import WPFiniteEntropy

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualFiniteEntropyCarry

set_option maxHeartbeats 1000000

/-- Every unit factor of the literal binomial row, including its last factor. -/
noncomputable def fullProductQ (p r : ℕ) : ℚ :=
  ∏ k ∈ Finset.range r, (1 - (p : ℚ) / ((k + 1 : ℕ) : ℚ))

noncomputable def fullHarmonicQ (r : ℕ) : ℚ :=
  ∑ k ∈ Finset.range r, 1 / ((k + 1 : ℕ) : ℚ)

noncomputable def fullProductIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  ∏ k ∈ Finset.range r, (1 - (p : integralRationals p) * smallIntegralInverse p (k + 1))

noncomputable def fullHarmonicIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ k ∈ Finset.range r, smallIntegralInverse p (k + 1)

noncomputable def fullProductRemainder (p : ℕ) [Fact p.Prime] : ℕ → integralRationals p
  | 0 => 0
  | r + 1 => fullProductRemainder p r +
      fullHarmonicIntegral p r * smallIntegralInverse p (r + 1) -
      (p : integralRationals p) * fullProductRemainder p r * smallIntegralInverse p (r + 1)

theorem fullProductIntegral_firstTaylor (p r : ℕ) [Fact p.Prime] :
    fullProductIntegral p r = 1 - (p : integralRationals p) * fullHarmonicIntegral p r +
      (p : integralRationals p)^2 * fullProductRemainder p r := by
  induction r with
  | zero => simp [fullProductIntegral, fullHarmonicIntegral, fullProductRemainder]
  | succ r ih =>
    simp only [fullProductIntegral, Finset.prod_range_succ] at ih ⊢
    rw [ih]
    simp only [fullHarmonicIntegral, Finset.sum_range_succ, fullProductRemainder]
    ring

theorem fullHarmonicIntegral_value (p r : ℕ) [Fact p.Prime] (hr : r < p) :
    (fullHarmonicIntegral p r).val = fullHarmonicQ r := by
  change (integralRationals p).subtype (fullHarmonicIntegral p r) = _
  rw [fullHarmonicIntegral, map_sum, fullHarmonicQ]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr := Finset.mem_range.mp hk
  exact smallIntegralInverse_value p (k + 1) (by omega) (by omega)

theorem fullProductIntegral_value (p r : ℕ) [Fact p.Prime] (hr : r < p) :
    (fullProductIntegral p r).val = fullProductQ p r := by
  change (integralRationals p).subtype (fullProductIntegral p r) = _
  rw [fullProductIntegral, map_prod, fullProductQ]
  apply Finset.prod_congr rfl
  intro k hk
  have hkr := Finset.mem_range.mp hk
  rw [map_sub, map_one, map_mul, map_natCast]
  change 1 - (p : ℚ) * (smallIntegralInverse p (k + 1)).val = _
  rw [smallIntegralInverse_value p (k + 1) (by omega) (by omega)]
  ring

theorem signed_pred_choose_product (p r : ℕ) [Fact p.Prime] (hr : r < p) :
    (-1 : ℚ)^r * ((p - 1).choose r : ℚ) = fullProductQ p r := by
  induction r with
  | zero => simp [fullProductQ]
  | succ r ih =>
    have hi := ih (by omega)
    have hnat := Nat.choose_succ_right_eq (p - 1) r
    have h := congrArg (fun n : ℕ => (n : ℚ)) hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : r ≤ p - 1),
      Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_add, Nat.cast_one] at h
    have hu : (r : ℚ) + 1 ≠ 0 := by positivity
    have hc : ((p - 1).choose (r + 1) : ℚ) =
        ((p - 1).choose r : ℚ) * ((p : ℚ) - 1 - r) / ((r : ℚ) + 1) :=
      (eq_div_iff hu).mpr h
    have hfactor : ((p : ℚ) - 1 - r) / ((r : ℚ) + 1) =
        (p : ℚ) / ((r : ℚ) + 1) - 1 := by
      field_simp [hu]
      ring
    rw [pow_succ, hc]
    simp only [fullProductQ, Finset.prod_range_succ]
    simp only [fullProductQ] at hi
    rw [← hi]
    push_cast
    rw [mul_div_assoc, hfactor]
    ring

/-- The coefficient of the actual rational even entropy before any residue map. -/
noncomputable def entropyCoefficientQ (p j : ℕ) : ℚ :=
  -(p.choose (2 * j) : ℚ) / (p : ℚ)

theorem entropyCoefficient_product (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : 2 * j < p) :
    entropyCoefficientQ p j = fullProductQ p (2 * j - 1) / ((2 * j : ℕ) : ℚ) := by
  have hmul := Nat.add_one_mul_choose_eq (p - 1) (2 * j - 1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    Nat.sub_add_cancel (by omega : 1 ≤ 2 * j)] at hmul
  have hm := congrArg (fun n : ℕ => (n : ℚ)) hmul
  push_cast at hm
  have ho : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  have hs := signed_pred_choose_product p (2 * j - 1) (by omega)
  rw [ho.neg_one_pow] at hs
  rw [← hs]
  unfold entropyCoefficientQ
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hj0 : ((2 * j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * j ≠ 0)
  simp only [neg_one_mul]
  apply (div_eq_div_iff hp0 hj0).mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  linear_combination hm

theorem entropyCoefficient_firstTaylor (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : 2 * j < p) :
    entropyCoefficientQ p j = 1 / ((2 * j : ℕ) : ℚ) -
      (p : ℚ) * fullHarmonicQ (2 * j - 1) / ((2 * j : ℕ) : ℚ) +
      (p : ℚ)^2 * (fullProductRemainder p (2 * j - 1)).val / ((2 * j : ℕ) : ℚ) := by
  rw [entropyCoefficient_product p j hj hjp]
  have h := congrArg (integralRationals p).subtype
    (fullProductIntegral_firstTaylor p (2 * j - 1))
  simp only [map_add, map_sub, map_mul, map_one, map_natCast, map_pow,
    fullHarmonicIntegral_value p (2 * j - 1) (by omega),
    fullProductIntegral_value p (2 * j - 1) (by omega),
    Subring.subtype_apply] at h
  rw [h]
  ring

/-- The first carry is the prescribed rational difference divided by p. -/
noncomputable def entropyCoefficientCarryQ (p j : ℕ) : ℚ :=
  (1 / ((2 * j : ℕ) : ℚ) - entropyCoefficientQ p j) / (p : ℚ)

noncomputable def entropyCoefficientCarryIntegral (p j : ℕ) [Fact p.Prime] :
    integralRationals p :=
  (fullHarmonicIntegral p (2 * j - 1) -
    (p : integralRationals p) * fullProductRemainder p (2 * j - 1)) *
      smallIntegralInverse p (2 * j)

theorem entropyCoefficientCarryIntegral_value (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : 2 * j < p) :
    (entropyCoefficientCarryIntegral p j).val = entropyCoefficientCarryQ p j := by
  change (integralRationals p).subtype (entropyCoefficientCarryIntegral p j) = _
  rw [entropyCoefficientCarryIntegral, map_mul, map_sub, map_mul, map_natCast]
  simp only [Subring.subtype_apply]
  rw [
    fullHarmonicIntegral_value p (2 * j - 1) (by omega),
    smallIntegralInverse_value p (2 * j) (by omega) hjp]
  unfold entropyCoefficientCarryQ
  rw [entropyCoefficient_firstTaylor p j hj hjp]
  field_simp [show (p : ℚ) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero]
  ring

/-- The field reduction retains the full H_(2j-1)/(2j), including j=N. -/
theorem entropyCoefficientCarryIntegral_field (p j : ℕ) [Fact p.Prime]
    (hj : 0 < j) (hjp : 2 * j < p) :
    residueHom p (entropyCoefficientCarryIntegral p j) =
      (∑ k ∈ Finset.range (2 * j - 1), ((k + 1 : ℕ) : ZMod p)⁻¹) /
        ((2 * j : ℕ) : ZMod p) := by
  rw [entropyCoefficientCarryIntegral, map_mul, map_sub, map_mul, map_natCast,
    ZMod.natCast_self, zero_mul, sub_zero,
    smallIntegralInverse_field p (2 * j) (by omega) hjp]
  congr 1
  rw [fullHarmonicIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr := Finset.mem_range.mp hk
  exact smallIntegralInverse_field p (k + 1) (by omega) (by omega)

end WPFieldAssembly.ActualFiniteEntropyCarry
