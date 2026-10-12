import WPMomentPrecision.BasePole.BinomialCarry
import WPMomentPrecision.BasePole.FieldContractions

open scoped Polynomial BigOperators
open Polynomial

namespace WPMomentPrecision.BasePole

theorem interior_coefficient_at_multiple {K : Type*} [CommRing K]
    (p m : ℕ) (a b : K) : (binomialInterior p a b).coeff (m * p) = 0 := by
  rw [binomialInterior_coefficient, if_neg]
  intro h
  have hmp := Finset.mem_Ico.mp h
  by_cases hm : m = 0
  · subst m
    simp at hmp
  · have hm1 : 1 ≤ m := by omega
    have hpmp : p ≤ m * p := by
      simpa only [one_mul] using Nat.mul_le_mul_right p hm1
    omega

/-- The entire coefficient convolution retains every interior index. -/
theorem product_middle_coefficient {K : Type*} [CommRing K]
    (p : ℕ) (hp : 1 ≤ p) (P Q : K[X]) (h0 : P.coeff 0 = 0)
    (hpSlot : P.coeff p = 0) :
    (P * Q).coeff p = ∑ r ∈ Finset.Ico 1 p, P.coeff r * Q.coeff (p - r) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ hp]
  simp only [Finset.sum_range_one, h0, hpSlot, zero_mul, zero_add, add_zero]

theorem actual_first_F_square_middle (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((firstFCarry p : (ZMod p)[X]) ^ 2).coeff p = 0 := by
  rw [pow_two, product_middle_coefficient p (by omega)
    _ _ (by simpa only [firstFCarry, zero_mul] using
      (interior_coefficient_at_multiple (K := ZMod p) p 0 (-1) 4))
    (by simpa only [firstFCarry, one_mul] using
      (interior_coefficient_at_multiple (K := ZMod p) p 1 (-1) 4))]
  have h := first_F_square_convolution p hp
  apply Eq.trans _ h
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p - r ∈ Finset.Ico 1 p := by
    have hri := Finset.mem_Ico.mp hr
    exact Finset.mem_Ico.mpr (by omega)
  rw [actual_firstFCarry_field_coefficient p r hp hr,
    actual_firstFCarry_field_coefficient p (p-r) hp hpr]
  rfl

theorem actual_first_FG_middle (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((firstFCarry p : (ZMod p)[X]) * firstGCarry p).coeff p =
      WPFiniteInversion.R p 16 := by
  rw [product_middle_coefficient p (by omega)
    _ _ (by simpa only [firstFCarry, zero_mul] using
      (interior_coefficient_at_multiple (K := ZMod p) p 0 (-1) 4))
    (by simpa only [firstFCarry, one_mul] using
      (interior_coefficient_at_multiple (K := ZMod p) p 1 (-1) 4))]
  have h := first_FG_convolution p hp
  apply Eq.trans _ h
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p - r ∈ Finset.Ico 1 p := by
    have hri := Finset.mem_Ico.mp hr
    exact Finset.mem_Ico.mpr (by omega)
  rw [actual_firstFCarry_field_coefficient p r (by omega) hr,
    actual_firstGCarry_field_coefficient p (p-r) (by omega) hpr]
  rfl

/-- Both constant Frobenius slots remain in the exact first-carry row. -/
theorem actual_baseFirstCarry_field_normalform (p : ℕ) [Fact p.Prime] :
    (baseFirstCarry p : (ZMod p)[X]) =
      (-8 + 34 * X ^ p - 8 * X ^ (2*p)) * firstFCarry p +
        (16 - 8 * X ^ p + X ^ (2*p)) * firstGCarry p := by
  unfold baseFirstCarry frobeniusF frobeniusG
  rw [ZMod.pow_card, C_ofNat, show 2*p=p*2 by omega, pow_mul]
  ring

/-- The whole second carry, before its resonant coefficient selection. -/
theorem actual_baseSecondCarry_field_normalform (p : ℕ) [Fact p.Prime] :
    (baseSecondCarry p : (ZMod p)[X]) =
      4 * firstFCarry p ^ 2 * X ^ p - firstFCarry p ^ 2 +
        8 * firstFCarry p * firstGCarry p - 2 * (firstFCarry p * firstGCarry p) * X ^ p := by
  unfold baseSecondCarry frobeniusF frobeniusG
  rw [ZMod.pow_card, C_ofNat]
  ring

theorem interior_product_outer {K : Type*} [CommRing K]
    (p n : ℕ) (hp : 1 ≤ p) (hn : 2*p ≤ n) (a b c d : K) :
    (binomialInterior p a b * binomialInterior p c d).coeff n = 0 := by
  have hd : (binomialInterior p a b * binomialInterior p c d).natDegree ≤
      (p-1)+(p-1) :=
    (natDegree_mul_le).trans
      (Nat.add_le_add (binomialInterior_degree p a b) (binomialInterior_degree p c d))
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem actual_first_F_square_constant {K : Type*} [CommRing K] (p : ℕ) :
    ((firstFCarry p : K[X]) ^ 2).coeff 0 = 0 := by
  simp [pow_two, mul_coeff_zero, firstFCarry, binomialInterior_coefficient]

theorem actual_first_FG_constant {K : Type*} [CommRing K] (p : ℕ) :
    ((firstFCarry p : K[X]) * firstGCarry p).coeff 0 = 0 := by
  simp [mul_coeff_zero, firstFCarry, firstGCarry, binomialInterior_coefficient]

/-- Both nonzero second-carry resonances follow from the whole integral rows. -/
theorem actual_second_carry_resonances (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (baseSecondCarry p : (ZMod p)[X]).coeff p = 8 * WPFiniteInversion.R p 16 ∧
      (baseSecondCarry p : (ZMod p)[X]).coeff (2*p) = -2 * WPFiniteInversion.R p 16 := by
  have hsq := actual_first_F_square_middle p (by omega)
  have hfg := actual_first_FG_middle p hp
  have hsq2 : ((firstFCarry p : (ZMod p)[X]) ^ 2).coeff (2*p) = 0 := by
    rw [pow_two]
    exact interior_product_outer p (2*p) (by omega) le_rfl (-1) 4 (-1) 4
  have hfg2 : ((firstFCarry p : (ZMod p)[X]) * firstGCarry p).coeff (2*p) = 0 :=
    interior_product_outer p (2*p) (by omega) le_rfl (-1) 4 4 (-1)
  have hshift : 2*p-p=p := by omega
  have hp2 : p ≤ 2*p := by omega
  have hn : (baseSecondCarry p : (ZMod p)[X]) =
      4 * (firstFCarry p ^ 2 * X ^ p) - firstFCarry p ^ 2 +
        8 * (firstFCarry p * firstGCarry p) -
          2 * ((firstFCarry p * firstGCarry p) * X ^ p) := by
    rw [actual_baseSecondCarry_field_normalform]
    ring
  rw [hn]
  constructor
  · simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
    rw [coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      actual_first_F_square_constant, hsq, hfg,
      coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, actual_first_FG_constant]
    ring
  · simp only [coeff_sub, coeff_add, coeff_ofNat_mul]
    rw [coeff_mul_X_pow', if_pos hp2, hshift, hsq, hsq2, hfg2,
      coeff_mul_X_pow', if_pos hp2, hshift, hfg]
    ring

end WPMomentPrecision.BasePole
