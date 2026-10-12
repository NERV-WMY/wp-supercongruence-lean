import WPActualEvenLogCarry
import WPFiniteEntropy

open scoped Polynomial BigOperators
open Polynomial WPActualRankTwoHatLift WPPIntegralReduction WPActualGaussProper

namespace WPFiniteCarry

set_option maxHeartbeats 800000

/-- The complete interior binomial row, divided in Z before any coefficient map. -/
noncomputable def cubicInterior {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p,
    C (((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) *
      (4 * X) ^ j * (-11) ^ (p - j)

theorem cubicInterior_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : ℕ) : (cubicInterior p).map f = (cubicInterior p : L[X]) := by
  simp [cubicInterior, Polynomial.map_sum]

theorem cubicInterior_source {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] :
    (4 * X - 11 : K[X]) ^ p =
      (4 * X) ^ p + (-11) ^ p + C (p : K) * cubicInterior p := by
  have hprime : p.Prime := Fact.out
  have hbin := add_pow (4 * X : K[X]) (-11) p
  rw [Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, one_mul, Nat.choose_self, Nat.sub_self] at hbin
  have hsum : (∑ j ∈ Finset.Ico 1 p,
      (4 * X : K[X]) ^ j * (-11) ^ (p - j) * (p.choose j : K[X])) =
      C (p : K) * cubicInterior p := by
    rw [cubicInterior, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp := Finset.mem_Ico.mp hj
    have hd : (p : ℤ) ∣ (p.choose j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by omega : j ≠ 0) hjp.2
    have he : (p : K) * (((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) = (p.choose j : K) := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : K)) (Int.mul_ediv_cancel' hd)
    have heP := congrArg (C : K → K[X]) he
    simp only [map_mul, C_eq_natCast] at heP
    rw [C_eq_natCast]
    linear_combination -(4 * X : K[X]) ^ j * (-11) ^ (p - j) * heP
  rw [hsum] at hbin
  simpa only [Nat.sub_zero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbin

/-- Integer numerator retaining the constant and degree-p Frobenius slots. -/
noncomputable def cubicCarryNumerator {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  C (4 * ((WPFiniteInversion.integerFermatQuotient p 4 : K) -
    (WPFiniteInversion.integerFermatQuotient p 5 : K))) * X ^ p -
  C (11 * ((WPFiniteInversion.integerFermatQuotient p 11 : K) -
    (WPFiniteInversion.integerFermatQuotient p 5 : K))) + cubicInterior p

theorem cubicCarryNumerator_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : ℕ) :
    (cubicCarryNumerator p).map f = (cubicCarryNumerator p : L[X]) := by
  norm_num [cubicCarryNumerator, cubicInterior_map, map_ofNat]

noncomputable def rationalCubicPower (p : ℕ) : ℚ[X] :=
  C (1 / (5 : ℚ) ^ (p - 1)) * (4 * X - 11) ^ p

/-- The actual Q quotient; both derivative-invisible coefficients are present. -/
noncomputable def actualCubicCarry (p : ℕ) : ℚ[X] :=
  C (1 / (p : ℚ)) * (rationalCubicPower p - (4 * X ^ p - 11))

theorem cubicCarryNumerator_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (4 * X - 11 : ℚ[X]) ^ p - C ((5 : ℚ) ^ (p - 1)) * (4 * X ^ p - 11) =
      C (p : ℚ) * cubicCarryNumerator p := by
  have h4 : (4 : ZMod p) ≠ 0 := small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have h11 : (11 : ZMod p) ≠ 0 := small_cast_ne_zero p 11 (by omega) (by omega)
  have hq (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
      (WPFiniteInversion.integerFermatQuotient p a : ℚ) * (p : ℚ) =
        (a : ℚ) ^ (p - 1) - 1 := by
    exact_mod_cast WPFiniteInversion.integerFermatQuotient_mul p a ha
  have hq4 := congrArg (C : ℚ → ℚ[X]) (hq 4 (by simpa using h4))
  have hq5 := congrArg (C : ℚ → ℚ[X]) (hq 5 (by simpa using h5))
  have hq11 := congrArg (C : ℚ → ℚ[X]) (hq 11 (by simpa using h11))
  simp only [map_mul, map_sub, map_pow, map_one] at hq4 hq5 hq11
  norm_num at hq4 hq5 hq11
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpow (a : ℚ[X]) : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [cubicInterior_source p, mul_pow, hodd.neg_pow]
  rw [hpow 4, hpow 11]
  unfold cubicCarryNumerator
  simp only [map_mul, map_sub, map_pow, map_ofNat]
  simp only [C_ofNat, C_eq_natCast, C_eq_intCast] at hq4 hq5 hq11 ⊢
  linear_combination -4 * X ^ p * hq4 + 4 * X ^ p * hq5 + 11 * hq11 - 11 * hq5

theorem actualCubicCarry_numerator (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCubicCarry p = C (1 / (5 : ℚ) ^ (p - 1)) * cubicCarryNumerator p := by
  have hpP : C (p : ℚ) ≠ (0 : ℚ[X]) := C_ne_zero.mpr (by positivity)
  have h5P : C ((5 : ℚ) ^ (p - 1)) ≠ (0 : ℚ[X]) := C_ne_zero.mpr (by positivity)
  have hpi : C (p : ℚ) * C (1 / (p : ℚ)) = (1 : ℚ[X]) := by
    rw [← C_mul, mul_one_div_cancel (by positivity : (p : ℚ) ≠ 0), C_1]
  have h5i : C ((5 : ℚ) ^ (p - 1)) * C (1 / (5 : ℚ) ^ (p - 1)) = (1 : ℚ[X]) := by
    rw [← C_mul, mul_one_div_cancel (by positivity : (5 : ℚ) ^ (p - 1) ≠ 0), C_1]
  apply mul_left_cancel₀ (mul_ne_zero hpP h5P)
  unfold actualCubicCarry rationalCubicPower
  linear_combination cubicCarryNumerator_source p hp +
    C ((5 : ℚ) ^ (p - 1)) * ((4 * X - 11) ^ p * C (1 / (5 : ℚ) ^ (p - 1)) -
      (4 * X ^ p - 11)) * hpi +
    ((4 * X - 11) ^ p - C (p : ℚ) * cubicCarryNumerator p) * h5i

noncomputable def integralCubicCarry (p : ℕ) [Fact p.Prime] :
    (integralRationals p)[X] :=
  C (smallIntegralInverse p 5 ^ (p - 1)) * cubicCarryNumerator p

theorem integralCubicCarry_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralCubicCarry p).map (integralRationals p).subtype = actualCubicCarry p := by
  rw [integralCubicCarry, Polynomial.map_mul, Polynomial.map_C, map_pow,
    show (integralRationals p).subtype (smallIntegralInverse p 5) = 1 / (5 : ℚ)
      from smallIntegralInverse_value p 5 (by omega) (by omega), cubicCarryNumerator_map,
    actualCubicCarry_numerator p hp]
  rw [one_div_pow]

theorem actualCubicCarry_coefficient_integral (p n : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p ((actualCubicCarry p).coeff n) := by
  rw [← integralCubicCarry_value p hp, coeff_map]
  exact ((integralCubicCarry p).coeff n).property

theorem cubicInterior_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (cubicInterior p : (ZMod p)[X]) =
      11 * (WPFiniteAffineLog.LP p).comp (C (4 / 11 : ZMod p) * X) := by
  have h11 : (11 : ZMod p) ≠ 0 := small_cast_ne_zero p 11 (by omega) (by omega)
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨k, by omega⟩
  unfold cubicInterior WPFiniteAffineLog.LP
  rw [sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Finset.mem_Ico.mp hj
  have hsign : (-1 : ZMod p) ^ (j - 1) * (-1) ^ (p - j) = 1 := by
    rw [← pow_add, show j - 1 + (p - j) = p - 1 by omega]
    exact heven.neg_one_pow
  have h11pow : (11 : ZMod p) ^ (p - j) = 11 / (11 : ZMod p) ^ j := by
    apply (eq_div_iff (pow_ne_zero j h11)).mpr
    rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ p), ZMod.pow_card]
  have hcoef := WPFiniteInversion.divided_choose_cast p j hj
  rw [hcoef, mul_comp, C_comp, pow_comp, X_comp]
  simp only [mul_pow, ← C_pow]
  have hscalar : ((-1 : ZMod p) ^ (j - 1) / (j : ZMod p)) *
      4 ^ j * (-11) ^ (p - j) = 11 * (j : ZMod p)⁻¹ * (4 / 11 : ZMod p) ^ j := by
    rw [show (-11 : ZMod p) = (-1) * 11 by ring, mul_pow, div_pow, h11pow]
    simp only [div_eq_mul_inv]
    linear_combination 4 ^ j * (j : ZMod p)⁻¹ * 11 * ((11 : ZMod p) ^ j)⁻¹ * hsign
  have hpoly := congrArg (fun a : ZMod p => C a * (X : (ZMod p)[X]) ^ j) hscalar
  norm_num [map_mul, map_pow, map_ofNat] at hpoly ⊢
  linear_combination X ^ j * hpoly

noncomputable def actualCubicCarryField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (integralCubicCarry p).map (residueHom p)

/-- The entire NC81b polynomial, with both actual endpoint quotients retained. -/
theorem actualCubicCarry_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCubicCarryField p =
      C (4 * (2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))) * X ^ p -
      C (11 * ((WPFiniteInversion.integerFermatQuotient p 11 : ZMod p) -
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))) +
      11 * (WPFiniteAffineLog.LP p).comp (C (4 / 11 : ZMod p) * X) := by
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  have hi : residueHom p (smallIntegralInverse p 5 ^ (p - 1)) = 1 := by
    rw [map_pow, smallIntegralInverse_field p 5 (by omega) (by omega), inv_pow]
    change ((5 : ZMod p) ^ (p - 1))⁻¹ = 1
    rw [ZMod.pow_card_sub_one_eq_one h5, inv_one]
  rw [actualCubicCarryField, integralCubicCarry, Polynomial.map_mul,
    Polynomial.map_C, hi, C_1, one_mul, cubicCarryNumerator_map]
  unfold cubicCarryNumerator
  rw [cubicInterior_field p hp, WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)]

theorem actualCubicCarry_source (p : ℕ) [Fact p.Prime] :
    rationalCubicPower p - (4 * X ^ p - 11) = C (p : ℚ) * actualCubicCarry p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hi : C (p : ℚ) * C (1 / (p : ℚ)) = (1 : ℚ[X]) := by
    rw [← C_mul, mul_one_div_cancel hp0, C_1]
  unfold actualCubicCarry
  rw [← mul_assoc, hi, one_mul]

/-- The apparent zero of the cubic power still has its literal divided contribution. -/
theorem actualCubicCarry_at_cubic_zero (p : ℕ) [Fact p.Prime] :
    (actualCubicCarry p).eval (11 / 4) =
      (11 - 4 * (11 / 4 : ℚ) ^ p) / (p : ℚ) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  simp only [actualCubicCarry, rationalCubicPower, eval_mul, eval_C,
    eval_sub, eval_pow, eval_X, eval_ofNat]
  norm_num [hp]
  ring

end WPFiniteCarry
