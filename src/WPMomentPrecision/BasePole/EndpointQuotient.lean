import WPMomentPrecision.BasePole.BinomialCarry
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Div

open scoped Polynomial BigOperators
open Polynomial

namespace WPMomentPrecision.BasePole

noncomputable def endpointGeometric {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.range p, C ((4 : K) ^ (p - 1 - j)) * X ^ j

/-- The geometric quotient is an entire polynomial, including its constant term. -/
theorem endpointGeometric_source {K : Type*} [CommRing K] (p : ℕ) :
    (4 - X : K[X]) * endpointGeometric p = frobeniusF p := by
  have hs := geom_sum₂_mul (X : K[X]) 4 p
  have hrow : (∑ j ∈ Finset.range p, (X : K[X]) ^ j * 4 ^ (p - 1 - j)) =
      endpointGeometric p := by
    unfold endpointGeometric
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show (4 : K[X]) = C (4 : K) by rw [C_ofNat], ← map_pow, mul_comm]
  have hfour : (4 : K[X]) ^ p = C ((4 : K) ^ p) := by
    rw [show (4 : K[X]) = C (4 : K) by rw [C_ofNat], ← map_pow]
  rw [hrow, hfour] at hs
  unfold frobeniusF
  linear_combination -hs

theorem endpointGeometric_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : ℕ) :
    (endpointGeometric p).map f = (endpointGeometric p : L[X]) := by
  simp [endpointGeometric, Polynomial.map_sum, map_ofNat]

theorem endpointGeometric_coefficient {K : Type*} [CommRing K] (p j : ℕ) :
    (endpointGeometric p : K[X]).coeff j =
      if j < p then (4 : K) ^ (p - 1 - j) else 0 := by
  classical
  rw [endpointGeometric, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

theorem actual_firstFCarry_endpoint (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (firstFCarry p : ℤ[X]).eval 4 = 0 := by
  have hs := congrArg (fun P : ℤ[X] => P.eval 4) (actual_F_first_carry_source p hp)
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpNat : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hm : (p : ℤ) * (firstFCarry p : ℤ[X]).eval 4 = 0 := by
    simpa only [eval_pow, eval_sub, eval_ofNat, eval_X, sub_self, zero_pow hpNat,
      eval_add, eval_mul, eval_C, frobeniusF, zero_add] using hs.symm
  exact (mul_eq_zero.mp hm).resolve_left hp0

/-- This quotient is formed in Z[X], before any rational or residue-field map. -/
noncomputable def endpointFCarryQuotient (p : ℕ) : ℤ[X] :=
  -((firstFCarry p : ℤ[X]) /ₘ (X - C 4))

theorem endpointFCarryQuotient_source (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 - X : ℤ[X]) * endpointFCarryQuotient p = firstFCarry p := by
  have hr : IsRoot (firstFCarry p : ℤ[X]) 4 := actual_firstFCarry_endpoint p hp
  have hs : (X - C 4 : ℤ[X]) * ((firstFCarry p : ℤ[X]) /ₘ (X - C 4)) =
      firstFCarry p := mul_divByMonic_eq_iff_isRoot.mpr hr
  unfold endpointFCarryQuotient
  calc
    _ = (X - C 4 : ℤ[X]) * ((firstFCarry p : ℤ[X]) /ₘ (X - C 4)) := by
      simp only [C_ofNat]
      ring
    _ = _ := hs

/-- The actual F^(p-1) has an integral first carry; no rational pole remains. -/
theorem actual_endpoint_first_digit_source (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 - X : ℤ[X]) ^ (p - 1) =
      endpointGeometric p + C (p : ℤ) * endpointFCarryQuotient p := by
  have hF : (4 - X : ℤ[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : ℤ[X] => P.coeff 1) hz
    norm_num at hc
  apply mul_left_cancel₀ hF
  rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le,
    actual_F_first_carry_source p hp, mul_add, endpointGeometric_source]
  rw [show (4 - X : ℤ[X]) * (C (p : ℤ) * endpointFCarryQuotient p) =
      C (p : ℤ) * ((4 - X) * endpointFCarryQuotient p) by ring,
    endpointFCarryQuotient_source p hp]

theorem endpoint_quotient_carry_cancellation (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    endpointFCarryQuotient p * frobeniusF p =
      (endpointGeometric p : ℤ[X]) * firstFCarry p := by
  have hF : (4 - X : ℤ[X]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : ℤ[X] => P.coeff 1) hz
    norm_num at hc
  apply mul_left_cancel₀ hF
  calc
    _ = ((4 - X) * endpointFCarryQuotient p) * frobeniusF p := by ring
    _ = firstFCarry p * frobeniusF p := by rw [endpointFCarryQuotient_source p hp]
    _ = firstFCarry p * ((4 - X) * endpointGeometric p) := by
      rw [endpointGeometric_source]
    _ = _ := by ring

noncomputable def endpointFirstCarry (p : ℕ) : ℤ[X] :=
  2 * endpointGeometric p * firstFCarry p * frobeniusG p +
    endpointGeometric p * frobeniusF p * firstGCarry p

noncomputable def endpointSecondCarry (p : ℕ) : ℤ[X] :=
  endpointFCarryQuotient p * firstFCarry p * frobeniusG p +
    2 * endpointGeometric p * firstFCarry p * firstGCarry p

/-- The canceled endpoint numerator retains all three integral carry rows. -/
theorem actual_endpoint_three_carry_source (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 - X : ℤ[X]) ^ (2 * p - 1) * (4 * X - 1) ^ p =
      endpointGeometric p * frobeniusF p * frobeniusG p +
      C (p : ℤ) * endpointFirstCarry p + C ((p : ℤ) ^ 2) * endpointSecondCarry p +
      C ((p : ℤ) ^ 3) * endpointFCarryQuotient p * firstFCarry p * firstGCarry p := by
  have hprime : p.Prime := Fact.out
  rw [show 2 * p - 1 = (p - 1) + p by omega, pow_add,
    actual_endpoint_first_digit_source p hp, actual_F_first_carry_source p hp,
    actual_G_first_carry_source p hp]
  have hc := endpoint_quotient_carry_cancellation p hp
  unfold endpointFirstCarry endpointSecondCarry
  simp only [map_pow]
  linear_combination C (p : ℤ) * frobeniusG p * hc +
    C (p : ℤ) ^ 2 * firstGCarry p * hc

end WPMomentPrecision.BasePole
