import WPActualEvenLogCarry
import WPActualRankTwoHatLift
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators
open WPPIntegralReduction WPActualEvenLogCarry WPActualRankTwoHatLift

namespace WPFiniteCarry

set_option maxHeartbeats 800000

/-- The literal odd harmonic sum O_r, using the zero-based odd index. -/
noncomputable def oddHarmonicQ (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range r, 1 / ((2 * j + 1 : ℕ) : ℚ)

/-- The actual rational product in NC81, before any reduction. -/
noncomputable def oddProductQ (p r : ℕ) : ℚ :=
  ∏ j ∈ Finset.range r, (1 - (p : ℚ) / ((2 * j + 1 : ℕ) : ℚ))

theorem oddHarmonicQ_Icc (r : ℕ) :
    oddHarmonicQ r = ∑ j ∈ Finset.Icc 1 r, 1 / ((2 * j - 1 : ℕ) : ℚ) := by
  have hs : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hs, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, oddHarmonicQ]
  apply Finset.sum_congr rfl
  intro j _hj
  congr 2
  omega

theorem signedChooseQ_recurrence (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    2 * ((r : ℚ) + 1) *
        ((-1 : ℚ) ^ (r + 1) * (((p - 1) / 2).choose (r + 1) : ℚ)) =
      (2 * (r : ℚ) + 1 - (p : ℚ)) *
        ((-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ)) := by
  have h := congrArg (fun z : ℕ => (z : ℚ))
    (Nat.choose_succ_right_eq ((p - 1) / 2) r)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hr, Nat.cast_add, Nat.cast_one] at h
  have hN := congrArg (fun z : ℕ => (z : ℚ))
    (prime_half_identity p (by omega : 7 ≤ p))
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hN
  rw [pow_succ]
  linear_combination -2 * (-1 : ℚ) ^ r * h -
    ((-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ)) * hN

/-- Exact finite-product identity, including r=0 and the full top index N. -/
theorem signedChooseQ_finiteProduct (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ) =
      centralCoefficient ℚ r * oddProductQ p r := by
  induction r with
  | zero => simp [oddProductQ, centralCoefficient_zero]
  | succ r ih =>
    have hi := ih (by omega)
    have hchoose := signedChooseQ_recurrence p r hp (by omega)
    have hcentral := centralCoefficient_recurrence (K := ℚ) (by norm_num) r
    have hod : ((2 * r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hu : 2 * ((r : ℚ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hu
    rw [hchoose, hi]
    simp only [oddProductQ, Finset.prod_range_succ]
    change (2 * (r : ℚ) + 1 - (p : ℚ)) *
      (centralCoefficient ℚ r * oddProductQ p r) = 2 * ((r : ℚ) + 1) *
      (centralCoefficient ℚ (r + 1) *
        (oddProductQ p r * (1 - (p : ℚ) / ((2 * r + 1 : ℕ) : ℚ))))
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hod ⊢
    field_simp
    linear_combination -(oddProductQ p r) * (2 * (r : ℚ) + 1 - p) * hcentral

/-- The same product with the printed one-based j=1,...,r indexing. -/
theorem signedChooseQ_finiteProduct_Icc (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ) = centralCoefficient ℚ r *
      ∏ j ∈ Finset.Icc 1 r, (1 - (p : ℚ) / ((2 * j - 1 : ℕ) : ℚ)) := by
  rw [signedChooseQ_finiteProduct p r hp hr]
  congr 1
  have hs : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hs, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, oddProductQ]
  apply Finset.prod_congr rfl
  intro j _hj
  congr 3
  omega

/-- Integral realization of O_r; the retained reciprocal supplies every unit. -/
noncomputable def oddHarmonicIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  ∑ j ∈ Finset.range r, smallIntegralInverse p (2 * j + 1)

noncomputable def oddProductIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  ∏ j ∈ Finset.range r,
    (1 - (p : integralRationals p) * smallIntegralInverse p (2 * j + 1))

/-- Explicit integral second-order remainder; multiplication adds the next odd factor. -/
noncomputable def oddProductRemainder (p : ℕ) [Fact p.Prime] : ℕ → integralRationals p
  | 0 => 0
  | r + 1 => oddProductRemainder p r +
      oddHarmonicIntegral p r * smallIntegralInverse p (2 * r + 1) -
      (p : integralRationals p) * oddProductRemainder p r * smallIntegralInverse p (2 * r + 1)

theorem oddProductIntegral_firstTaylor (p r : ℕ) [Fact p.Prime] :
    oddProductIntegral p r = 1 - (p : integralRationals p) * oddHarmonicIntegral p r +
      (p : integralRationals p) ^ 2 * oddProductRemainder p r := by
  induction r with
  | zero => simp [oddProductIntegral, oddHarmonicIntegral, oddProductRemainder]
  | succ r ih =>
    simp only [oddProductIntegral, Finset.prod_range_succ] at ih ⊢
    rw [ih]
    simp only [oddHarmonicIntegral, Finset.sum_range_succ, oddProductRemainder]
    ring

theorem oddHarmonicIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (integralRationals p).subtype (oddHarmonicIntegral p r) = oddHarmonicQ r := by
  rw [oddHarmonicIntegral, map_sum, oddHarmonicQ]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr := Finset.mem_range.mp hj
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  exact smallIntegralInverse_value p (2 * j + 1) (by omega) (by omega)

theorem oddProductIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (integralRationals p).subtype (oddProductIntegral p r) = oddProductQ p r := by
  rw [oddProductIntegral, map_prod, oddProductQ]
  apply Finset.prod_congr rfl
  intro j hj
  have hjr := Finset.mem_range.mp hj
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  rw [map_sub, map_one, map_mul, map_natCast,
    show (integralRationals p).subtype (smallIntegralInverse p (2 * j + 1)) =
      1 / ((2 * j + 1 : ℕ) : ℚ) from
      smallIntegralInverse_value p (2 * j + 1) (by omega) (by omega)]
  ring

theorem oddProductQ_firstTaylor (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    oddProductQ p r = 1 - (p : ℚ) * oddHarmonicQ r +
      (p : ℚ) ^ 2 * (oddProductRemainder p r).val := by
  have h := congrArg (integralRationals p).subtype (oddProductIntegral_firstTaylor p r)
  simpa only [oddProductIntegral_value p r hp hr, map_add, map_sub, map_mul,
    map_one, map_natCast, map_pow, oddHarmonicIntegral_value p r hp hr,
    Subring.subtype_apply] using h

/-- Integral lift of the retained central coefficient, without redefining that coefficient. -/
noncomputable def centralCoefficientIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  (Nat.centralBinom r : integralRationals p) * (smallIntegralInverse p 4) ^ r

theorem centralCoefficientIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype (centralCoefficientIntegral p r) = centralCoefficient ℚ r := by
  rw [centralCoefficientIntegral, map_mul, map_natCast, map_pow,
    show (integralRationals p).subtype (smallIntegralInverse p 4) = (1 / 4 : ℚ) from
      (by change (smallIntegralInverse p 4).val = (1 / 4 : ℚ)
          exact smallIntegralInverse_value p 4 (by omega) (by omega))]
  simp [centralCoefficient, div_eq_mul_inv, inv_pow]

theorem centralCoefficientIntegral_field (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (centralCoefficientIntegral p r) = centralCoefficient (ZMod p) r := by
  rw [centralCoefficientIntegral, map_mul, map_natCast, map_pow,
    smallIntegralInverse_field p 4 (by omega) (by omega)]
  simp [centralCoefficient, div_eq_mul_inv, inv_pow]

theorem oddHarmonicIntegral_field (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    residueHom p (oddHarmonicIntegral p r) =
      ∑ j ∈ Finset.range r, (((2 * j + 1 : ℕ) : ZMod p))⁻¹ := by
  rw [oddHarmonicIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr := Finset.mem_range.mp hj
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  exact smallIntegralInverse_field p (2 * j + 1) (by omega) (by omega)

/-- The literal b_r O_r coefficient of the universal carry. -/
noncomputable def centralOddIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  centralCoefficientIntegral p r * oddHarmonicIntegral p r

theorem centralOddIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (centralOddIntegral p r).val = centralCoefficient ℚ r * oddHarmonicQ r := by
  change (integralRationals p).subtype (centralOddIntegral p r) = _
  rw [centralOddIntegral, map_mul, centralCoefficientIntegral_value p r hp,
    oddHarmonicIntegral_value p r hp hr]

noncomputable def signedChooseRemainder (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  centralCoefficientIntegral p r * oddProductRemainder p r

/-- Integration interface: the first carry is literal and the p^2 error is integral. -/
theorem signedChooseQ_firstTaylor (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) :
    (-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ) =
      centralCoefficient ℚ r - (p : ℚ) * centralCoefficient ℚ r * oddHarmonicQ r +
        (p : ℚ) ^ 2 * (signedChooseRemainder p r).val := by
  rw [signedChooseQ_finiteProduct p r hp hr, oddProductQ_firstTaylor p r hp hr]
  have hv : (signedChooseRemainder p r).val =
      centralCoefficient ℚ r * (oddProductRemainder p r).val := by
    change (integralRationals p).subtype (signedChooseRemainder p r) = _
    rw [signedChooseRemainder, map_mul, centralCoefficientIntegral_value p r hp]
    rfl
  rw [hv]
  ring

theorem centralCoefficient_integral (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    0 ≤ padicValRat p (centralCoefficient ℚ r) := by
  rw [← centralCoefficientIntegral_value p r hp]
  exact (centralCoefficientIntegral p r).property

theorem oddHarmonicQ_integral (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr : r ≤ (p - 1) / 2) : 0 ≤ padicValRat p (oddHarmonicQ r) := by
  rw [← oddHarmonicIntegral_value p r hp hr]
  exact (oddHarmonicIntegral p r).property

theorem integral_mul_twoInverse_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) (a : integralRationals p) :
    (a * smallIntegralInverse p (2 * r)).val = a.val / (2 * (r : ℚ)) := by
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  change (integralRationals p).subtype (a * smallIntegralInverse p (2 * r)) = _
  rw [map_mul,
    show (integralRationals p).subtype (smallIntegralInverse p (2 * r)) =
      1 / ((2 * r : ℕ) : ℚ) from smallIntegralInverse_value p (2 * r) (by omega) (by omega)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Subring.subtype_apply]
  ring

/-- Integral coefficient of L(q), with the original integration pivot. -/
noncomputable def centralLogCoefficientIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  centralCoefficientIntegral p r * smallIntegralInverse p (2 * r)

theorem centralLogCoefficientIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    (centralLogCoefficientIntegral p r).val = centralCoefficient ℚ r / (2 * (r : ℚ)) := by
  rw [centralLogCoefficientIntegral, integral_mul_twoInverse_value p r hp hr0 hr]
  change (integralRationals p).subtype (centralCoefficientIntegral p r) / _ = _
  rw [centralCoefficientIntegral_value p r hp]

theorem centralLogCoefficientIntegral_field (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    residueHom p (centralLogCoefficientIntegral p r) =
      centralCoefficient (ZMod p) r / (2 * (r : ZMod p)) := by
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  rw [centralLogCoefficientIntegral, map_mul, centralCoefficientIntegral_field p r hp,
    smallIntegralInverse_field p (2 * r) (by omega) (by omega)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]

/-- Integral coefficient of the universal E_L(q), retaining the whole O_r. -/
noncomputable def centralOddLogIntegral (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  centralOddIntegral p r * smallIntegralInverse p (2 * r)

theorem centralOddLogIntegral_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    (centralOddLogIntegral p r).val =
      centralCoefficient ℚ r * oddHarmonicQ r / (2 * (r : ℚ)) := by
  rw [centralOddLogIntegral, integral_mul_twoInverse_value p r hp hr0 hr,
    centralOddIntegral_value p r hp hr]

theorem centralOddLogIntegral_field (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    residueHom p (centralOddLogIntegral p r) =
      (centralCoefficient (ZMod p) r *
        ∑ j ∈ Finset.range r, (((2 * j + 1 : ℕ) : ZMod p))⁻¹) / (2 * (r : ZMod p)) := by
  have hn := prime_half_identity p (by omega : 7 ≤ p)
  rw [centralOddLogIntegral, centralOddIntegral, map_mul, map_mul,
    centralCoefficientIntegral_field p r hp, oddHarmonicIntegral_field p r hp hr,
    smallIntegralInverse_field p (2 * r) (by omega) (by omega)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]

/-- Integral p^2 remainder after the original log integration denominator 2r. -/
noncomputable def logCoefficientRemainder (p r : ℕ) [Fact p.Prime] : integralRationals p :=
  signedChooseRemainder p r * smallIntegralInverse p (2 * r)

theorem logCoefficientRemainder_value (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    (logCoefficientRemainder p r).val = (signedChooseRemainder p r).val / (2 * (r : ℚ)) := by
  exact integral_mul_twoInverse_value p r hp hr0 hr (signedChooseRemainder p r)

theorem signedChooseQ_div_firstTaylor (p r : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hr0 : 0 < r) (hr : r ≤ (p - 1) / 2) :
    ((-1 : ℚ) ^ r * (((p - 1) / 2).choose r : ℚ)) / (2 * (r : ℚ)) =
      centralCoefficient ℚ r / (2 * (r : ℚ)) -
        (p : ℚ) * (centralCoefficient ℚ r * oddHarmonicQ r / (2 * (r : ℚ))) +
        (p : ℚ) ^ 2 * (logCoefficientRemainder p r).val := by
  rw [signedChooseQ_firstTaylor p r hp hr, logCoefficientRemainder_value p r hp hr0 hr]
  ring

end WPFiniteCarry
