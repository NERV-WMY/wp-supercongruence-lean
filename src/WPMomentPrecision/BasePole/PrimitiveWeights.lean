import WPPIntegralReduction

open scoped BigOperators

namespace WPMomentPrecision.BasePole

open WPPIntegralReduction WPNativeMomentIntegrality

/-- Divide the original two-end primitive in Q before reducing modulo p. -/
theorem primitiveWeight_div_prime (p : ℕ) [Fact p.Prime] (m : ℤ) :
    primitiveWeight p m / (p : ℚ) =
      ((2 : ℚ) ^ m - (2 : ℚ) ^ (-m)) / (m : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold primitiveWeight
  rw [div_div, mul_comm (m : ℚ) (p : ℚ), mul_div_mul_left _ _ hpq]

/-- Every nonresonant divided primitive has a unit denominator at p. -/
theorem divided_primitive_weight_integral (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) (hm : ¬(p : ℤ) ∣ m) :
    0 ≤ padicValRat p (primitiveWeight p m / (p : ℚ)) := by
  rw [primitiveWeight_div_prime]
  let a : integralRationals p := ⟨(2 : ℚ) ^ m - (2 : ℚ) ^ (-m),
    integral_two_endpoint_difference p hp m⟩
  let b : integralRationals p := ⟨(m : ℚ)⁻¹, by
    change 0 ≤ padicValRat p (m : ℚ)⁻¹
    rw [padicValRat.inv, integer_denominator_unit p m hm]
    norm_num⟩
  have h : 0 ≤ padicValRat p
      (((2 : ℚ) ^ m - (2 : ℚ) ^ (-m)) * (m : ℚ)⁻¹) := (a * b).property
  simpa only [div_eq_mul_inv] using h

/-- Both original endpoints survive in the reduction of the divided unit weight. -/
theorem divided_primitive_weight_residue (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) (hm : ¬(p : ℤ) ∣ m) :
    ((primitiveWeight p m / (p : ℚ) : ℚ) : ZMod p) = fieldWeight p m := by
  have hmc : (m : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hm
  have hdiff := integral_two_endpoint_difference p hp m
  have hnum : (((m : ℚ).num : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Rat.num_intCast] using hmc
  unfold fieldWeight
  rw [primitiveWeight_div_prime,
    Rat.cast_div_of_ne_zero (integral_denominator_cast_ne_zero p _ hdiff) hnum,
    Rat.cast_sub_of_ne_zero
      (integral_denominator_cast_ne_zero p _
        (by rw [two_zpow_unit p hp m]))
      (integral_denominator_cast_ne_zero p _
        (by rw [two_zpow_unit p hp (-m)])),
    cast_two_zpow, cast_two_zpow, Rat.cast_intCast]

/-- Reduction of a complete finite unit band, with its actual coefficient multipliers. -/
theorem divided_primitive_weighted_sum_residue (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) {ι : Type*} (s : Finset ι) (a : ι → ℚ) (m : ι → ℤ)
    (ha : ∀ i ∈ s, 0 ≤ padicValRat p (a i))
    (hm : ∀ i ∈ s, ¬(p : ℤ) ∣ m i) :
    ((∑ i ∈ s, a i * (primitiveWeight p (m i) / (p : ℚ)) : ℚ) : ZMod p) =
      ∑ i ∈ s, (a i : ZMod p) * fieldWeight p (m i) := by
  have hw (i : ι) (hi : i ∈ s) := divided_primitive_weight_integral p hp (m i) (hm i hi)
  have ht (i : ι) (hi : i ∈ s) :
      0 ≤ padicValRat p (a i * (primitiveWeight p (m i) / (p : ℚ))) :=
    (integralRationals p).mul_mem (ha i hi) (hw i hi)
  rw [cast_sum_integral p s _ ht]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ (ha i hi))
      (integral_denominator_cast_ne_zero p _ (hw i hi)),
    divided_primitive_weight_residue p hp (m i) (hm i hi)]

/-- The signed index of y^r Y^c in the SB3 primitive. The block number is integral. -/
def primitiveBlockIndex (p r : ℕ) (c : ℤ) : ℤ :=
  2 * (r : ℤ) + (2 * c - 5) * (p : ℤ)

theorem primitiveBlockIndex_cast (p r : ℕ) [Fact p.Prime] (c : ℤ) :
    (primitiveBlockIndex p r c : ZMod p) = 2 * (r : ZMod p) := by
  simp [primitiveBlockIndex]

theorem primitive_weight_small_nat_ne_zero (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hd
  have hle := Nat.le_of_dvd hn hd
  omega

/-- The entire block is nonresonant: its residue is the explicitly retained 2r. -/
theorem primitiveBlockIndex_nonresonant (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) (c : ℤ) :
    ¬(p : ℤ) ∣ primitiveBlockIndex p r c := by
  have h2 := primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega)
  have hr0 := primitive_weight_small_nat_ne_zero p r
    (by have h := (Finset.mem_Ico.mp hr).1; omega) (Finset.mem_Ico.mp hr).2
  intro hd
  have he : (primitiveBlockIndex p r c : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [primitiveBlockIndex_cast] at he
  exact (mul_ne_zero h2 hr0) he

theorem divided_primitive_block_integral (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) (c : ℤ) :
    0 ≤ padicValRat p (primitiveWeight p (primitiveBlockIndex p r c) / (p : ℚ)) :=
  divided_primitive_weight_integral p (by omega) _
    (primitiveBlockIndex_nonresonant p r hp hr c)

theorem two_block_positive_endpoint (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (c : ℤ) :
    (2 : ZMod p) ^ primitiveBlockIndex p r c =
      (2 : ZMod p) ^ (2 * c - 5) * (4 : ZMod p) ^ r := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      (primitive_weight_small_nat_ne_zero p 2 (by omega) (by omega))
  have hperiod (e : ℤ) : (2 : ZMod p) ^ (e * (p : ℤ)) = (2 : ZMod p) ^ e := by
    rw [mul_comm e, zpow_mul, zpow_natCast, ZMod.pow_card]
  have hpow : (2 : ZMod p) ^ (2 * (r : ℤ)) = (4 : ZMod p) ^ r := by
    rw [show 2 * (r : ℤ) = ((2 * r : ℕ) : ℤ) by omega, zpow_natCast, pow_mul]
    norm_num
  rw [primitiveBlockIndex, zpow_add₀ h2, hperiod, hpow, mul_comm]

theorem two_block_negative_endpoint (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (c : ℤ) :
    (2 : ZMod p) ^ (-primitiveBlockIndex p r c) =
      (2 : ZMod p) ^ (5 - 2 * c) * ((4 : ZMod p) ^ r)⁻¹ := by
  rw [zpow_neg, two_block_positive_endpoint p r hp c, mul_inv_rev,
    ← zpow_neg (2 : ZMod p) (2 * c - 5),
    show -(2 * c - 5) = 5 - 2 * c by ring, mul_comm]

section BlockAlgebra

variable {K : Type*} [Field K]

/-- The SB3 weight keeps both ordered endpoints for every integral block number. -/
def dividedBlockWeight (c : ℤ) (r z : K) : K :=
  ((2 : K) ^ (2 * c - 5) * z - (2 : K) ^ (5 - 2 * c) * z⁻¹) / (2 * r)

theorem dividedBlockWeight_zero (r z : K) :
    dividedBlockWeight 0 r z = (z / 32 - 32 / z) / (2 * r) := by
  norm_num [dividedBlockWeight, zpow_neg, div_eq_mul_inv, mul_comm]

theorem dividedBlockWeight_one (r z : K) :
    dividedBlockWeight 1 r z = (z / 8 - 8 / z) / (2 * r) := by
  norm_num [dividedBlockWeight, zpow_neg, div_eq_mul_inv, mul_comm]

theorem dividedBlockWeight_two (r z : K) :
    dividedBlockWeight 2 r z = (z / 2 - 2 / z) / (2 * r) := by
  norm_num [dividedBlockWeight, zpow_neg, div_eq_mul_inv, mul_comm]

end BlockAlgebra

/-- The actual divided primitive reduces to SB3, including both original endpoints. -/
theorem divided_primitive_block_residue (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) (c : ℤ) :
    ((primitiveWeight p (primitiveBlockIndex p r c) / (p : ℚ) : ℚ) : ZMod p) =
      dividedBlockWeight c (r : ZMod p) ((4 : ZMod p) ^ r) := by
  rw [divided_primitive_weight_residue p (by omega) _
    (primitiveBlockIndex_nonresonant p r hp hr c)]
  unfold fieldWeight dividedBlockWeight
  rw [two_block_positive_endpoint p r hp c, two_block_negative_endpoint p r hp c,
    primitiveBlockIndex_cast]

theorem divided_primitive_block_zero_residue (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) :
    ((primitiveWeight p (primitiveBlockIndex p r 0) / (p : ℚ) : ℚ) : ZMod p) =
      ((4 : ZMod p) ^ r / 32 - 32 / (4 : ZMod p) ^ r) / (2 * (r : ZMod p)) := by
  rw [divided_primitive_block_residue p r hp hr 0, dividedBlockWeight_zero]

theorem divided_primitive_block_one_residue (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) :
    ((primitiveWeight p (primitiveBlockIndex p r 1) / (p : ℚ) : ℚ) : ZMod p) =
      ((4 : ZMod p) ^ r / 8 - 8 / (4 : ZMod p) ^ r) / (2 * (r : ZMod p)) := by
  rw [divided_primitive_block_residue p r hp hr 1, dividedBlockWeight_one]

theorem divided_primitive_block_two_residue (p r : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hr : r ∈ Finset.Ico 1 p) :
    ((primitiveWeight p (primitiveBlockIndex p r 2) / (p : ℚ) : ℚ) : ZMod p) =
      ((4 : ZMod p) ^ r / 2 - 2 / (4 : ZMod p) ^ r) / (2 * (r : ZMod p)) := by
  rw [divided_primitive_block_residue p r hp hr 2, dividedBlockWeight_two]

end WPMomentPrecision.BasePole
