import WPMomentPrecision.BasePole.ActualKernels
import WPFiniteReflection
import WPActualNativeCMLogValues

open scoped BigOperators

namespace WPMomentPrecision.BasePole

section EndpointAlgebra

variable {K : Type*} [Field K]

def blockWeight0 (r z : K) : K := (z / 32 - 32 / z) / (2 * r)
def blockWeight1 (r z : K) : K := (z / 8 - 8 / z) / (2 * r)
def blockWeight2 (r z : K) : K := (z / 2 - 2 / z) / (2 * r)

/-- The entire first-carry F-block cancels pointwise; the G-block retains its full unit sum. -/
theorem first_carry_block_contraction (r z : K)
    (h2 : (2 : K) ≠ 0) (hr : r ≠ 0) (hz : z ≠ 0) :
    (-4 / (z * r)) *
        (-8 * blockWeight0 r z + 34 * blockWeight1 r z - 8 * blockWeight2 r z) +
      (z / r) *
        (16 * blockWeight0 r z - 8 * blockWeight1 r z + blockWeight2 r z) =
      -225 / r ^ 2 := by
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 ^ 3 by ring]
    exact pow_ne_zero _ h2
  have h32 : (32 : K) ≠ 0 := by
    rw [show (32 : K) = 2 ^ 5 by ring]
    exact pow_ne_zero _ h2
  unfold blockWeight0 blockWeight1 blockWeight2
  field_simp [h2, h8, h32, hr, hz]
  ring

/-- Both full endpoint unit bands vanish together, before summation or any chosen lift. -/
theorem endpoint_main_unit_block_zero (r z : K)
    (h2 : (2 : K) ≠ 0) (hr : r ≠ 0) (hz : z ≠ 0) :
    -4 * blockWeight0 r z + 17 * blockWeight1 r z - 4 * blockWeight2 r z = 0 := by
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 ^ 3 by ring]
    exact pow_ne_zero _ h2
  have h32 : (32 : K) ≠ 0 := by
    rw [show (32 : K) = 2 ^ 5 by ring]
    exact pow_ne_zero _ h2
  unfold blockWeight0 blockWeight1 blockWeight2
  field_simp [h2, h8, h32, hr, hz]
  ring

end EndpointAlgebra

/-- Literal field reductions of the two integral binomial carry rows. -/
def firstFCoeff (p r : ℕ) [Fact p.Prime] : ZMod p :=
  -4 / ((4 : ZMod p) ^ r * (r : ZMod p))

def firstGCoeff (p r : ℕ) [Fact p.Prime] : ZMod p :=
  (4 : ZMod p) ^ r / (r : ZMod p)

def geometricCoeff (p r : ℕ) [Fact p.Prime] : ZMod p := (4 : ZMod p)⁻¹ ^ r

theorem four_field_ne_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (4 : ZMod p) ≠ 0 :=
  WPFiniteInversion.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))

theorem reflected_four_power (p r : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hr : r ∈ Finset.Ico 1 p) :
    (4 : ZMod p) ^ (p - r) = 4 / (4 : ZMod p) ^ r := by
  rw [pow_sub₀ (4 : ZMod p) (four_field_ne_zero p hp)
      (Nat.le_of_lt (Finset.mem_Ico.mp hr).2),
    ZMod.pow_card]
  rfl

theorem firstFCoeff_reflected (p r : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hr : r ∈ Finset.Ico 1 p) : firstFCoeff p (p - r) = firstGCoeff p r := by
  have h4 := four_field_ne_zero p hp
  have hz := pow_ne_zero r h4
  have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
  unfold firstFCoeff firstGCoeff
  rw [reflected_four_power p r hp hr, WPFiniteInversion.reflected_denominator p r hr]
  field_simp [h4, hz, hr0]

theorem firstGCoeff_reflected (p r : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hr : r ∈ Finset.Ico 1 p) : firstGCoeff p (p - r) = firstFCoeff p r := by
  have h4 := four_field_ne_zero p hp
  have hz := pow_ne_zero r h4
  have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
  unfold firstFCoeff firstGCoeff
  rw [reflected_four_power p r hp hr, WPFiniteInversion.reflected_denominator p r hr]
  field_simp [h4, hz, hr0]

/-- The first carry is retained through its full normalized p^2 contribution, then canceled. -/
theorem whole_first_carry_contraction (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (∑ r ∈ Finset.Ico 1 p,
      (firstFCoeff p r *
        (-8 * blockWeight0 (r : ZMod p) ((4 : ZMod p) ^ r) +
          34 * blockWeight1 (r : ZMod p) ((4 : ZMod p) ^ r) -
          8 * blockWeight2 (r : ZMod p) ((4 : ZMod p) ^ r)) +
      firstGCoeff p r *
        (16 * blockWeight0 (r : ZMod p) ((4 : ZMod p) ^ r) -
          8 * blockWeight1 (r : ZMod p) ((4 : ZMod p) ^ r) +
          blockWeight2 (r : ZMod p) ((4 : ZMod p) ^ r)))) = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hs : (∑ r ∈ Finset.Ico 1 p,
      (firstFCoeff p r *
        (-8 * blockWeight0 (r : ZMod p) ((4 : ZMod p) ^ r) +
          34 * blockWeight1 (r : ZMod p) ((4 : ZMod p) ^ r) -
          8 * blockWeight2 (r : ZMod p) ((4 : ZMod p) ^ r)) +
      firstGCoeff p r *
        (16 * blockWeight0 (r : ZMod p) ((4 : ZMod p) ^ r) -
          8 * blockWeight1 (r : ZMod p) ((4 : ZMod p) ^ r) +
          blockWeight2 (r : ZMod p) ((4 : ZMod p) ^ r)))) =
      -225 * WPFiniteInversion.R p 1 := by
    rw [WPFiniteInversion.R, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have h := first_carry_block_contraction (r : ZMod p) ((4 : ZMod p) ^ r) h2
      (WPFiniteInversion.denominator_ne_zero p r hr)
      (pow_ne_zero r (four_field_ne_zero p hp))
    simpa only [firstFCoeff, firstGCoeff, one_pow, mul_one, mul_one_div] using h
  rw [hs, WPFiniteInversion.R_one_eq_zero p (by omega), mul_zero]

/-- Complete first-carry convolution at the middle resonance of f^2. -/
theorem first_F_square_convolution (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (∑ r ∈ Finset.Ico 1 p, firstFCoeff p r * firstFCoeff p (p - r)) = 0 := by
  have hs : (∑ r ∈ Finset.Ico 1 p, firstFCoeff p r * firstFCoeff p (p - r)) =
      -4 * WPFiniteInversion.R p 1 := by
    rw [WPFiniteInversion.R, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [firstFCoeff_reflected p r hp hr]
    have hz := pow_ne_zero r (four_field_ne_zero p hp)
    have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
    unfold firstFCoeff firstGCoeff
    simp only [one_pow]
    field_simp [hz, hr0]
  rw [hs, WPFiniteInversion.R_one_eq_zero p (by omega), mul_zero]

/-- Complete first-carry convolution at the middle resonance of f*g. -/
theorem first_FG_convolution (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (∑ r ∈ Finset.Ico 1 p, firstFCoeff p r * firstGCoeff p (p - r)) =
      WPFiniteInversion.R p 16 := by
  have h4 := four_field_ne_zero p (by omega)
  have h16 : (16 : ZMod p) ≠ 0 := by
    rw [show (16 : ZMod p) = 4 ^ 2 by ring]
    exact pow_ne_zero _ h4
  have hs : (∑ r ∈ Finset.Ico 1 p, firstFCoeff p r * firstGCoeff p (p - r)) =
      16 * WPFiniteInversion.R p (16 : ZMod p)⁻¹ := by
    rw [WPFiniteInversion.R, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [firstGCoeff_reflected p r (by omega) hr]
    have hz := pow_ne_zero r h4
    have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
    have hpow : (16 : ZMod p) ^ r = ((4 : ZMod p) ^ r) ^ 2 := by
      rw [show (16 : ZMod p) = 4 * 4 by ring, mul_pow]
      ring
    unfold firstFCoeff
    rw [inv_pow, hpow]
    field_simp [hz, hr0]
    ring
  rw [hs, WPFiniteInversion.R_inversion p 16 h16, ZMod.pow_card]
  field_simp [h16]

theorem geometric_F_convolution (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (∑ r ∈ Finset.Ico 1 p, geometricCoeff p (p - r) * firstFCoeff p r) = 0 := by
  have h4 := four_field_ne_zero p hp
  have hs : (∑ r ∈ Finset.Ico 1 p, geometricCoeff p (p - r) * firstFCoeff p r) =
      -WPFiniteInversion.ell p 1 := by
    rw [WPFiniteInversion.ell, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    unfold geometricCoeff firstFCoeff
    rw [inv_pow, reflected_four_power p r hp hr]
    have hz := pow_ne_zero r h4
    have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
    simp only [one_pow]
    field_simp [h4, hz, hr0]
  rw [hs, WPFiniteInversion.ell_one_eq_zero p (by omega), neg_zero]

theorem geometric_G_convolution (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (∑ r ∈ Finset.Ico 1 p, geometricCoeff p (p - r) * firstGCoeff p r) =
      WPFiniteInversion.ell p 16 / 4 := by
  have h4 := four_field_ne_zero p hp
  rw [WPFiniteInversion.ell, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  unfold geometricCoeff firstGCoeff
  rw [inv_pow, reflected_four_power p r hp hr]
  have hz := pow_ne_zero r h4
  have hr0 := WPFiniteInversion.denominator_ne_zero p r hr
  have hpow : (16 : ZMod p) ^ r = ((4 : ZMod p) ^ r) ^ 2 := by
    rw [show (16 : ZMod p) = 4 * 4 by ring, mul_pow]
    ring
  rw [hpow]
  field_simp [h4, hz, hr0]

end WPMomentPrecision.BasePole
