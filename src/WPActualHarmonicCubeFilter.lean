import WPActualHarmonicCubicTrace

open scoped BigOperators
open WPActualGaussBottom WPActualGaussProper WPActualCMGauss WPActualHarmonicCubicTrace

namespace WPActualHarmonicCubeFilter

theorem fieldHarmonic_Ico (p n : ℕ) :
    (∑ j ∈ Finset.Ico 1 (n + 1), (j : ZMod p)⁻¹) = fieldHarmonic p n := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  unfold fieldHarmonic
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm]

theorem cubic_filter_sum {M : Type*} [AddCommMonoid M] (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (f : ℕ → M) :
    (∑ j ∈ (Finset.Ico 1 p).filter (fun j => 3 ∣ j), f j) =
      ∑ r ∈ Finset.Ico 1 (p / 3 + 1), f (3 * r) := by
  have hc := prime_gauss_classes p hp
  have hs : (Finset.Ico 1 (p / 3 + 1)).image (fun r => 3 * r) =
      (Finset.Ico 1 p).filter (fun j => 3 ∣ j) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_filter]
    constructor
    · rintro ⟨r, ⟨hr0, hrk⟩, rfl⟩
      exact ⟨⟨by omega, by rcases hc with h | h <;> omega⟩, ⟨r, rfl⟩⟩
    · rintro ⟨⟨hj0, hjp⟩, ⟨r, hr⟩⟩
      refine ⟨r, ⟨by omega, ?_⟩, hr.symm⟩
      rcases hc with h | h <;> omega
  rw [← hs]
  apply Finset.sum_image
  intro r hr s hs he
  change 3 * r = 3 * s at he
  omega

theorem negative_sign_pair {K : Type*} [CommRing K] (j : ℕ) (hj : 1 ≤ j) :
    (-1 : K) ^ (j - 1) * (-1) ^ j = -1 := by
  have he : (-1 : K) ^ j = (-1) ^ (j - 1) * -1 := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  rw [he]
  have hs := negative_power_square (K := K) (j - 1)
  linear_combination -hs

theorem cubicQuotientSum_cast (p : ℕ) [Fact p.Prime] (s : ℤ) :
    (cubicQuotientSum p s : ZMod p) = ∑ j ∈ Finset.Ico 1 p,
      if 3 ∣ j then (-1 : ZMod p) ^ (j - 1) / (j : ZMod p) * (s : ZMod p) ^ j else 0 := by
  unfold cubicQuotientSum
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h3 : 3 ∣ j
  · simp only [h3, ite_true, WPFiniteInversion.divided_choose_cast p j hj]
  · simp [h3]

theorem cubicQuotientSum_minus_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    3 * (cubicQuotientSum p (-1) : ZMod p) = -fieldHarmonic p (p / 3) := by
  have he : (cubicQuotientSum p (-1) : ZMod p) =
      ∑ j ∈ Finset.Ico 1 p, if 3 ∣ j then -(j : ZMod p)⁻¹ else 0 := by
    rw [cubicQuotientSum_cast]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h3 : 3 ∣ j
    · simp only [h3, ite_true, Int.cast_neg, Int.cast_one, div_eq_mul_inv]
      have hs := negative_sign_pair (K := ZMod p) j (Finset.mem_Ico.mp hj).1
      linear_combination (j : ZMod p)⁻¹ * hs
    · simp [h3]
  rw [he, ← Finset.sum_filter, cubic_filter_sum p hp, Finset.mul_sum]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  calc
    _ = ∑ r ∈ Finset.Ico 1 (p / 3 + 1), -(r : ZMod p)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hu : (r : ZMod p) ≠ 0 :=
        small_cast_ne_zero p r (Finset.mem_Ico.mp hr).1 (by have := (Finset.mem_Ico.mp hr).2; omega)
      push_cast
      field_simp
    _ = -fieldHarmonic p (p / 3) := by rw [Finset.sum_neg_distrib, fieldHarmonic_Ico]

theorem cubicQuotientSum_plus_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    3 * (cubicQuotientSum p 1 : ZMod p) =
      ∑ r ∈ Finset.Ico 1 (p / 3 + 1), (-1 : ZMod p) ^ (r - 1) / (r : ZMod p) := by
  rw [cubicQuotientSum_cast]
  simp only [Int.cast_one, one_pow, mul_one]
  rw [← Finset.sum_filter, cubic_filter_sum p hp, Finset.mul_sum]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 := (Finset.mem_Ico.mp hr).1
  have hu : (r : ZMod p) ≠ 0 :=
    small_cast_ne_zero p r hr0 (by have := (Finset.mem_Ico.mp hr).2; omega)
  have hs : (-1 : ZMod p) ^ (3 * r - 1) = (-1) ^ (r - 1) := by
    rw [show 3 * r - 1 = r - 1 + 2 * r by omega, pow_add,
      pow_mul, show (-1 : ZMod p) ^ 2 = 1 by ring, one_pow, mul_one]
  rw [hs]
  push_cast
  field_simp

end WPActualHarmonicCubeFilter
