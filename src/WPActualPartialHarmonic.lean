import WPActualHarmonicCubeFilter

open scoped BigOperators
open WPActualGaussBottom WPActualGaussProper WPActualHarmonicCubicTrace WPActualHarmonicCubeFilter

namespace WPActualPartialHarmonic

theorem even_filter_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ j ∈ (Finset.Ico 1 (n + 1)).filter (fun j => 2 ∣ j), f j) =
      ∑ r ∈ Finset.Ico 1 (n / 2 + 1), f (2 * r) := by
  have hs : (Finset.Ico 1 (n / 2 + 1)).image (fun r => 2 * r) =
      (Finset.Ico 1 (n + 1)).filter (fun j => 2 ∣ j) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_filter]
    constructor
    · rintro ⟨r, ⟨hr0, hrk⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨r, rfl⟩⟩
    · rintro ⟨⟨hj0, hjn⟩, ⟨r, hr⟩⟩
      exact ⟨r, ⟨by omega, by omega⟩, hr.symm⟩
  rw [← hs]
  apply Finset.sum_image
  intro r hr s hs he
  change 2 * r = 2 * s at he
  omega

theorem alternating_sign (j : ℕ) (hj : 1 ≤ j) :
    (-1 : ℤ) ^ (j - 1) = if 2 ∣ j then -1 else 1 := by
  by_cases hd : 2 ∣ j
  · rw [if_pos hd]
    rcases hd with ⟨r, hr⟩
    have ho : Odd (j - 1) := ⟨r - 1, by omega⟩
    exact ho.neg_one_pow
  · rw [if_neg hd]
    have hm : j % 2 = 1 := by
      have hn := Nat.mod_lt j (by omega : 0 < 2)
      have hdz : j % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hd
      omega
    have he : Even (j - 1) := ⟨j / 2, by have := Nat.mod_add_div j 2; omega⟩
    exact he.neg_one_pow

theorem alternating_harmonic (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hn : n < p) :
    (∑ j ∈ Finset.Ico 1 (n + 1), (-1 : ZMod p) ^ (j - 1) / (j : ZMod p)) =
      fieldHarmonic p n - fieldHarmonic p (n / 2) := by
  have hs : (∑ j ∈ Finset.Ico 1 (n + 1), (-1 : ZMod p) ^ (j - 1) / (j : ZMod p)) =
      (∑ j ∈ Finset.Ico 1 (n + 1), (j : ZMod p)⁻¹) -
        2 * (∑ j ∈ Finset.Ico 1 (n + 1), if 2 ∣ j then (j : ZMod p)⁻¹ else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have he := congrArg (fun z : ℤ => (z : ZMod p))
      (alternating_sign j (Finset.mem_Ico.mp hj).1)
    push_cast at he
    rw [he, div_eq_mul_inv]
    split_ifs <;> ring
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  rw [hs, fieldHarmonic_Ico, ← Finset.sum_filter, even_filter_sum, Finset.mul_sum]
  congr 1
  calc
    _ = ∑ r ∈ Finset.Ico 1 (n / 2 + 1), (r : ZMod p)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hu : (r : ZMod p) ≠ 0 :=
        small_cast_ne_zero p r (Finset.mem_Ico.mp hr).1 (by have := (Finset.mem_Ico.mp hr).2; omega)
      push_cast
      field_simp
    _ = _ := fieldHarmonic_Ico p (n / 2)

theorem cubicQuotientSum_minus_fermat (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) =
      2 * (cubicQuotientSum p (-1) : ZMod p) := by
  let q := cubicQuotientSum p (-1)
  let T := cubicTrace ((1 - cubicOmega) ^ p)
  have ht : T = 3 + 3 * (p : ℤ) * q := by
    have he := cubicQuotientSum_minus_source p hp
    change T - 3 = 3 * (p : ℤ) * q at he
    linear_combination he
  have hsq := cubicTrace_minus_prime_square p hp
  change T ^ 2 = 9 * (3 : ℤ) ^ (p - 1) at hsq
  rw [ht] at hsq
  have hnum : (3 : ℤ) ^ (p - 1) - 1 = 2 * (p : ℤ) * q + (p : ℤ) ^ 2 * q ^ 2 := by
    nlinarith [hsq]
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 3 (by simpa using h3)
  rw [hnum] at hq
  have hid : WPFiniteInversion.integerFermatQuotient p 3 = 2 * q + (p : ℤ) * q ^ 2 := by
    apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
    linear_combination hq
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hid
  simpa [q] using hz

theorem cubicQuotientSum_plus_fermat (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    3 * (cubicQuotientSum p 1 : ZMod p) =
      2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
  have hs := cubicQuotientSum_plus_source p hp
  have hp1 := (Fact.out : p.Prime).one_le
  have he : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [he] at hs
  have hid : 3 * cubicQuotientSum p 1 = 2 * WPFiniteInversion.integerFermatQuotient p 2 := by
    apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
    linear_combination -hs - 2 * hq
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hid
  simpa only [Int.cast_mul, Int.cast_ofNat] using hz

/-- The actual harmonic sum through floor(p/3), both prime classes. -/
theorem actual_harmonic_third (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    fieldHarmonic p (p / 3) =
      -(3 / 2 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have hq := cubicQuotientSum_minus_fermat p hp
  have hh := cubicQuotientSum_minus_field p hp
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  field_simp
  linear_combination 2 * hh + 3 * hq

/-- The exact harmonic sum through floor(p/6) from the same integral cubic filter. -/
theorem actual_harmonic_sixth (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    fieldHarmonic p (p / 6) =
      -2 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        (3 / 2 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have hq := cubicQuotientSum_plus_fermat p hp
  have hs := cubicQuotientSum_plus_field p hp
  rw [alternating_harmonic p (p / 3) hp (by omega)] at hs
  have hn : (p / 3) / 2 = p / 6 := by omega
  rw [hn, actual_harmonic_third p hp] at hs
  linear_combination hs - hq

end WPActualPartialHarmonic
