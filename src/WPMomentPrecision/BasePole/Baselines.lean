import WPMomentPrecision.BasePole.FieldContractions

open scoped BigOperators

namespace WPMomentPrecision.BasePole

/-- The exact four-resonance primitive; its argument is the actual 2^p. -/
def baseBaseline (l : ℚ) : ℚ :=
  (2 * l ^ 9 - 20 * l ^ 5 + 40 * l ^ 3 - 30 * l + 8 / l) / 15

/-- The endpoint resonant baseline, kept without a logarithmic derivative ratio. -/
def endpointBaseline (l : ℚ) : ℚ :=
  2 / 15 * (l ^ 7 - 5 * l ^ 3 + 5 * l - l⁻¹ ^ 3)

def baseTaylorRemainder (t : ℚ) : ℚ :=
  79932 + 205760 * t + 254208 * t ^ 2 + 214400 * t ^ 3 +
    122880 * t ^ 4 + 46080 * t ^ 5 + 10240 * t ^ 6 + 1024 * t ^ 7

def endpointTaylorRemainder (t : ℚ) : ℚ :=
  33903 + 116800 * t + 210320 * t ^ 2 + 256128 * t ^ 3 +
    214720 * t ^ 4 + 122880 * t ^ 5 + 46080 * t ^ 6 +
      10240 * t ^ 7 + 1024 * t ^ 8

/-- A finite rational identity, so the full third-order remainder is explicit. -/
theorem baseBaseline_exact_taylor (t : ℚ) (hu : 1 + t ≠ 0) :
    baseBaseline (2 * (1 + t)) =
      216 / 5 + 2304 / 5 * t + 10476 / 5 * t ^ 2 +
        t ^ 3 * baseTaylorRemainder t / (15 * (1 + t)) := by
  unfold baseBaseline baseTaylorRemainder
  field_simp [hu]
  ring

/-- This identity uses no denominator 29 and retains the actual endpoint normalization. -/
theorem endpointBaseline_exact_taylor (t : ℚ) (hu : 1 + t ≠ 0) :
    16 / 125 * (1 + t) ^ 2 * endpointBaseline (2 * (1 + t)) =
      1044 / 625 + 10476 / 625 * t +
        4 * t ^ 2 * endpointTaylorRemainder t / (1875 * (1 + t)) := by
  unfold endpointBaseline endpointTaylorRemainder
  field_simp [hu]
  ring

theorem inverse_cube_exact_taylor (t : ℚ) (hu : 1 + t ≠ 0) :
    (1 + t)⁻¹ ^ 3 = 1 - 3 * t + 6 * t ^ 2 -
      t ^ 3 * (10 + 15 * t + 6 * t ^ 2) / (1 + t) ^ 3 := by
  field_simp [hu]
  ring

theorem inverse_first_exact_taylor (t : ℚ) (hu : 1 + t ≠ 0) :
    (1 + t)⁻¹ = 1 - t + t ^ 2 / (1 + t) := by
  field_simp [hu]
  ring

/-- The full finite logarithm at 16 is reduced using the original integer quotients. -/
theorem actual_beta_fermat (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteInversion.ell p 16 =
      15 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) +
        15 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) -
          64 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have small (a : ℕ) (ha : 0 < a) (hap : a < p) : (a : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p a (Finset.mem_Ico.mpr ⟨ha, hap⟩)
  have h3 := small 3 (by omega) (by omega)
  have h4 := small 4 (by omega) (by omega)
  have h5 := small 5 (by omega) (by omega)
  have h15 := small 15 (by omega) (by omega)
  have h16 := small 16 (by omega) (by omega)
  have hq16 := WPActualNativeCMLogValues.integerFermatQuotient_product_cast p 4 4
    (by simpa using h4) (by simpa using h4)
  norm_num only [show (4 * 4 : ℤ) = 16 by norm_num] at hq16
  rw [WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)] at hq16
  have hq15 := WPActualNativeCMLogValues.integerFermatQuotient_product_cast p 3 5
    (by simpa using h3) (by simpa using h5)
  norm_num only [show (3 * 5 : ℤ) = 15 by norm_num] at hq15
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have heven : Even (p - 1) := by rcases hodd with ⟨m, hm⟩; exact ⟨m, by omega⟩
  have hqneg : WPFiniteInversion.integerFermatQuotient p (-15) =
      WPFiniteInversion.integerFermatQuotient p 15 := by
    unfold WPFiniteInversion.integerFermatQuotient
    rw [heven.neg_pow]
  have he := WPFiniteInversion.entropyQuotient_eq_fermat p 16
    (by simpa using h16) (by
      norm_num only [show (1 - 16 : ℤ) = -15 by norm_num]
      simpa only [Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat] using neg_ne_zero.mpr h15)
  rw [show (1 - 16 : ℤ) = -15 by norm_num, hqneg] at he
  have hel := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) 16
  rw [he] at hel
  norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_mul, Int.cast_sub,
    neg_neg, sub_neg_eq_add] at hel
  rw [hq16, hq15] at hel
  linear_combination hel

end WPMomentPrecision.BasePole
