import WPActualPartialHarmonic

open scoped BigOperators Polynomial
open Polynomial WPActualGaussBottom WPActualGaussProper WPActualNativeCubicPrimitive
  WPFiniteAffineLog WPActualPartialHarmonic

namespace WPActualNativeCMLogValues

theorem integerFermatQuotient_product_cast (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    (WPFiniteInversion.integerFermatQuotient p (a * b) : ZMod p) =
      (WPFiniteInversion.integerFermatQuotient p a : ZMod p) +
        (WPFiniteInversion.integerFermatQuotient p b : ZMod p) := by
  have hab : ((a * b : ℤ) : ZMod p) ≠ 0 := by simpa only [Int.cast_mul] using mul_ne_zero ha hb
  have hqa := WPFiniteInversion.integerFermatQuotient_mul p a ha
  have hqb := WPFiniteInversion.integerFermatQuotient_mul p b hb
  have hqab := WPFiniteInversion.integerFermatQuotient_mul p (a * b) hab
  have hae : a ^ (p - 1) = 1 + (p : ℤ) * WPFiniteInversion.integerFermatQuotient p a := by
    linear_combination -hqa
  have hbe : b ^ (p - 1) = 1 + (p : ℤ) * WPFiniteInversion.integerFermatQuotient p b := by
    linear_combination -hqb
  rw [mul_pow, hae, hbe] at hqab
  have hid : WPFiniteInversion.integerFermatQuotient p (a * b) =
      WPFiniteInversion.integerFermatQuotient p a + WPFiniteInversion.integerFermatQuotient p b +
        (p : ℤ) * WPFiniteInversion.integerFermatQuotient p a * WPFiniteInversion.integerFermatQuotient p b := by
    apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
    linear_combination hqab
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hid
  simpa using hz

theorem ell_half_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteInversion.ell p (1 / 2) = (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have he := WPFiniteInversion.ell_inversion p 2 h2
  rw [ZMod.pow_card, WPFiniteInversion.ell_two_eq_fermat p (by omega)] at he
  rw [one_div]
  calc
    WPFiniteInversion.ell p (2⁻¹) = -2⁻¹ * (-2 *
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)) := he
    _ = _ := by field_simp

theorem ell_neg_eight_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteInversion.ell p (-8) =
      24 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
        18 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 := small_cast_ne_zero p 4 (by omega) (by omega)
  have h8 : (-8 : ZMod p) ≠ 0 := neg_ne_zero.mpr (small_cast_ne_zero p 8 (by omega) (by omega))
  have h9 : (9 : ZMod p) ≠ 0 := small_cast_ne_zero p 9 (by omega) (by omega)
  have hqeight := integerFermatQuotient_product_cast p 2 4 (by simpa using h2) (by simpa using h4)
  norm_num only [show (2 * 4 : ℤ) = 8 by norm_num] at hqeight
  rw [WPFiniteInversion.integerFermatQuotient_four_cast p (by omega)] at hqeight
  have hqnine := integerFermatQuotient_product_cast p 3 3 (by simpa using h3) (by simpa using h3)
  norm_num only [show (3 * 3 : ℤ) = 9 by norm_num] at hqnine
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have heven : Even (p - 1) := by rcases hodd with ⟨m, hm⟩; exact ⟨m, by omega⟩
  have hqneg : WPFiniteInversion.integerFermatQuotient p (-8) =
      WPFiniteInversion.integerFermatQuotient p 8 := by
    unfold WPFiniteInversion.integerFermatQuotient
    rw [heven.neg_pow]
  have he := WPFiniteInversion.entropyQuotient_eq_fermat p (-8)
    (by simpa using h8) (by norm_num only [show (1 - (-8) : ℤ) = 9 by norm_num]; simpa using h9)
  rw [hqneg, show (1 - (-8) : ℤ) = 9 by norm_num] at he
  have hel := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) (-8)
  rw [he] at hel
  norm_num only [Int.cast_neg, Int.cast_ofNat, Int.cast_mul, Int.cast_sub, neg_neg] at hel
  rw [hqeight, hqnine] at hel
  linear_combination hel

theorem nativeUnitPrimitive_endpoint_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeUnitPrimitive p).eval 1 =
      -72 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        54 * (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  simp only [nativeUnitPrimitive, eval_sub, eval_mul, eval_add, eval_ofNat, eval_pow,
    eval_X, one_pow, eval_comp, eval_neg, LP_eval_eq, mul_one]
  change (4 + 8) * WPFiniteInversion.ell p 1 - 3 * WPFiniteInversion.ell p (-8) = _
  rw [WPFiniteInversion.ell_one_eq_zero p (by omega), ell_neg_eight_value p hp]
  ring

theorem nativeUnitPrimitive_center_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeUnitPrimitive p).eval (1 / 2) =
      -16 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) +
        15 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  simp only [nativeUnitPrimitive, eval_sub, eval_mul, eval_add, eval_ofNat, eval_pow,
    eval_X, eval_comp, eval_neg, LP_eval_eq, ZMod.pow_card]
  change (4 + 8 * (1 / 2 : ZMod p)) * WPFiniteInversion.ell p (1 / 2) -
    3 * WPFiniteInversion.ell p (-8 * (1 / 2)) = _
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have he : (-8 * (1 / 2) : ZMod p) = -4 := by field_simp; ring
  rw [he, ell_half_value p hp, WPFiniteInversion.ell_neg_four_eq_fermat p (by omega)]
  field_simp
  ring

noncomputable def nativeCMSourceConstant (p : ℕ) [Fact p.Prime] : ZMod p :=
  ((nativeUnitPrimitive p).eval (1 / 2) - 28 * fieldHarmonic p (p / 3) -
    (nativeUnitPrimitive p).eval 1 / 2) / 5

/-- Value of the coefficient-defined source constant; the native finite-part transport is separate. -/
theorem actual_native_CM_source_constant (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeCMSourceConstant p = -2 * fieldHarmonic p (p / 6) +
      3 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  unfold nativeCMSourceConstant
  rw [nativeUnitPrimitive_center_value p hp, nativeUnitPrimitive_endpoint_value p hp,
    actual_harmonic_third p (by omega), actual_harmonic_sixth p (by omega)]
  have h2 : (2 : ZMod p) ≠ 0 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := small_cast_ne_zero p 5 (by omega) (by omega)
  field_simp
  ring

end WPActualNativeCMLogValues
