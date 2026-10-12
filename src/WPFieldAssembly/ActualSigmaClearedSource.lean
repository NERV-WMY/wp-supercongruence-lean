import WPFieldAssembly.ActualSigmaFiniteEvenSource
import WPFiniteZSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSigmaFiniteEvenSource

namespace WPFieldAssembly.ActualSigmaClearedSource

set_option maxHeartbeats 1400000

/- SB95 before p-division. Every finite logarithm keeps its degree-N term.
The comparison branch scalar is retained explicitly; its derivative is zero.
Attachment to the existing actualSigmaIntegral is a separate source equality. -/

noncomputable def originalMovingQ (p : ℕ) [Fact p.Prime] : ℚ[X] :=
  (finiteEvenSquaredQ p).comp (4 * WPFiniteWSource.squaredCoordinate) -
    (finiteEvenSquaredQ p).comp WPFiniteWSource.squaredCoordinate

noncomputable def originalEvenSumQ (p : ℕ) [Fact p.Prime] : ℚ[T;T⁻¹] :=
  (originalMovingQ p).toLaurent + invert (originalMovingQ p).toLaurent

noncomputable def originalPhaseQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 15 : ℚ) *
    (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ)))

noncomputable def originalComparisonQ (p : ℕ) [Fact p.Prime] (branch : ℚ) :
    ℚ[T;T⁻¹] :=
  originalPhaseQ p * originalEvenSumQ p + LaurentPolynomial.C branch

noncomputable def originalBQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1 / 2 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) *
    T (-(p : ℤ)) * (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^
      ((p - 1) / 2) * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) *
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1)

noncomputable def originalNormDifferenceQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (p : ℚ)) *
    (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ)) -
      LaurentPolynomial.C ((1 / 5 : ℚ) ^ (2 * (p - 1))) *
        T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p)

noncomputable def originalFourCarryQ (p : ℕ) : ℚ :=
  ((4 : ℚ) ^ ((p - 1) / 2) - 1) / (p : ℚ)

/-- The exact finite moving derivative, including its final degree-N carry. -/
theorem originalMovingQ_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]) * (originalMovingQ p).derivative =
      Polynomial.C (15 / 2 : ℚ) *
        ((WPFiniteWSource.squaredCoordinate : ℚ[X]) ^ ((p - 1) / 2) - 1) +
      Polynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) * (4 - X) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]) ^ ((p - 1) / 2) := by
  let s : ℚ[X] := WPFiniteWSource.squaredCoordinate
  let E : ℚ[X] := finiteEvenSquaredQ p
  have h4 := congrArg (fun F : ℚ[X] => F.comp (4 * s))
    (finiteEvenSquaredQ_source p hp)
  have h1 := congrArg (fun F : ℚ[X] => F.comp s)
    (finiteEvenSquaredQ_source p hp)
  simp only [mul_comp, ofNat_comp, sub_comp, one_comp, X_comp, pow_comp] at h4 h1
  simp only [Nat.cast_ofNat] at h4 h1
  have hd : s.derivative = Polynomial.C (1 / 5 : ℚ) := by
    norm_num [s, WPFiniteWSource.squaredCoordinate, derivative_mul,
      derivative_add, derivative_C, derivative_X, derivative_one]
  have hd4 : (4 * s).derivative = Polynomial.C (4 / 5 : ℚ) := by
    rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) from rfl, derivative_C_mul, hd,
      ← Polynomial.C_mul]
    congr 1
    norm_num
  have hp4 : (4 * s) ^ ((p - 1) / 2) =
      Polynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) * s ^ ((p - 1) / 2) := by
    rw [mul_pow, Polynomial.C_pow, map_ofNat]
  rw [hp4] at h4
  change 2 * (1 - 4 * s) * E.derivative.comp (4 * s) =
    1 - Polynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) * s ^ ((p - 1) / 2) at h4
  change 2 * (1 - s) * E.derivative.comp s = 1 - s ^ ((p - 1) / 2) at h1
  rw [originalMovingQ, derivative_sub]
  change (WPFiniteZSource.Abar : ℚ[X]) *
    ((E.comp (4 * s)).derivative - (E.comp s).derivative) = _
  rw [derivative_comp, derivative_comp, hd4, hd]
  have h5 : 5 * Polynomial.C (1 / 5 : ℚ) = (1 : ℚ[X]) := by
    rw [show (5 : ℚ[X]) = Polynomial.C (5 : ℚ) from rfl, ← map_mul]
    norm_num
  have h2 : 2 * Polynomial.C (1 / 2 : ℚ) = (1 : ℚ[X]) := by
    rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) from rfl, ← map_mul]
    norm_num
  have hc4 : Polynomial.C (4 / 5 : ℚ) = 4 * Polynomial.C (1 / 5 : ℚ) := by
    rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) from rfl, ← map_mul]
    congr 1
    norm_num
  have hn : Polynomial.C (15 / 2 : ℚ) = 15 * Polynomial.C (1 / 2 : ℚ) := by
    rw [show (15 : ℚ[X]) = Polynomial.C (15 : ℚ) from rfl, ← map_mul]
    congr 1
    norm_num
  have hc : Polynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) =
      2 * (Polynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) - 1) := by
    simp only [map_mul, map_sub, map_ofNat, map_one]
  have hf4 : (WPFiniteZSource.Abar : ℚ[X]) * Polynomial.C (4 / 5 : ℚ) =
      -2 * (4 - X) * (2 * (1 - 4 * s)) := by
    rw [hc4]
    dsimp only [s]
    rw [WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
    simp only [one_div] at h5 ⊢
    linear_combination -4 * (4 - X) * h5
  have hf1 : (WPFiniteZSource.Abar : ℚ[X]) * Polynomial.C (1 / 5 : ℚ) =
      Polynomial.C (1 / 2 : ℚ) * (4 * X - 1) * (2 * (1 - s)) := by
    dsimp only [s]
    rw [WPFiniteWSource.squaredCoordinate, WPFiniteZSource.Abar]
    simp only [one_div] at h5 h2 ⊢
    linear_combination (4 * X - 1) * h5 -
      (4 * X - 1) * (1 - Polynomial.C ((5 : ℚ)⁻¹) * (X + 1)) * h2
  calc
    _ = -2 * (4 - X) * (2 * (1 - 4 * s) * E.derivative.comp (4 * s)) -
        Polynomial.C (1 / 2 : ℚ) * (4 * X - 1) *
          (2 * (1 - s) * E.derivative.comp s) := by
      linear_combination E.derivative.comp (4 * s) * hf4 - E.derivative.comp s * hf1
    _ = -2 * (4 - X) * (1 - Polynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) *
        s ^ ((p - 1) / 2)) -
        Polynomial.C (1 / 2 : ℚ) * (4 * X - 1) * (1 - s ^ ((p - 1) / 2)) := by
      rw [h4, h1]
    _ = _ := by
      rw [hn, hc]
      change _ = 15 * Polynomial.C (1 / 2 : ℚ) * (s ^ ((p - 1) / 2) - 1) +
        2 * (Polynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) - 1) * (4 - X) *
          s ^ ((p - 1) / 2)
      linear_combination 2 * (4 - X) * (1 - s ^ ((p - 1) / 2)) * h2

/-- Reflection is applied to the full cleared source, including both end bands. -/
theorem originalEvenSumQ_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent * D (originalEvenSumQ p) =
      LaurentPolynomial.C (15 / 2 : ℚ) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) +
      LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        ((4 - T 1) - T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * (4 * T 1 - 1)) := by
  let A : ℚ[T;T⁻¹] := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let E : ℚ[T;T⁻¹] := (originalMovingQ p).toLaurent
  let sN : ℚ[T;T⁻¹] :=
    (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2)
  have hm := congrArg Polynomial.toLaurent (originalMovingQ_derivative p hp)
  simp only [map_mul, map_add, map_sub, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, map_ofNat, map_one, ← D_toLaurent] at hm
  have hc : (2 * (4 ^ ((p - 1) / 2) - 1) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) := by
    simp only [map_mul, map_sub, map_pow, map_ofNat, map_one]
  rw [hc] at hm
  change A * D E = LaurentPolynomial.C (15 / 2 : ℚ) * (sN - 1) +
    LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) * (4 - T 1) * sN at hm
  have hi := congrArg (fun F : ℚ[T;T⁻¹] => invert F) hm
  have hA : invert A = T (-2) * A := WPFiniteZSource.invert_Abar
  have hs : invert sN = T (-(((p - 1) / 2 : ℕ) : ℤ)) * sN :=
    WPFiniteZSource.invert_squared_power p
  simp only [map_mul, map_add, map_sub, map_one, invert_C, invert_T, map_ofNat,
    hA, hs] at hi
  have hcarry : LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) =
      2 * (LaurentPolynomial.C ((4 : ℚ) ^ ((p - 1) / 2)) - 1) := by
    simp only [map_mul, map_sub, map_ofNat, map_one]
  rw [← hcarry] at hi
  have ht : (T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) : ℚ[T;T⁻¹]) * T 1 =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  have hunit : (T 1 : ℚ[T;T⁻¹]) * T (-1) = 1 := by
    rw [← T_add]
    norm_num
  change A * D (E + invert E) = _
  rw [map_add, D_invert]
  linear_combination hm - hi +
    LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) *
      sN * (4 - T (-1)) * ht +
    LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) *
      sN * T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * hunit

/-- The phase derivative keeps the two nonunit resonances until p-division. -/
theorem originalPhaseQ_derivative (p : ℕ) :
    D (originalPhaseQ p) =
      LaurentPolynomial.C (-4 * (p : ℚ) / 15) *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  have h17 : D (17 : ℚ[T;T⁻¹]) = 0 := D_C (17 : ℚ)
  have hpos : D (4 * T (p : ℤ) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (4 * (p : ℚ)) * T ((p : ℤ) - 1) := by
    simpa only [map_ofNat, Int.cast_natCast] using D_monomial (4 : ℚ) (p : ℤ)
  have hneg : D (4 * T (-(p : ℤ)) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (-(4 * (p : ℚ))) * T (-(p : ℤ) - 1) := by
    simpa only [map_ofNat, Int.cast_neg, Int.cast_natCast, mul_neg] using
      D_monomial (4 : ℚ) (-(p : ℤ))
  rw [originalPhaseQ, D_C_mul, map_sub, map_sub, h17, hpos, hneg]
  simp only [map_neg]
  have hc : LaurentPolynomial.C (1 / 15 : ℚ) *
      LaurentPolynomial.C (4 * (p : ℚ)) = LaurentPolynomial.C (4 * (p : ℚ) / 15) := by
    rw [← map_mul]
    congr 1
    ring
  have hn : LaurentPolynomial.C (-4 * (p : ℚ) / 15) =
      -LaurentPolynomial.C (4 * (p : ℚ) / 15) := by
    rw [← map_neg]
    congr 1
    ring
  rw [hn]
  linear_combination -(T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * hc

/-- The literal phase and complete B source combine before any divided digit. -/
theorem originalSigma_numerator_cleared (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (branch : ℚ) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        (D (originalComparisonQ p branch) - originalBQ p) =
      LaurentPolynomial.C (1 / 2 : ℚ) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) *
        (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ)) -
          LaurentPolynomial.C ((1 / 5 : ℚ) ^ (2 * (p - 1))) * T (-(p : ℤ)) *
            (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p) +
      LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) * originalPhaseQ p *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        ((4 - T 1) - T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * (4 * T 1 - 1)) -
      LaurentPolynomial.C (4 * (p : ℚ) / 15) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * originalEvenSumQ p := by
  let A : ℚ[T;T⁻¹] := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let sN : ℚ[T;T⁻¹] :=
    (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2)
  have hm := originalEvenSumQ_derivative p hp
  have hk : LaurentPolynomial.C (15 / 2 : ℚ) * originalPhaseQ p =
      LaurentPolynomial.C (1 / 2 : ℚ) *
        (17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))) := by
    rw [originalPhaseQ, ← mul_assoc, ← map_mul]
    congr 2
    norm_num
  have hBA : A * originalBQ p =
      LaurentPolynomial.C (1 / 2 : ℚ) * sN *
        (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) *
        (LaurentPolynomial.C ((1 / 5 : ℚ) ^ (2 * (p - 1))) *
          T (-(p : ℤ)) * A ^ p) := by
    have hAp : A ^ p = A ^ (p - 1) * A := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    rw [hAp, originalBQ, map_mul]
    dsimp only [A, sN]
    ring
  have hneg : LaurentPolynomial.C (-4 * (p : ℚ) / 15) =
      -LaurentPolynomial.C (4 * (p : ℚ) / 15) := by
    rw [← map_neg]
    congr 1
    ring
  rw [originalComparisonQ, map_add, D_mul, D_C, add_zero,
    originalPhaseQ_derivative]
  rw [hneg]
  linear_combination originalPhaseQ p * hm - hBA +
    sN * (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) * hk

/-- SB95's exact rational cleared quotient, with the actual half-binomial factor canceled. -/
theorem originalSigma_quotient_cleared (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (branch : ℚ) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        (LaurentPolynomial.C (1 / (p : ℚ)) *
          (D (originalComparisonQ p branch) - originalBQ p)) =
      LaurentPolynomial.C (1 / 2 : ℚ) *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) * originalNormDifferenceQ p +
      LaurentPolynomial.C (2 * originalFourCarryQ p) * originalPhaseQ p *
        (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
        ((4 - T 1) - T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * (4 * T 1 - 1)) -
      LaurentPolynomial.C (4 / 15 : ℚ) *
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * originalEvenSumQ p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm := congrArg (fun F : ℚ[T;T⁻¹] => LaurentPolynomial.C (1 / (p : ℚ)) * F)
    (originalSigma_numerator_cleared p hp branch)
  have hc : LaurentPolynomial.C (1 / (p : ℚ)) *
      LaurentPolynomial.C (2 * ((4 : ℚ) ^ ((p - 1) / 2) - 1)) =
      LaurentPolynomial.C (2 * originalFourCarryQ p) := by
    rw [← map_mul, originalFourCarryQ]
    congr 1
    ring
  have hd : LaurentPolynomial.C (1 / (p : ℚ)) *
      LaurentPolynomial.C (4 * (p : ℚ) / 15) = LaurentPolynomial.C (4 / 15 : ℚ) := by
    rw [← map_mul]
    congr 1
    field_simp [hpq]
  rw [originalNormDifferenceQ]
  linear_combination hm +
    originalPhaseQ p *
      (WPFiniteWSource.squaredCoordinate : ℚ[X]).toLaurent ^ ((p - 1) / 2) *
      ((4 - T 1) - T (-(((p - 1) / 2 : ℕ) : ℤ) - 1) * (4 * T 1 - 1)) * hc -
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
      (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) * originalEvenSumQ p * hd

end WPFieldAssembly.ActualSigmaClearedSource
