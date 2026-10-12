import WPFieldAssembly.NativeDiscriminant
import WPActualChiSource
import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential WPActualLogarithmicEta
  WPActualEtaPole WPActualPullbackSource WPActualChiSource WPActualNativeFirstIntegral
  WPHasseCubicSource

namespace WPFieldAssembly.NativeChiCovariance

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable def c2 : ℚ[X] := Polynomial.C (4 / 125) * (Polynomial.X + 1) * cubicDiscriminant ^ 2
noncomputable def c1 : ℚ[X] :=
  Polynomial.C (2 / 125) * cubicDiscriminant ^ 2 +
    Polynomial.C (4 / 125) * (Polynomial.X + 1) * cubicDiscriminant * (17 - 8 * Polynomial.X)
noncomputable def c0 : ℚ[X] := -Polynomial.C (1 / 25) * cubicNumerator

noncomputable def concomitantPoly (f g : ℚ[X]) : ℚ[X] :=
  c2 * (f * g.derivative.derivative + g * f.derivative.derivative - f.derivative * g.derivative) +
    c1 * (f * g.derivative + g * f.derivative) + c0 * f * g

noncomputable def concomitant (f g : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  c2.toLaurent * (f * D (D g) + g * D (D f) - D f * D g) +
    c1.toLaurent * (f * D g + g * D f) + c0.toLaurent * f * g

noncomputable def r0 : ℚ[T;T⁻¹] :=
  C (1 / 2 : ℚ) * (T (-1) * c1.toLaurent - T (-1) ^ 2 * c2.toLaurent)
noncomputable def r1 : ℚ[T;T⁻¹] := C (1 / 2 : ℚ) * T (-1) * c2.toLaurent
noncomputable def metric : ℚ[T;T⁻¹] := C (1 / 4 : ℚ) * T (-1) ^ 2 * c2.toLaurent

noncomputable def forcing (f : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] := r0 * f ^ 2 + r1 * f * D f
noncomputable def forcingCross (f g : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  2 * r0 * f * g + r1 * (f * D g + g * D f)

theorem ratify_T (n : ℤ) : ratify (T n) = rationalVariable ^ n := by
  rw [ratify, LaurentPolynomial.eval₂_T]
  exact Units.val_zpow_eq_zpow_val _ n

theorem concomitant_toLaurent (f g : ℚ[X]) :
    concomitant f.toLaurent g.toLaurent = (concomitantPoly f g).toLaurent := by
  simp only [concomitant, concomitantPoly, D_toLaurent, map_add, map_sub, map_mul]

/-- The literal self concomitant is the whole transported native norm. -/
theorem self_native_pullback (P : ℚ[X]) :
    concomitant (P.comp Vpolynomial).toLaurent (P.comp Vpolynomial).toLaurent =
      ((Polynomial.C (1 / 2 : ℚ) * Polynomial.X * nativeDiscriminant P).comp Vpolynomial).toLaurent := by
  rw [concomitant_toLaurent]
  have hd2 : (P.comp Vpolynomial).derivative.derivative =
      P.derivative.derivative.comp Vpolynomial * Vpolynomial.derivative ^ 2 +
        P.derivative.comp Vpolynomial * Vpolynomial.derivative.derivative := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_comp]
    ring
  simp only [concomitantPoly, hd2]
  simp only [Polynomial.derivative_comp, nativeDiscriminant,
    Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp,
    Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.one_comp, Polynomial.ofNat_comp]
  generalize P.comp Vpolynomial = F
  generalize P.derivative.comp Vpolynomial = G
  generalize P.derivative.derivative.comp Vpolynomial = H
  apply ratify_injective
  simp [c2, c1, c0, cubicDiscriminant, cubicNumerator, Vpolynomial,
    Polynomial.derivative_mul, Polynomial.derivative_pow_succ,
    Polynomial.toLaurent_X, ratify_C, ratify_T, map_ofNat]
  ring

theorem D_T (n : ℤ) : D (T n : ℚ[T;T⁻¹]) = C (n : ℚ) * T n * T (-1) := by
  simpa only [map_one, one_mul, T_sub, mul_assoc] using D_monomial (1 : ℚ) n

theorem D_inverse_square (f : ℚ[T;T⁻¹]) :
    D (invert f) = -T (-1) ^ 2 * invert (D f) := by
  have ht : (T (-1) : ℚ[T;T⁻¹]) ^ 2 = T (-2) := by norm_num [T_pow]
  simpa only [ht, neg_mul] using D_invert f

/-- The two rational gauge corrections remain at every integer reciprocal weight. -/
theorem reciprocal_self_covariance (n : ℤ) (f : ℚ[T;T⁻¹]) :
    let w := T n * invert f
    let r : ℚ := 2 * (n : ℚ) + 1
    concomitant w w = T n ^ 2 * T 1 * invert (concomitant f f) +
      C (2 * r) * forcing w - C (r ^ 2) * metric * w ^ 2 := by
  dsimp only
  have hz : D (T (-1) : ℚ[T;T⁻¹]) = -T (-1) ^ 2 := by
    simpa only [Int.cast_neg, Int.cast_one, map_neg, map_one,
      neg_one_mul, neg_mul, pow_two, one_mul] using D_T (-1)
  have hd1 : D (T n * invert f) =
      T n * (C (n : ℚ) * T (-1) * invert f - T (-1) ^ 2 * invert (D f)) := by
    rw [D_mul, D_T, D_inverse_square]
    ring
  have hd2 : D (D (T n * invert f)) =
      T n * (C ((n : ℚ) * ((n : ℚ) - 1)) * T (-1) ^ 2 * invert f +
        C (2 * (1 - (n : ℚ))) * T (-1) ^ 3 * invert (D f) +
        T (-1) ^ 4 * invert (D (D f))) := by
    rw [hd1, D_mul, D_T]
    have hDone : D (1 : ℚ[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : ℚ)
    simp only [pow_succ, pow_zero, map_sub, D_mul,
      D_C, hz, D_inverse_square, hDone, zero_mul, zero_add, map_mul, map_one, map_ofNat]
    ring
  simp only [concomitant, forcing, r0, r1, metric]
  simp only [hd2]
  simp only [hd1]
  apply ratify_injective
  simp only [c2, c1, c0, cubicDiscriminant, cubicNumerator, map_add, map_sub,
    map_mul, map_pow, map_neg, map_one, map_ofNat, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, invert_C, invert_T, ratify_C, ratify_T, map_div₀, map_intCast]
  field_simp [rationalVariable_ne_zero]
  ring

/-- Polarization is exact before division by the actual rational prime. -/
theorem reciprocal_difference_identity (n : ℤ) (p : ℚ) (f χ : ℚ[T;T⁻¹])
    (hp : p = 2 * (n : ℚ) + 1) (hχ : C p * χ = f - T n * invert f) :
    C (2 * p) * (concomitant f χ + forcing f) =
      concomitant f f - T n ^ 2 * T 1 * invert (concomitant f f) +
      C (p ^ 2) * (concomitant χ χ + 2 * forcingCross f χ -
        C (2 * p) * forcing χ + metric * (T n * invert f) ^ 2) := by
  have hc := reciprocal_self_covariance n f
  dsimp only at hc
  rw [← hp] at hc
  have hw : T n * invert f = f - C p * χ := by linear_combination hχ
  rw [hw] at hc ⊢
  simp only [concomitant, forcing, forcingCross, map_sub, map_add, D_C_mul,
    map_mul, map_pow, map_ofNat] at hc ⊢
  linear_combination -hc

theorem actual_chi_numerator (p N e : ℕ) (hpq : (p : ℚ) ≠ 0) :
    C (p : ℚ) * chiX p N e = Fpull e Vx - T (N : ℤ) * invert (Fpull e Vx) := by
  rw [chiX, ← Fpull_reciprocal e, ← mul_assoc]
  rw [← map_mul, mul_one_div_cancel hpq, map_one, one_mul]

/-- The complete actual V/Q covariance at its unchanged literal cutoff. -/
theorem actual_chi_concomitant_cleared (p N e : ℕ)
    (hpq : (p : ℚ) ≠ 0) (hN : p = 2 * N + 1) :
    let f := Fpull e Vx
    let χ := chiX p N e
    let w := T (N : ℤ) * Fpull e Qx
    C (2 * (p : ℚ)) * (concomitant f χ + forcing f) =
      concomitant f f - T (p : ℤ) * invert (concomitant f f) +
      C ((p : ℚ) ^ 2) * (concomitant χ χ + 2 * forcingCross f χ -
        C (2 * (p : ℚ)) * forcing χ + metric * w ^ 2) := by
  dsimp only
  have hr : (p : ℚ) = 2 * ((N : ℤ) : ℚ) + 1 := by exact_mod_cast hN
  have he := reciprocal_difference_identity (N : ℤ) (p : ℚ) (Fpull e Vx) (chiX p N e)
    hr (actual_chi_numerator p N e hpq)
  have ht : (T (N : ℤ) : ℚ[T;T⁻¹]) ^ 2 * T 1 = T (p : ℤ) := by
    rw [T_pow, ← T_add]
    congr 1
    exact_mod_cast hN.symm
  rw [ht, Fpull_reciprocal e] at he
  exact he

end WPFieldAssembly.NativeChiCovariance
