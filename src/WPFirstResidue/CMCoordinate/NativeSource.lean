import WPFirstResidue.CMCoordinate.Branch
import WPFirstResidue.CMLogarithmicPole
import WPActualNativeCMFinitePart
import WPActualNativeFirstIntegral
import Mathlib.Tactic

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualCubicGauge WPActualGaussProper WPActualGaussBottom WPActualCMGauss
  WPActualNativeHasse WPActualNativeJetODE WPActualNativeCMSource
  WPActualNativeCMFinitePart WPActualNativeCMLogValues
  WPFirstResidue.CMCoordinate WPFirstResidue.NativeCMCoordinate

namespace WPFirstResidue.NativeCMCoordinate

variable {K : Type*} [Field K]

/-- The series used in the inverse construction is the original native V(x). -/
theorem nativeVSeries_original_rational :
    ((nativeVSeries : K⟦X⟧) : K⸨X⸩) =
      ((WPMomentPrecision.ConicCoordinates.V (RatFunc.X : RatFunc K) : RatFunc K) :
        K⸨X⸩) := by
  simp only [nativeVSeries, WPMomentPrecision.ConicCoordinates.V,
    map_pow, PowerSeries.coe_C,
    PowerSeries.coe_X, map_mul, map_sub,
    map_ofNat, map_one, RatFunc.coe_X, div_eq_mul_inv, map_inv₀]
  ring

/-- The regular part of dlog Q in the original x-coordinate. -/
noncomputable def nativeLogRegular : K⟦X⟧ :=
  -PowerSeries.C (2 : K) * (PowerSeries.C (4 : K) - PowerSeries.X)⁻¹ +
    PowerSeries.C (4 : K) * (PowerSeries.C (4 : K) * PowerSeries.X - 1)⁻¹

theorem nativeLogRegular_origin (h2 : (2 : K) ≠ 0) :
    PowerSeries.constantCoeff (nativeLogRegular : K⟦X⟧) = -9 / 2 := by
  have h4 : (4 : K) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1
    norm_num
  simp only [nativeLogRegular, map_add, map_mul, map_neg, map_sub,
    PowerSeries.constantCoeff_inv, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X, map_one]
  field_simp [h4]
  ring

theorem nativeLogRegular_actual_laurent (h2 : (2 : K) ≠ 0) :
    (HahnSeries.single (-1) (-3 : K) +
      ((nativeLogRegular : K⟦X⟧) : K⸨X⸩)) =
      -(3 : K⸨X⸩) / ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) -
        2 / (4 - ((PowerSeries.X : K⟦X⟧) : K⸨X⸩)) +
        4 / (4 * ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) - 1) := by
  have h4 : (4 : K) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have ha : PowerSeries.constantCoeff (PowerSeries.C (4 : K) - PowerSeries.X) ≠ 0 := by
    simpa using h4
  have hb : PowerSeries.constantCoeff
      (PowerSeries.C (4 : K) * PowerSeries.X - 1) ≠ 0 := by simp
  rw [nativeLogRegular, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_mul, PowerSeries.coe_neg,
    WPRationalInfinitySeries.powerSeries_inverse_cast _ ha,
    WPRationalInfinitySeries.powerSeries_inverse_cast _ hb]
  simp only [PowerSeries.coe_sub, PowerSeries.coe_mul,
    PowerSeries.coe_one, map_ofNat, div_eq_mul_inv]
  rw [PowerSeries.coe_X, HahnSeries.inv_single]
  norm_num only [inv_one]
  have hs : (HahnSeries.single (-1) (-3 : K) : K⸨X⸩) =
      -(3 : K⸨X⸩) * HahnSeries.single (-1) 1 := by
    have hc : (HahnSeries.C (-3 : K) : K⸨X⸩) = -(3 : K⸨X⸩) := by
      rw [map_neg, map_ofNat]
    rw [← hc, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  rw [hs]
  ring

/-- The local logarithmic coefficient is exactly Q'/Q, with Q the original
reciprocal native cubic and with its factor x^-3 retained. -/
theorem native_logarithmic_density_exact (x : K) (hx : x ≠ 0)
    (ha : 4 - x ≠ 0) (hb : 4 * x - 1 ≠ 0) :
    ((-2 * (4 - x) * (4 * x - 1) + 4 * (4 - x) ^ 2) * x -
        3 * (4 - x) ^ 2 * (4 * x - 1)) /
      ((4 - x) ^ 2 * (4 * x - 1) * x) =
      -3 / x - 2 / (4 - x) + 4 / (4 * x - 1) := by
  field_simp [hx, ha, hb]
  ring

theorem nativeDelta_actual_cubic_cleared (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    centerEvalHom (1 / 2 : K) (nativeDelta h2 h5 h11) (cubicA : K[X]) =
      (nativeVSeries : K⟦X⟧) *
        centerEvalHom (1 / 2 : K) (nativeDelta h2 h5 h11) (cubicH : K[X]) ^ 3 := by
  let d := nativeDelta h2 h5 h11
  have ht (P : K[X]) : centerEvalHom (1 / 2 : K) d P =
      (P.comp (C (1 / 2) + X)).eval₂ PowerSeries.C d := by
    simp [centerEvalHom, Polynomial.eval₂_comp]
  have hA : centerEvalHom (1 / 2 : K) d (cubicA : K[X]) =
      PowerSeries.C (4 : K) - PowerSeries.C (16 : K) * d +
        PowerSeries.C (64 : K) * d ^ 3 - PowerSeries.C (64 : K) * d ^ 4 := by
    rw [ht]
    change (centeredNumerator : K[X]).eval₂ PowerSeries.C d = _
    rw [centeredNumerator_exact h2]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, map_ofNat]
  have hH : centerEvalHom (1 / 2 : K) d (cubicH : K[X]) ^ 3 =
      (PowerSeries.C (5 : K) + PowerSeries.C (8 : K) * d) ^ 3 := by
    rw [ht, ← Polynomial.eval₂_pow]
    change (centeredDenominator : K[X]).eval₂ PowerSeries.C d = _
    rw [centeredDenominator_exact h2]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_X, map_ofNat]
  rw [hA, hH]
  exact (nativeDelta_cleared h2 h5 h11).symm

theorem actual_h2 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (2 : ZMod p) ≠ 0 :=
  small_cast_ne_zero p 2 (by omega) (by omega)

theorem actual_h3 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (3 : ZMod p) ≠ 0 :=
  small_cast_ne_zero p 3 (by omega) (by omega)

theorem actual_h5 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (5 : ZMod p) ≠ 0 :=
  small_cast_ne_zero p 5 (by omega) (by omega)

theorem actual_h11 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (11 : ZMod p) ≠ 0 :=
  small_cast_ne_zero p 11 (by omega) (by omega)

noncomputable def actualNativeDelta (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)⟦X⟧ :=
  nativeDelta (actual_h2 p hp) (actual_h5 p hp) (actual_h11 p hp)

theorem actualNativeDelta_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff (actualNativeDelta p hp) = 0 :=
  nativeDelta_origin (actual_h2 p hp) (actual_h5 p hp) (actual_h11 p hp)

theorem actualNativeDelta_coefficients (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.coeff 1 (actualNativeDelta p hp) = (15 / 16 : ZMod p) ∧
      PowerSeries.coeff 2 (actualNativeDelta p hp) = (45 / 32 : ZMod p) :=
  nativeDelta_coefficients (actual_h2 p hp) (actual_h5 p hp) (actual_h11 p hp)

theorem actualNativeDelta_linear_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    IsUnit (PowerSeries.coeff 1 (actualNativeDelta p hp)) :=
  nativeDelta_linear_unit (actual_h2 p hp) (actual_h3 p hp) (actual_h5 p hp)
    (actual_h11 p hp)

noncomputable def actualCMPolynomialSeries (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : (ZMod p)[X]) : (ZMod p)⟦X⟧ :=
  centerEvalHom (1 / 2 : ZMod p) (actualNativeDelta p hp) P

@[simp] theorem actualCMPolynomialSeries_origin (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (P : (ZMod p)[X]) :
    PowerSeries.constantCoeff (actualCMPolynomialSeries p hp P) = P.eval (1 / 2) :=
  centerEvalHom_origin _ _ (actualNativeDelta_origin p hp) P

noncomputable def actualCMRatFuncHom (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    RatFunc (ZMod p) →+* (ZMod p)⸨X⸩ :=
  centerRatFuncHom (1 / 2 : ZMod p) (actualNativeDelta p hp)
    (actualNativeDelta_origin p hp) (actualNativeDelta_linear_unit p hp)

@[simp] theorem actualCMRatFuncHom_polynomial (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (P : (ZMod p)[X]) :
    actualCMRatFuncHom p hp (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) P) =
      ((actualCMPolynomialSeries p hp P : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) :=
  centerRatFuncHom_polynomial _ _ _ _ P

@[simp] theorem actualCMRatFuncHom_C (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (a : ZMod p) : actualCMRatFuncHom p hp (RatFunc.C a) = HahnSeries.C a :=
  centerRatFuncHom_C _ a _ _ _

theorem actual_CM_cubic_argument (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCMRatFuncHom p hp
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) =
      ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) := by
  have hH : PowerSeries.constantCoeff (actualCMPolynomialSeries p hp
      (cubicH : (ZMod p)[X])) ≠ 0 := by
    rw [actualCMPolynomialSeries_origin, cubicH_center p hp]
    exact actual_h5 p hp
  have hHL : ((actualCMPolynomialSeries p hp (cubicH : (ZMod p)[X]) :
      (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) ≠ 0 := by
    intro hz
    have hs : actualCMPolynomialSeries p hp (cubicH : (ZMod p)[X]) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ)
        (by simpa only [PowerSeries.coe_zero] using hz)
    exact hH (by rw [hs]; simp)
  rw [map_div₀, map_pow, actualCMRatFuncHom_polynomial,
    actualCMRatFuncHom_polynomial]
  apply (div_eq_iff (pow_ne_zero 3 hHL)).mpr
  have he := congrArg (fun f : (ZMod p)⟦X⟧ ↦ (f : (ZMod p)⸨X⸩))
    (nativeDelta_actual_cubic_cleared (actual_h2 p hp) (actual_h5 p hp)
      (actual_h11 p hp))
  simpa only [actualCMPolynomialSeries, actualNativeDelta,
    PowerSeries.coe_mul, map_pow] using he

/-- This is the image of the retained actual nativeCMRational, not an assigned period. -/
noncomputable def actualCMSeries (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)⸨X⸩ := actualCMRatFuncHom p hp (nativeCMRational p)

/-- The complete original J_N and F_d are retained under the actual cubic branch. -/
theorem actual_CM_native_ratio (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualCMSeries p hp =
      (nativeJetField p).eval₂ (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩)
          ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) /
        (nativeField p (p / 6)).eval₂ (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩)
          ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) := by
  have hC : (actualCMRatFuncHom p hp).comp RatFunc.C = HahnSeries.C := by
    ext1 a
    rw [RingHom.comp_apply]
    exact actualCMRatFuncHom_C p hp a
  unfold actualCMSeries nativeCMRational
  rw [map_div₀, Polynomial.hom_eval₂, Polynomial.hom_eval₂, hC,
    actual_CM_cubic_argument]

/-- NC55 after the actual V substitution, with the full quotient Wronskian. -/
theorem actual_native_first_integral_at_V (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let v := ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)
    let E := Polynomial.eval₂RingHom (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) v
    v * (E (nativeField p (p / 6)) * E (nativeJetField p).derivative -
        E (nativeField p (p / 6)).derivative * E (nativeJetField p)) =
      E (nativeField p (p / 6)) *
        ((1 - v) ^ ((p - 1) / 2) - E (nativeField p (p / 6))) := by
  dsimp
  have he := congrArg
    (Polynomial.eval₂RingHom (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩)
      ((nativeVSeries : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩))
    (WPActualNativeFirstIntegral.actual_native_first_integral p hp)
  simpa only [map_mul, map_sub, map_pow, map_one, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X] using he

noncomputable def nativeBeta (p : ℕ) [Fact p.Prime] : ZMod p :=
  -2 * fieldHarmonic p (p / 6) +
    3 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)

noncomputable def nativeKappa (p : ℕ) [Fact p.Prime] : ZMod p :=
  44 / (5 * ((actualGauss p).derivative.eval (1 / 2)) ^ 2)

theorem nativeKappa_nonzero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hk : Odd (p / 3)) : nativeKappa p ≠ 0 := nativeCM_odd_pole_nonzero p hp hk

noncomputable def actualDeltaUnit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)⟦X⟧ := shiftedUnit (actualNativeDelta p hp)

theorem actualDeltaUnit_coefficients (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff (actualDeltaUnit p hp) = (15 / 16 : ZMod p) ∧
      PowerSeries.coeff 1 (actualDeltaUnit p hp) = (45 / 32 : ZMod p) := by
  simpa [actualDeltaUnit] using actualNativeDelta_coefficients p hp

theorem actualDeltaUnit_origin_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff (actualDeltaUnit p hp) ≠ 0 := by
  simpa [actualDeltaUnit] using (actualNativeDelta_linear_unit p hp).ne_zero

theorem actual_pole_in_native_coordinate (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (A : ZMod p) :
    HahnSeries.C A / ((actualNativeDelta p hp : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      HahnSeries.single (-1) A *
        (((actualDeltaUnit p hp)⁻¹ : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) := by
  have hf := shiftedUnit_factor (actualNativeDelta p hp) (actualNativeDelta_origin p hp)
  change actualNativeDelta p hp = PowerSeries.X * actualDeltaUnit p hp at hf
  rw [hf, PowerSeries.coe_mul, PowerSeries.coe_X, div_eq_mul_inv,
    mul_inv_rev, ← WPRationalInfinitySeries.powerSeries_inverse_cast _
      (actualDeltaUnit_origin_ne_zero p hp), HahnSeries.inv_single]
  rw [HahnSeries.C_apply]
  have hs : (HahnSeries.single (0 : ℤ) A : (ZMod p)⸨X⸩) *
      HahnSeries.single (-1) 1 = HahnSeries.single (-1) A := by
    rw [HahnSeries.single_mul_single]; simp
  norm_num only [neg_neg, inv_one]
  linear_combination hs *
    (((actualDeltaUnit p hp)⁻¹ : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)

/-- The full nonzero pole and the checked native finite part are transported
through the inverse-defined coordinate before taking a logarithmic residue. -/
theorem actual_native_CM_odd_series (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hk : Odd (p / 3)) :
    ∃ G : (ZMod p)⟦X⟧,
      actualCMSeries p hp = HahnSeries.single (-1) (nativeKappa p) *
        (((actualDeltaUnit p hp)⁻¹ : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) +
          (G : (ZMod p)⸨X⸩) ∧
      PowerSeries.constantCoeff G = nativeBeta p := by
  obtain ⟨U, R, hU, hsource, hvalue⟩ := actual_native_CM_odd_finite_part p hp hk
  let G := actualCMPolynomialSeries p hp R * (actualCMPolynomialSeries p hp U)⁻¹
  have hu : PowerSeries.constantCoeff (actualCMPolynomialSeries p hp U) ≠ 0 := by
    rwa [actualCMPolynomialSeries_origin]
  refine ⟨G, ?_, ?_⟩
  · have he := congrArg (actualCMRatFuncHom p hp) hsource
    simp only [map_add, map_div₀, actualCMRatFuncHom_C,
      actualCMRatFuncHom_polynomial] at he
    have hL : actualCMPolynomialSeries p hp (X - C (1 / 2)) = actualNativeDelta p hp := by
      simp [actualCMPolynomialSeries, centerEvalHom]
    have hκ : (HahnSeries.C (44 : ZMod p) : (ZMod p)⸨X⸩) /
        HahnSeries.C (5 * ((actualGauss p).derivative.eval (1 / 2)) ^ 2) =
          HahnSeries.C (nativeKappa p) :=
      (map_div₀ (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) _ _).symm
    rw [hκ, hL, actual_pole_in_native_coordinate] at he
    change actualCMSeries p hp = _ at he
    rw [show ((G : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
        ((actualCMPolynomialSeries p hp R : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) /
          ((actualCMPolynomialSeries p hp U : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) by
      change ((actualCMPolynomialSeries p hp R * (actualCMPolynomialSeries p hp U)⁻¹ :
        (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) = _
      rw [PowerSeries.coe_mul, WPRationalInfinitySeries.powerSeries_inverse_cast _ hu]
      rfl]
    exact he
  · change PowerSeries.constantCoeff
      (actualCMPolynomialSeries p hp R * (actualCMPolynomialSeries p hp U)⁻¹) = _
    rw [map_mul, PowerSeries.constantCoeff_inv, actualCMPolynomialSeries_origin,
      actualCMPolynomialSeries_origin]
    simpa only [nativeBeta, div_eq_mul_inv] using hvalue

theorem actual_native_CM_even_series (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (hk : Even (p / 3)) :
    ∃ G : (ZMod p)⟦X⟧, actualCMSeries p hp = (G : (ZMod p)⸨X⸩) ∧
      PowerSeries.constantCoeff G = nativeBeta p := by
  let N := actualCMPolynomialSeries p hp (nativeCMNumerator p)
  let D := actualCMPolynomialSeries p hp (nativeCMDenominator p)
  let G := N * D⁻¹
  have hu : PowerSeries.constantCoeff D ≠ 0 := by
    change PowerSeries.constantCoeff (actualCMPolynomialSeries p hp _) ≠ 0
    rw [actualCMPolynomialSeries_origin]
    simp only [nativeCMDenominator, Polynomial.eval_mul, Polynomial.eval_pow,
      cubicH_center p hp, ZMod.pow_card]
    exact mul_ne_zero (actual_h5 p hp)
      (WPActualNativeCMParity.actualGauss_CM_even_ne_zero p hp hk)
  refine ⟨G, ?_, ?_⟩
  · have hs : nativeCMRational p =
        algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeCMNumerator p) /
          algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeCMDenominator p) :=
      nativeCM_source_quotient p hp
    have he := congrArg (actualCMRatFuncHom p hp) hs
    rw [map_div₀, actualCMRatFuncHom_polynomial, actualCMRatFuncHom_polynomial] at he
    change actualCMSeries p hp = (N : (ZMod p)⸨X⸩) / (D : (ZMod p)⸨X⸩) at he
    change actualCMSeries p hp = ((N * D⁻¹ : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)
    rw [he, PowerSeries.coe_mul, WPRationalInfinitySeries.powerSeries_inverse_cast _ hu]
    rfl
  · change PowerSeries.constantCoeff (N * D⁻¹) = _
    rw [map_mul, PowerSeries.constantCoeff_inv]
    change PowerSeries.constantCoeff (actualCMPolynomialSeries p hp _) *
      (PowerSeries.constantCoeff (actualCMPolynomialSeries p hp _))⁻¹ = _
    rw [actualCMPolynomialSeries_origin, actualCMPolynomialSeries_origin]
    simpa only [nativeBeta, div_eq_mul_inv] using actual_native_CM_even_regular_value p hp hk

noncomputable def actualLogQSeries (p : ℕ) [Fact p.Prime] : (ZMod p)⸨X⸩ :=
  HahnSeries.single (-1) (-3 : ZMod p) +
    ((nativeLogRegular : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)

theorem actual_native_CM_odd_logarithmic_residue (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Odd (p / 3)) :
    (actualCMSeries p hp * actualLogQSeries p).coeff (-1) = -3 * nativeBeta p := by
  obtain ⟨G, hG, hbeta⟩ := actual_native_CM_odd_series p hp hk
  rw [hG, actualLogQSeries,
    WPFirstResidue.CMLogarithmicPole.complete_simple_pole_logarithmic_residue _ _ _ _
      (actualDeltaUnit_origin_ne_zero p hp), hbeta,
    (actualDeltaUnit_coefficients p hp).1, (actualDeltaUnit_coefficients p hp).2,
    nativeLogRegular_origin (actual_h2 p hp)]
  exact WPFirstResidue.CMLogarithmicPole.native_coordinate_pole_cancellation _ _
    (actual_h2 p hp) (actual_h3 p hp) (actual_h5 p hp)

theorem actual_native_CM_even_logarithmic_residue (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : Even (p / 3)) :
    (actualCMSeries p hp * actualLogQSeries p).coeff (-1) = -3 * nativeBeta p := by
  obtain ⟨G, hG, hbeta⟩ := actual_native_CM_even_series p hp hk
  rw [hG, actualLogQSeries, mul_add]
  simp only [HahnSeries.coeff_add]
  have hregular : (((G : (ZMod p)⸨X⸩) *
      ((nativeLogRegular : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩))).coeff (-1) = 0 := by
    rw [← PowerSeries.coe_mul, PowerSeries.coeff_coe]
    simp
  rw [hregular, add_zero, mul_comm, HahnSeries.coeff_single_mul]
  norm_num only
  simp [PowerSeries.coeff_coe, hbeta]

/-- Both prime classes use the same actual native quotient and original dlog Q. -/
theorem actual_native_CM_logarithmic_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualCMSeries p hp * actualLogQSeries p).coeff (-1) =
      6 * fieldHarmonic p (p / 6) -
        9 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) := by
  rcases Nat.even_or_odd (p / 3) with he | ho
  · rw [actual_native_CM_even_logarithmic_residue p hp he, nativeBeta]
    ring
  · rw [actual_native_CM_odd_logarithmic_residue p hp ho, nativeBeta]
    ring

end WPFirstResidue.NativeCMCoordinate
