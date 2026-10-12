import WPFirstResidue.CentralResidueAttachment
import WPFirstResidue.LaurentDifferential
import WPMomentPrecision.Conic.WPActualConicInfinityAttachment

open scoped Polynomial LaurentPolynomial LaurentSeries RatFunc
open Polynomial LaurentPolynomial WPActualNativeHasse WPActualNativeJetODE
  WPActualConicInfinitySource WPActualConicInfinityAttachment WPHasseIntegralTransport
  WPFirstResidue.CentralResidue WPFirstResidue.CentralResidueAttachment
  WPFirstResidue.LaurentDifferential WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.NativeResidue

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- Dropping the constant coefficient is the only correction to the finite
Euler primitive when its degree is strictly below the characteristic. -/
theorem eulerPrimitive_derivative_with_constant (p : ℕ) [Fact p.Prime]
    (G : (ZMod p)[X]) (hdeg : G.natDegree < p) :
    X * (WPActualPositivePair.eulerPrimitive p G).derivative =
      G - Polynomial.C (G.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, coeff_derivative, WPActualPositivePair.eulerPrimitive_coeff]
    simp only [coeff_sub, coeff_C]
    by_cases hc : G.coeff (n + 1) = 0
    · simp [hc]
    · have hn : n + 1 < p := (le_natDegree_of_ne_zero hc).trans_lt hdeg
      have hu : ((n + 1 : ℕ) : ZMod p) ≠ 0 :=
        WPActualGaussProper.small_cast_ne_zero p (n + 1) (by omega) hn
      have hu' : (n : ZMod p) + 1 ≠ 0 := by simpa using hu
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hu']
      simp

theorem actual_native_H_Euler_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    X * (nativeHField p).derivative = nativeField p (p / 6) - 1 := by
  have h := eulerPrimitive_derivative_with_constant p (nativeField p (p / 6))
    ((actual_native_field_degree p).trans_lt (by omega))
  rw [coeff_zero_eq_eval_zero, actual_native_field_origin, C_1] at h
  exact h

/-- Both logarithmic densities retain their original poles. -/
def logV (x : K) : K := 2 / (x - 1 / 4) + 1 / (x - 4)
def logQ (x : K) : K := 1 / (x - 1 / 4) + 2 / (x - 4) - 3 / x

theorem logV_native_form (x : K) (h4 : (4 : K) ≠ 0)
    (ha : x - 1 / 4 ≠ 0) :
    logV x = 8 / (4 * x - 1) + 1 / (x - 4) := by
  have ha' : 4 * x - 1 ≠ 0 := by
    have he : 4 * x - 1 = 4 * (x - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have he : 2 / (x - 1 / 4) = 8 / (4 * x - 1) := by
    field_simp [h4, ha, ha']
    ring
  exact congrArg (fun y : K => y + 1 / (x - 4)) he

theorem logQ_native_form (x : K) (h4 : (4 : K) ≠ 0)
    (ha : x - 1 / 4 ≠ 0) :
    logQ x = -3 / x - 2 / (4 - x) + 4 / (4 * x - 1) := by
  have ha' : 4 * x - 1 ≠ 0 := by
    have he : 4 * x - 1 = 4 * (x - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have he : 1 / (x - 1 / 4) = 4 / (4 * x - 1) := by
    field_simp [h4, ha, ha']
  have hn : 2 / (x - 4) = -2 / (4 - x) := by
    rw [← neg_sub 4 x, div_neg, neg_div]
  unfold logQ
  rw [he, hn]
  ring

section DifferentialAlgebra

variable {A : Type*} [Field A] [Algebra K A]

theorem derivation_V (D : Derivation K A A) (x : A) (hDx : D x = 1)
    (h4 : (4 : A) ≠ 0) (h125 : (125 : A) ≠ 0)
    (ha : x - 1 / 4 ≠ 0) (hb : x - 4 ≠ 0) :
    D (V x) = V x * logV x := by
  have ha' : 4 * x - 1 ≠ 0 := by
    have he : 4 * x - 1 = 4 * (x - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hb' : 4 - x ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  have derivativeFour := D.map_natCast 4
  change D (4 : A) = 0 at derivativeFour
  have derivative125 := D.map_natCast 125
  change D (125 : A) = 0 at derivative125
  simp [V, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_inv, smul_eq_mul, nsmul_eq_mul, hDx,
    derivativeFour, derivative125]
  unfold logV
  field_simp [h4, h125, ha, hb, ha', hb']
  ring

theorem derivation_Q (D : Derivation K A A) (x : A) (hDx : D x = 1)
    (hx : x ≠ 0) (h4 : (4 : A) ≠ 0) (h125 : (125 : A) ≠ 0)
    (ha : x - 1 / 4 ≠ 0) (hb : x - 4 ≠ 0) :
    D (Q x) = Q x * logQ x := by
  have ha' : 4 * x - 1 ≠ 0 := by
    have he : 4 * x - 1 = 4 * (x - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hb' : 4 - x ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  have derivativeFour := D.map_natCast 4
  change D (4 : A) = 0 at derivativeFour
  have derivative125 := D.map_natCast 125
  change D (125 : A) = 0 at derivative125
  simp [Q, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_inv, smul_eq_mul, nsmul_eq_mul, hDx,
    derivativeFour, derivative125]
  unfold logQ
  field_simp [hx, h4, h125, ha, hb, ha', hb']
  ring

end DifferentialAlgebra

variable (p : ℕ) [Fact p.Prime]

noncomputable def originalX : (ZMod p)⸨X⸩ := HahnSeries.single 1 1
noncomputable def nativeV : (ZMod p)⸨X⸩ := V (originalX p)
noncomputable def nativeQ : (ZMod p)⸨X⸩ := Q (originalX p)
noncomputable def nativeFV : (ZMod p)⸨X⸩ :=
  (nativeField p (p / 6)).eval₂ HahnSeries.C (nativeV p)
noncomputable def nativeFQ : (ZMod p)⸨X⸩ :=
  (nativeField p (p / 6)).eval₂ HahnSeries.C (nativeQ p)
noncomputable def nativeJV : (ZMod p)⸨X⸩ :=
  (nativeJetField p).eval₂ HahnSeries.C (nativeV p)
noncomputable def nativeHQ : (ZMod p)⸨X⸩ :=
  (nativeHField p).eval₂ HahnSeries.C (nativeQ p)
noncomputable def nativeRatio : (ZMod p)⸨X⸩ := nativeJV p / nativeFV p
noncomputable def nativeLogV : (ZMod p)⸨X⸩ := logV (originalX p)
noncomputable def nativeLogQ : (ZMod p)⸨X⸩ := logQ (originalX p)

theorem originalX_rational :
    algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
      (variableRat : RatFunc (ZMod p)) = originalX p := by
  simpa only [variableRat, RatFunc.algebraMap_X, originalX] using
    (RatFunc.coe_X (F := ZMod p))

theorem originalX_ne_zero : originalX p ≠ 0 := by
  rw [← originalX_rational]
  exact (_root_.map_ne_zero _).mpr variableRat_ne_zero

theorem originalX_sub_constant_ne_zero (a : ZMod p) :
    originalX p - HahnSeries.C a ≠ 0 := by
  have h := (_root_.map_ne_zero (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩)).mpr
    (variableRat_sub_constant_ne_zero a)
  simpa only [map_sub, originalX_rational, rational_coefficient_series] using h

theorem originalX_pole_units :
    originalX p - 1 / 4 ≠ 0 ∧ originalX p - 4 ≠ 0 := by
  constructor
  · simpa only [map_div₀, map_one, map_ofNat] using originalX_sub_constant_ne_zero p (1 / 4)
  · simpa only [map_ofNat] using originalX_sub_constant_ne_zero p 4

theorem originalX_derivative :
    nativeDerivation (originalX p) = (1 : (ZMod p)⸨X⸩) := by
  rw [nativeDerivation_apply]
  ext j
  rw [derivative_coefficient]
  by_cases hj : j = 0
  · subst j; norm_num [originalX]
  · have hj' : j + 1 ≠ 1 := by omega
    simp [originalX, HahnSeries.coeff_one, hj, hj']

theorem series_small_unit (_hp : 19 ≤ p) (n : ℕ) (hn : 0 < n) (hnp : n < p) :
    (n : (ZMod p)⸨X⸩) ≠ 0 := by
  have h := WPActualGaussProper.small_cast_ne_zero p n hn hnp
  simpa only [map_natCast] using (_root_.map_ne_zero (HahnSeries.C (Γ := ℤ))).mpr h

theorem series_four_unit (hp : 19 ≤ p) : (4 : (ZMod p)⸨X⸩) ≠ 0 := by
  simpa only [Nat.cast_ofNat] using series_small_unit p hp 4 (by omega) (by omega)

theorem series_125_unit (hp : 19 ≤ p) : (125 : (ZMod p)⸨X⸩) ≠ 0 := by
  have h5 : (5 : (ZMod p)⸨X⸩) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using series_small_unit p hp 5 (by omega) (by omega)
  have he : (125 : (ZMod p)⸨X⸩) = 5 ^ 3 := by norm_num
  rw [he]
  exact pow_ne_zero 3 h5

theorem nativeV_ne_zero (hp : 19 ≤ p) : nativeV p ≠ 0 := by
  have ha := (originalX_pole_units p).1
  have hb := (originalX_pole_units p).2
  have hb' : 4 - originalX p ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  have h4 := series_four_unit p hp
  have h125 := series_125_unit p hp
  have ha' : 4 * originalX p - 1 ≠ 0 := by
    have he : 4 * originalX p - 1 = 4 * (originalX p - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  unfold nativeV V
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 ha') hb') h125

theorem nativeQ_ne_zero (hp : 19 ≤ p) : nativeQ p ≠ 0 := by
  have ha := (originalX_pole_units p).1
  have hb := (originalX_pole_units p).2
  have hb' : 4 - originalX p ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  have h4 := series_four_unit p hp
  have ha' : 4 * originalX p - 1 ≠ 0 := by
    have he : 4 * originalX p - 1 = 4 * (originalX p - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  unfold nativeQ Q
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hb') ha')
    (mul_ne_zero (series_125_unit p hp) (pow_ne_zero 3 (originalX_ne_zero p)))

theorem nativeV_derivative (hp : 19 ≤ p) :
    nativeDerivation (nativeV p) = nativeV p * nativeLogV p := by
  have derivativeFour : LaurentSeries.derivative (ZMod p) (4 : (ZMod p)⸨X⸩) = 0 := by
    simpa only [nativeDerivation_apply, Nat.cast_ofNat] using
      (nativeDerivation (K := ZMod p)).map_natCast 4
  have derivative125 : LaurentSeries.derivative (ZMod p) (125 : (ZMod p)⸨X⸩) = 0 := by
    simpa only [nativeDerivation_apply, Nat.cast_ofNat] using
      (nativeDerivation (K := ZMod p)).map_natCast 125
  have derivativeX : LaurentSeries.derivative (ZMod p) (originalX p) = 1 := by
    simpa only [nativeDerivation_apply] using originalX_derivative p
  have h4 := series_four_unit p hp
  have h125 := series_125_unit p hp
  have ha := (originalX_pole_units p).1
  have hb := (originalX_pole_units p).2
  have ha' : 4 * originalX p - 1 ≠ 0 := by
    have he : 4 * originalX p - 1 = 4 * (originalX p - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hb' : 4 - originalX p ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  rw [nativeDerivation_apply]
  simp only [nativeV, V, div_eq_mul_inv, LaurentDifferential.derivative_mul,
    LaurentDifferential.derivative_pow, LaurentDifferential.derivative_inverse,
    map_sub, derivativeFour, derivative125, derivativeX,
    LaurentDifferential.derivative_one]
  unfold nativeLogV logV
  field_simp [h4, h125, ha, hb, ha', hb']
  ring

theorem nativeQ_derivative (hp : 19 ≤ p) :
    nativeDerivation (nativeQ p) = nativeQ p * nativeLogQ p := by
  have derivativeFour : LaurentSeries.derivative (ZMod p) (4 : (ZMod p)⸨X⸩) = 0 := by
    simpa only [nativeDerivation_apply, Nat.cast_ofNat] using
      (nativeDerivation (K := ZMod p)).map_natCast 4
  have derivative125 : LaurentSeries.derivative (ZMod p) (125 : (ZMod p)⸨X⸩) = 0 := by
    simpa only [nativeDerivation_apply, Nat.cast_ofNat] using
      (nativeDerivation (K := ZMod p)).map_natCast 125
  have derivativeX : LaurentSeries.derivative (ZMod p) (originalX p) = 1 := by
    simpa only [nativeDerivation_apply] using originalX_derivative p
  have h4 := series_four_unit p hp
  have h125 := series_125_unit p hp
  have hx := originalX_ne_zero p
  have ha := (originalX_pole_units p).1
  have hb := (originalX_pole_units p).2
  have ha' : 4 * originalX p - 1 ≠ 0 := by
    have he : 4 * originalX p - 1 = 4 * (originalX p - 1 / 4) := by field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hb' : 4 - originalX p ≠ 0 := by
    simpa only [neg_sub] using (neg_ne_zero.mpr hb)
  rw [nativeDerivation_apply]
  simp only [nativeQ, Q, div_eq_mul_inv, LaurentDifferential.derivative_mul,
    LaurentDifferential.derivative_pow, LaurentDifferential.derivative_inverse,
    map_sub, derivativeFour, derivative125, derivativeX,
    LaurentDifferential.derivative_one]
  unfold nativeLogQ logQ
  field_simp [hx, h4, h125, ha, hb, ha', hb']
  ring

theorem polynomial_derivative_at (P : (ZMod p)[X]) (z : (ZMod p)⸨X⸩) :
    nativeDerivation (P.eval₂ HahnSeries.C z) =
      P.derivative.eval₂ HahnSeries.C z * nativeDerivation z := by
  have hC : algebraMap (ZMod p) (ZMod p)⸨X⸩ = HahnSeries.C := by
    apply RingHom.ext
    intro a
    exact algebraMap_constant a
  simpa only [nativeDerivation_apply, hC] using
    derivative_polynomial_evaluation P z

theorem actual_native_HQ_differential (hp : 19 ≤ p) :
    nativeDerivation (nativeHQ p) = (nativeFQ p - 1) * nativeLogQ p := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval₂ HahnSeries.C (nativeQ p))
    (actual_native_H_Euler_source p hp)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub,
    Polynomial.eval₂_one] at he
  rw [nativeHQ, polynomial_derivative_at, nativeQ_derivative p hp]
  unfold nativeFQ
  linear_combination nativeLogQ p * he

/-- Global rational nonvanishing is proved at V(1/4)=0; no CM value is
required to be a unit, including in the odd prime class. -/
theorem nativeFV_ne_zero (hp : 19 ≤ p) : nativeFV p ≠ 0 := by
  let F := nativeField p (p / 6)
  let P := F.comp (fieldV p)
  have h4 : (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hv : (fieldV p).eval (1 / 4) = 0 := by
    simp only [fieldV, eval_mul, eval_C, eval_pow, eval_sub, eval_ofNat, eval_X,
      eval_one]
    have he : (4 : ZMod p) * (1 / 4) - 1 = 0 := by field_simp [h4]; ring
    rw [he]
    simp
  have hP : P ≠ 0 := by
    intro hz
    have he := congrArg (fun A : (ZMod p)[X] => A.eval (1 / 4)) hz
    rw [show P = F.comp (fieldV p) from rfl, eval_comp, hv] at he
    simp only [F, actual_native_field_origin, eval_zero] at he
    exact one_ne_zero he
  have he := (_root_.map_ne_zero (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩)).mpr
    (RatFunc.algebraMap_ne_zero hP)
  have hV : (fieldV p).eval₂ HahnSeries.C (originalX p) = nativeV p := by
    simpa only [Polynomial.eval_map, nativeV] using fieldV_eval p HahnSeries.C (originalX p)
  have hpoly (G : (ZMod p)[X]) :
      algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) G) =
      G.eval₂ HahnSeries.C (originalX p) := by
    induction G using Polynomial.induction_on' with
    | add A B hA hB =>
      rw [map_add, map_add, hA, hB, eval₂_add]
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
        RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, rational_coefficient_series]
      simp only [RatFunc.algebraMap_X, RatFunc.coe_X, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X, originalX]
  rw [hpoly, show P = F.comp (fieldV p) from rfl, Polynomial.eval₂_comp, hV] at he
  simpa only [nativeFV, F] using he

theorem actual_native_series_reciprocity (hp : 19 ≤ p) :
    nativeFV p = originalX p ^ ((p - 1) / 2) * nativeFQ p := by
  simpa only [Polynomial.eval_map, nativeFV, nativeFQ, nativeV, nativeQ, V, Q] using
    native_reciprocal_evaluation p (by omega)
    (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) (originalX p) (originalX_ne_zero p)

theorem actual_native_negative_jet_source (hp : 19 ≤ p) :
    (originalX p)⁻¹ ^ ((p - 1) / 2) * nativeJV p = nativeRatio p * nativeFQ p := by
  have h := actual_native_series_reciprocity p hp
  unfold nativeRatio
  rw [inv_pow]
  field_simp [nativeFV_ne_zero p hp, originalX_ne_zero p]
  linear_combination nativeJV p * h

theorem original_rational_coefficients :
    (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩).comp
      (algebraMap (ZMod p) (RatFunc (ZMod p))) = HahnSeries.C := by
  apply RingHom.ext
  intro a
  rw [RingHom.comp_apply, rational_coefficient_series]

theorem actual_original_inverted_density (hp : 19 ≤ p) :
    algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (nativeJetInvertedRationalDensity p) =
      nativeRatio p * nativeDerivation (nativeHQ p) + nativeRatio p * nativeLogQ p := by
  have hs : algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (nativeJetInvertedRationalDensity p) =
      (originalX p)⁻¹ ^ ((p - 1) / 2) * nativeJV p * nativeLogQ p := by
    simp only [nativeJetInvertedRationalDensity, map_mul, map_pow, map_inv₀,
      Polynomial.hom_eval₂, original_rational_coefficients, V, map_div₀,
      map_sub, map_ofNat, map_one, map_add, originalX_rational,
      nativeJV, nativeV, nativeLogQ, logQ]
  rw [hs, actual_native_negative_jet_source p hp, actual_native_HQ_differential p hp]
  ring

noncomputable def actualIu : ZMod p :=
  (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (nativeJetInvertedRationalDensity p)).coeff (-1)
noncomputable def actualC : ZMod p :=
  (nativeHQ p * nativeDerivation (nativeRatio p)).coeff (-1)

/-- The whole actual negative lift is integrated locally, with its full
principal part. There is no assigned residue or source-identity premise. -/
theorem actual_Iu_integration_by_parts (hp : 19 ≤ p) :
    actualIu p = -actualC p + (nativeRatio p * nativeLogQ p).coeff (-1) := by
  have hi := residue_integration_by_parts (nativeRatio p) (nativeHQ p)
  change (nativeRatio p * nativeDerivation (nativeHQ p)).coeff (-1) =
    -(nativeDerivation (nativeRatio p) * nativeHQ p).coeff (-1) at hi
  rw [mul_comm (nativeDerivation (nativeRatio p))] at hi
  rw [actualIu, actual_original_inverted_density p hp, HahnSeries.coeff_add, hi]
  rfl

end WPFirstResidue.NativeResidue
