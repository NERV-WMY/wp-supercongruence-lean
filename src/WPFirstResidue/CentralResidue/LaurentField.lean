import WPActualCentralNativeJet
import Mathlib.RingTheory.LaurentSeries

open scoped Polynomial LaurentPolynomial LaurentSeries RatFunc
open LaurentPolynomial WPActualChiSource WPActualEtaIntegrality WPLaurentIntegralResidue

namespace WPFirstResidue.CentralResidue

variable {K : Type*} [Field K]

noncomputable def variableRat : RatFunc K :=
  algebraMap K[X] (RatFunc K) Polynomial.X

theorem variableRat_ne_zero : (variableRat : RatFunc K) ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

/-- The Laurent inclusion uses the original x variable, before any inversion. -/
noncomputable def fieldRatify : K[T;T⁻¹] →+* RatFunc K :=
  LaurentPolynomial.eval₂ (algebraMap K (RatFunc K))
    (Units.mk0 variableRat variableRat_ne_zero)

/-- The reciprocal evaluation keeps the full negative-power support. -/
noncomputable def reciprocalRatify : K[T;T⁻¹] →+* RatFunc K :=
  LaurentPolynomial.eval₂ (algebraMap K (RatFunc K))
    (Units.mk0 variableRat⁻¹ (inv_ne_zero variableRat_ne_zero))

theorem fieldRatify_C (a : K) : fieldRatify (C a) = algebraMap K (RatFunc K) a := by
  rw [fieldRatify, eval₂_C]

theorem fieldRatify_T (j : ℤ) : fieldRatify (T j : K[T;T⁻¹]) = variableRat ^ j := by
  simp only [fieldRatify, eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem reciprocalRatify_C (a : K) :
    reciprocalRatify (C a) = algebraMap K (RatFunc K) a := by
  rw [reciprocalRatify, eval₂_C]

theorem reciprocalRatify_T (j : ℤ) :
    reciprocalRatify (T j : K[T;T⁻¹]) = variableRat⁻¹ ^ j := by
  simp only [reciprocalRatify, eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem fieldRatify_substitute (P : K[X]) (L : K[T;T⁻¹]) :
    fieldRatify (substituteOver P L) = P.eval₂ (algebraMap K (RatFunc K)) (fieldRatify L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    dsimp only [substituteOver] at hP hQ ⊢
    rw [Polynomial.eval₂_add, map_add, hP, hQ, Polynomial.eval₂_add]
  | monomial n a =>
    simp only [substituteOver, Polynomial.eval₂_monomial, map_mul, map_pow, fieldRatify_C]

theorem reciprocalRatify_substitute (P : K[X]) (L : K[T;T⁻¹]) :
    reciprocalRatify (substituteOver P L) =
      P.eval₂ (algebraMap K (RatFunc K)) (reciprocalRatify L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    dsimp only [substituteOver] at hP hQ ⊢
    rw [Polynomial.eval₂_add, map_add, hP, hQ, Polynomial.eval₂_add]
  | monomial n a =>
    simp only [substituteOver, Polynomial.eval₂_monomial, map_mul, map_pow, reciprocalRatify_C]

theorem reciprocalRatify_toLaurent (P : K[X]) :
    reciprocalRatify (Polynomial.toLaurent P) =
      P.eval₂ (algebraMap K (RatFunc K)) variableRat⁻¹ := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n a =>
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, reciprocalRatify_C,
      reciprocalRatify_T, zpow_natCast, Polynomial.eval₂_monomial]

theorem fieldRatify_toLaurent (P : K[X]) :
    fieldRatify (Polynomial.toLaurent P) =
      P.eval₂ (algebraMap K (RatFunc K)) variableRat := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n a =>
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, fieldRatify_C,
      fieldRatify_T, zpow_natCast, Polynomial.eval₂_monomial]

theorem fieldRatify_invert (P : K[T;T⁻¹]) :
    fieldRatify (invert P) = reciprocalRatify P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T j a =>
    simp only [map_mul, invert_C, invert_T, fieldRatify_C, fieldRatify_T,
      reciprocalRatify_C, reciprocalRatify_T, inv_zpow, zpow_neg]

theorem reciprocalRatify_invert (P : K[T;T⁻¹]) :
    reciprocalRatify (invert P) = fieldRatify P := by
  rw [← fieldRatify_invert, involutive_invert P]

theorem variableRat_sub_constant_ne_zero (a : K) :
    variableRat - algebraMap K (RatFunc K) a ≠ 0 := by
  have hP : (Polynomial.X - Polynomial.C a : K[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : K[X] => P.coeff 1) h
    simp at hc
  have h := RatFunc.algebraMap_ne_zero hP
  simpa only [map_sub, variableRat, RatFunc.algebraMap_C,
    ← RatFunc.algebraMap_eq_C] using h

theorem inverse_variableRat_sub_constant_ne_zero (a : K) :
    variableRat⁻¹ - algebraMap K (RatFunc K) a ≠ 0 := by
  have hP : (1 - Polynomial.C a * Polynomial.X : K[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : K[X] => P.coeff 0) h
    simp at hc
  have hf : (1 : RatFunc K) - algebraMap K (RatFunc K) a * variableRat ≠ 0 := by
    simpa only [map_sub, map_one, map_mul, variableRat, RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_eq_C] using
      (RatFunc.algebraMap_ne_zero hP)
  intro hz
  have hs := congrArg (fun y : RatFunc K => variableRat * y) (sub_eq_zero.mp hz)
  rw [mul_inv_cancel₀ variableRat_ne_zero] at hs
  apply hf
  linear_combination hs

noncomputable def rationalSeries (P : K[T;T⁻¹]) : K⸨X⸩ :=
  algebraMap (RatFunc K) K⸨X⸩ (fieldRatify P)

/-- The rational inclusion sends a coefficient to its literal constant
series. This proof uses the polynomial and power-series inclusions, avoiding
an incompatible base-field scalar-tower instance. -/
theorem rational_coefficient_series (a : K) :
    algebraMap (RatFunc K) K⸨X⸩ (algebraMap K (RatFunc K) a) = HahnSeries.C a := by
  rw [RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C]
  simpa only [RatFunc.coePolynomial, Polynomial.coe_C, PowerSeries.coe_C] using
    (RatFunc.coe_coe (Polynomial.C a)).symm

theorem rationalSeries_monomial (a : K) (j : ℤ) :
    rationalSeries (C a * T j) = HahnSeries.single j a := by
  rw [rationalSeries, map_mul, fieldRatify_C, fieldRatify_T, map_mul, map_zpow₀]
  have hC : algebraMap (RatFunc K) K⸨X⸩ (algebraMap K (RatFunc K) a) =
      HahnSeries.C a := by
    exact rational_coefficient_series a
  have hX : algebraMap (RatFunc K) K⸨X⸩ (variableRat : RatFunc K) =
      HahnSeries.single 1 1 := by
    simpa only [variableRat, RatFunc.algebraMap_X] using (RatFunc.coe_X (F := K))
  rw [hC, hX, ← RatFunc.single_zpow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

/-- Every original Laurent coefficient is unchanged by its rational-series inclusion. -/
theorem rationalSeries_coefficient (P : K[T;T⁻¹]) (j : ℤ) :
    (rationalSeries P).coeff j = P.coeff j := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    have hadd : rationalSeries (P + Q) = rationalSeries P + rationalSeries Q := by
      unfold rationalSeries
      rw [map_add, map_add]
    rw [hadd, HahnSeries.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | C_mul_T n a =>
    rw [rationalSeries_monomial]
    simp only [HahnSeries.coeff_single, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]
    by_cases hj : j = n <;> simp [hj, eq_comm]

/-- Differential inversion contributes its negative Jacobian, including the logarithmic slot. -/
theorem differential_inverse_residue (P : K[T;T⁻¹]) :
    (rationalSeries (-T (-2) * invert P)).coeff (-1) = -P.coeff (-1) := by
  rw [rationalSeries_coefficient]
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, mul_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ, neg_add]
  | C_mul_T n a =>
    simp only [map_mul, invert_C, invert_T]
    rw [show (-T (-2) : K[T;T⁻¹]) * (C a * T (-n)) =
      C (-a) * T (-n - 2) by
        rw [show -n - 2 = (-2 : ℤ) + -n by omega, T_add]
        simp only [map_neg]
        ring]
    simp only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hn : n = -1
    · subst n; norm_num
    · rw [if_neg (by omega), if_neg (by omega), neg_zero]

theorem signed_reciprocal_rational_source (P : K[T;T⁻¹]) :
    fieldRatify (-T (-2) * invert P) =
      -variableRat⁻¹ ^ 2 * reciprocalRatify P := by
  rw [map_mul, map_neg, fieldRatify_T, fieldRatify_invert]
  simp only [zpow_neg, zpow_ofNat, inv_pow]

theorem integralLift_unique (p : ℕ) [Fact p.Prime]
    (P : integralLaurent p) (L : (WPPIntegralReduction.integralRationals p)[T;T⁻¹])
    (hL : coefficientMap (WPPIntegralReduction.integralRationals p).subtype L = P.val) :
    integralLift p P = L := by
  apply WPLaurentIntegralResidue.coefficientMap_injective _
    (Subring.subtype_injective (WPPIntegralReduction.integralRationals p))
  rw [integralLift_rational, hL]

end WPFirstResidue.CentralResidue
