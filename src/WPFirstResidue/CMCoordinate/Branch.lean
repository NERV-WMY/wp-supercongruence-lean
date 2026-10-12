import WPActualCubicGauge
import WPFirstResidue.CMCoordinate.SeriesAlgebra
import WPMomentPrecision.ConicCoordinates
import Mathlib.Tactic

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial WPActualCubicGauge WPFirstResidue.CMCoordinate

namespace WPFirstResidue.NativeCMCoordinate

variable {K : Type*} [Field K]

noncomputable def centeredNumerator : K[X] :=
  (cubicA : K[X]).comp (C (1 / 2) + X)

noncomputable def centeredDenominator : K[X] :=
  (cubicH : K[X]).comp (C (1 / 2) + X) ^ 3

theorem centeredNumerator_exact (h2 : (2 : K) ≠ 0) :
    (centeredNumerator : K[X]) = 4 - 16 * X + 64 * X ^ 3 - 64 * X ^ 4 := by
  have hhalf : 1 - (1 / 2 : K) = 1 / 2 := by field_simp; ring
  have h0 : (64 : K) * (1 / 2) ^ 4 = 4 := by field_simp; ring
  have h1 : (128 : K) * (1 / 2) ^ 3 = 16 := by field_simp; ring
  have h3 : (128 : K) * (1 / 2) = 64 := by field_simp; ring
  calc
    centeredNumerator = 64 * (C (1 / 2) + X) * (C (1 / 2) - X) ^ 3 := by
      unfold centeredNumerator cubicA
      simp only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, ofNat_comp]
      congr 2
      rw [show (1 : K[X]) - (C (1 / 2) + X) = C (1 - (1 / 2 : K)) - X by
        simp only [map_sub, map_one]
        ring]
      rw [hhalf]
    _ = C ((64 : K) * (1 / 2) ^ 4) -
        C ((128 : K) * (1 / 2) ^ 3) * X +
        C ((128 : K) * (1 / 2)) * X ^ 3 - 64 * X ^ 4 := by
      simp only [map_mul, map_pow, C_ofNat]
      ring
    _ = _ := by rw [h0, h1, h3]; simp only [C_ofNat]

theorem centeredDenominator_exact (h2 : (2 : K) ≠ 0) :
    (centeredDenominator : K[X]) = (5 + 8 * X) ^ 3 := by
  have h : (1 : K) + 8 * (1 / 2) = 5 := by field_simp; ring
  calc
    centeredDenominator = (C ((1 : K) + 8 * (1 / 2)) + 8 * X) ^ 3 := by
      unfold centeredDenominator cubicH
      simp only [add_comp, mul_comp, X_comp, one_comp, ofNat_comp,
        map_add, map_mul, map_one, C_ofNat]
      ring
    _ = _ := by rw [h]; simp only [C_ofNat]

/-- Both factors are coerced before inversion; the inverse is in K[[X]]. -/
noncomputable def centeredCubicSeries : K⟦X⟧ :=
  ((centeredNumerator : K[X]) : K⟦X⟧) *
    (((centeredDenominator : K[X]) : K⟦X⟧)⁻¹)

theorem centeredDenominator_origin (h2 : (2 : K) ≠ 0) :
    PowerSeries.constantCoeff ((centeredDenominator : K[X]) : K⟦X⟧) = 125 := by
  rw [centeredDenominator_exact h2]
  norm_num

theorem centeredCubicSeries_cleared (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) :
    centeredCubicSeries * ((centeredDenominator : K[X]) : K⟦X⟧) =
      ((centeredNumerator : K[X]) : K⟦X⟧) := by
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1
    norm_num
  rw [centeredCubicSeries, mul_assoc, PowerSeries.inv_mul_cancel _
    (by rw [centeredDenominator_origin h2]; exact h125), mul_one]

theorem centeredCubicSeries_origin (h2 : (2 : K) ≠ 0) :
    PowerSeries.constantCoeff (centeredCubicSeries : K⟦X⟧) = 4 / 125 := by
  rw [centeredCubicSeries, map_mul, PowerSeries.constantCoeff_inv,
    centeredDenominator_origin h2, centeredNumerator_exact h2]
  simp [div_eq_mul_inv]

theorem centeredDenominator_first_two (h2 : (2 : K) ≠ 0) :
    PowerSeries.coeff 1 ((centeredDenominator : K[X]) : K⟦X⟧) = 600 ∧
      PowerSeries.coeff 2 ((centeredDenominator : K[X]) : K⟦X⟧) = 960 := by
  rw [centeredDenominator_exact h2]
  have h : (5 + 8 * X : K[X]) ^ 3 =
      125 + 600 * X + 960 * X ^ 2 + 512 * X ^ 3 := by ring
  rw [h]
  rw [Polynomial.coeff_coe, Polynomial.coeff_coe]
  norm_num [Polynomial.coeff_X]

theorem centeredCubicSeries_linear (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) :
    PowerSeries.coeff 1 (centeredCubicSeries : K⟦X⟧) = -176 / 625 := by
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1
    norm_num
  have h625 : (625 : K) ≠ 0 := by
    convert pow_ne_zero 4 h5 using 1
    norm_num
  have he := congrArg (PowerSeries.coeff 1) (centeredCubicSeries_cleared h2 h5)
  rw [PowerSeries.coeff_one_mul, centeredDenominator_origin h2,
    (centeredDenominator_first_two h2).1, centeredCubicSeries_origin h2,
    centeredNumerator_exact h2] at he
  rw [Polynomial.coeff_coe] at he
  simp at he
  have hs : PowerSeries.coeff 1 (centeredCubicSeries : K⟦X⟧) =
      (-16 - 600 * (4 / 125 : K)) / 125 := by
    apply (eq_div_iff h125).mpr
    linear_combination he
  rw [hs]
  field_simp [h125, h625]
  ring

theorem centeredCubicSeries_quadratic (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) :
    PowerSeries.coeff 2 (centeredCubicSeries : K⟦X⟧) = 3456 / 3125 := by
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1
    norm_num
  have h625 : (625 : K) ≠ 0 := by
    convert pow_ne_zero 4 h5 using 1
    norm_num
  have h3125 : (3125 : K) ≠ 0 := by
    convert pow_ne_zero 5 h5 using 1
    norm_num
  have he := congrArg (PowerSeries.coeff 2) (centeredCubicSeries_cleared h2 h5)
  rw [coeff_two_mul, centeredDenominator_origin h2,
    (centeredDenominator_first_two h2).1, (centeredDenominator_first_two h2).2,
    centeredCubicSeries_origin h2, centeredCubicSeries_linear h2 h5,
    centeredNumerator_exact h2] at he
  rw [Polynomial.coeff_coe] at he
  norm_num [Polynomial.coeff_X] at he
  have hs : PowerSeries.coeff 2 (centeredCubicSeries : K⟦X⟧) =
      (-(4 / 125 : K) * 960 - (-176 / 625 : K) * 600) / 125 := by
    apply (eq_div_iff h125).mpr
    linear_combination he
  rw [hs]
  field_simp [h125, h625, h3125]
  ring

/-- The actual V polynomial in the original x-coordinate. -/
noncomputable def nativeVSeries : K⟦X⟧ :=
  PowerSeries.C (1 / 125 : K) * (4 * PowerSeries.X - 1) ^ 2 * (4 - PowerSeries.X)

theorem nativeVSeries_exact : (nativeVSeries : K⟦X⟧) =
    PowerSeries.C (4 / 125 : K) + PowerSeries.C (-33 / 125 : K) * PowerSeries.X +
      PowerSeries.C (72 / 125 : K) * PowerSeries.X ^ 2 +
      PowerSeries.C (-16 / 125 : K) * PowerSeries.X ^ 3 := by
  unfold nativeVSeries
  simp only [div_eq_mul_inv, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem nativeVSeries_coefficients :
    PowerSeries.constantCoeff (nativeVSeries : K⟦X⟧) = 4 / 125 ∧
      PowerSeries.coeff 1 (nativeVSeries : K⟦X⟧) = -33 / 125 ∧
      PowerSeries.coeff 2 (nativeVSeries : K⟦X⟧) = 72 / 125 := by
  rw [nativeVSeries_exact]
  simp

noncomputable def cubicDisplacement : K⟦X⟧ :=
  centeredCubicSeries - PowerSeries.C (4 / 125 : K)

noncomputable def nativeVDisplacement : K⟦X⟧ :=
  nativeVSeries - PowerSeries.C (4 / 125 : K)

theorem cubicDisplacement_origin (h2 : (2 : K) ≠ 0) :
    PowerSeries.constantCoeff (cubicDisplacement : K⟦X⟧) = 0 := by
  simp [cubicDisplacement, centeredCubicSeries_origin h2]

theorem nativeVDisplacement_origin :
    PowerSeries.constantCoeff (nativeVDisplacement : K⟦X⟧) = 0 := by
  simp [nativeVDisplacement, nativeVSeries_coefficients.1]

theorem cubicDisplacement_linear_unit (h2 : (2 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0) :
    IsUnit (PowerSeries.coeff 1 (cubicDisplacement : K⟦X⟧)) := by
  have h176 : (176 : K) ≠ 0 := by
    rw [show (176 : K) = 2 ^ 4 * 11 by ring]
    exact mul_ne_zero (pow_ne_zero 4 h2) h11
  have h625 : (625 : K) ≠ 0 := by
    convert pow_ne_zero 4 h5 using 1
    norm_num
  rw [cubicDisplacement, map_sub]
  simp only [PowerSeries.coeff_C, show (1 : ℕ) ≠ 0 by decide, if_false, sub_zero]
  rw [centeredCubicSeries_linear h2 h5]
  exact isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr h176) h625)

/-- The CM branch is constructed by the compositional inverse of the actual
centered cubic quotient, then composed with the actual native V displacement. -/
noncomputable def nativeDelta (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) : K⟦X⟧ :=
  (cubicDisplacement.substInvOfIsUnit (cubicDisplacement_linear_unit h2 h5 h11)).subst
    nativeVDisplacement

theorem nativeDelta_origin (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    PowerSeries.constantCoeff (nativeDelta h2 h5 h11) = 0 := by
  unfold nativeDelta
  exact PowerSeries.constantCoeff_subst_eq_zero nativeVDisplacement_origin _
    (PowerSeries.constantCoeff_substInvOfIsUnit _ _)

theorem nativeDelta_hasSubst (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) : PowerSeries.HasSubst (nativeDelta h2 h5 h11) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (nativeDelta_origin h2 h5 h11)

theorem nativeDelta_displacement_identity (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    (cubicDisplacement : K⟦X⟧).subst (nativeDelta h2 h5 h11) =
      (nativeVDisplacement : K⟦X⟧) := by
  have hv := PowerSeries.HasSubst.of_constantCoeff_zero'
    (nativeVDisplacement_origin (K := K))
  have he := congrArg (PowerSeries.subst (R := K) (nativeVDisplacement : K⟦X⟧))
    (PowerSeries.subst_substInvOfIsUnit_right (cubicDisplacement : K⟦X⟧)
      (cubicDisplacement_origin h2) (cubicDisplacement_linear_unit h2 h5 h11))
  rw [PowerSeries.subst_comp_subst_apply (R := K)
    (PowerSeries.HasSubst.substInvOfIsUnit _ _) hv,
    PowerSeries.subst_X (R := K) hv] at he
  exact he

theorem nativeDelta_cubic_identity (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    (centeredCubicSeries : K⟦X⟧).subst (nativeDelta h2 h5 h11) =
      (nativeVSeries : K⟦X⟧) := by
  have he := nativeDelta_displacement_identity h2 h5 h11
  have hc : (PowerSeries.C (4 / 125 : K)).subst (nativeDelta h2 h5 h11) =
      PowerSeries.C (4 / 125 : K) := by
    exact PowerSeries.subst_C (S := K) (a := nativeDelta h2 h5 h11) (4 / 125 : K)
  rw [cubicDisplacement, PowerSeries.subst_sub (R := K) (nativeDelta_hasSubst h2 h5 h11),
    hc, nativeVDisplacement] at he
  linear_combination he

/-- This exact cleared equation fixes all coefficients of the actual CM branch. -/
theorem nativeDelta_cleared (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    (nativeVSeries : K⟦X⟧) *
        (PowerSeries.C (5 : K) + PowerSeries.C (8 : K) * nativeDelta h2 h5 h11) ^ 3 =
      PowerSeries.C (4 : K) - PowerSeries.C (16 : K) * nativeDelta h2 h5 h11 +
        PowerSeries.C (64 : K) * (nativeDelta h2 h5 h11) ^ 3 -
        PowerSeries.C (64 : K) * (nativeDelta h2 h5 h11) ^ 4 := by
  let S := PowerSeries.substAlgHom (R := K) (nativeDelta_hasSubst h2 h5 h11)
  have hS (f : K⟦X⟧) : S.toRingHom f = f.subst (nativeDelta h2 h5 h11) :=
    congrFun (PowerSeries.coe_substAlgHom (nativeDelta_hasSubst h2 h5 h11)) f
  have hSC (a : K) : S.toRingHom (PowerSeries.C a) = PowerSeries.C a := by
    rw [hS]
    exact PowerSeries.subst_C (S := K) (a := nativeDelta h2 h5 h11) a
  have hSX : S.toRingHom (PowerSeries.X : K⟦X⟧) = nativeDelta h2 h5 h11 := by
    rw [hS]
    exact PowerSeries.subst_X (R := K) (nativeDelta_hasSubst h2 h5 h11)
  have hD : ((centeredDenominator : K[X]) : K⟦X⟧) =
      (PowerSeries.C (5 : K) + PowerSeries.C (8 : K) * PowerSeries.X) ^ 3 := by
    rw [centeredDenominator_exact h2]
    simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_X, ← Polynomial.C_ofNat, Polynomial.coe_C]
  have hN : ((centeredNumerator : K[X]) : K⟦X⟧) =
      PowerSeries.C (4 : K) - PowerSeries.C (16 : K) * PowerSeries.X +
        PowerSeries.C (64 : K) * PowerSeries.X ^ 3 -
        PowerSeries.C (64 : K) * PowerSeries.X ^ 4 := by
    rw [centeredNumerator_exact h2]
    simp only [Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X, ← Polynomial.C_ofNat, Polynomial.coe_C]
  have he := congrArg S.toRingHom (centeredCubicSeries_cleared h2 h5)
  rw [map_mul, hD, hN] at he
  have hc : S.toRingHom (centeredCubicSeries : K⟦X⟧) = (nativeVSeries : K⟦X⟧) := by
    rw [hS]
    exact nativeDelta_cubic_identity h2 h5 h11
  rw [hc] at he
  simpa only [map_pow, map_add, map_mul, map_sub, hSC, hSX] using he

theorem nativeDelta_coefficients (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (h11 : (11 : K) ≠ 0) :
    PowerSeries.coeff 1 (nativeDelta h2 h5 h11) = 15 / 16 ∧
      PowerSeries.coeff 2 (nativeDelta h2 h5 h11) = 45 / 32 := by
  let d := nativeDelta h2 h5 h11
  have hd0 : PowerSeries.constantCoeff d = 0 := nativeDelta_origin h2 h5 h11
  have h176 : (176 : K) ≠ 0 := by
    rw [show (176 : K) = 2 ^ 4 * 11 by ring]
    exact mul_ne_zero (pow_ne_zero 4 h2) h11
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1
    norm_num
  have h16 : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1
    norm_num
  have h32 : (32 : K) ≠ 0 := by
    convert pow_ne_zero 5 h2 using 1
    norm_num
  have h256 : (256 : K) ≠ 0 := by
    convert pow_ne_zero 8 h2 using 1
    norm_num
  have ht : (16 + 600 * (4 / 125 : K)) = 176 / 5 := by
    field_simp [h125, h5]
    ring
  have ht0 : (16 + 600 * (4 / 125 : K)) ≠ 0 := by
    rw [ht]; exact div_ne_zero h176 h5
  have he1 := congrArg (PowerSeries.coeff 1) (nativeDelta_cleared h2 h5 h11)
  change PowerSeries.coeff 1
    ((nativeVSeries : K⟦X⟧) * (PowerSeries.C 5 + PowerSeries.C 8 * d) ^ 3) =
      PowerSeries.coeff 1
        (PowerSeries.C 4 - PowerSeries.C 16 * d + PowerSeries.C 64 * d ^ 3 -
          PowerSeries.C 64 * d ^ 4) at he1
  simp [PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow, hd0,
    nativeVSeries_coefficients.1, nativeVSeries_coefficients.2.1] at he1
  have hs1 : PowerSeries.coeff 1 d =
      -(125 * (-33 / 125 : K)) / (16 + 600 * (4 / 125 : K)) := by
    apply (eq_div_iff ht0).mpr
    linear_combination he1
  have hd1 : PowerSeries.coeff 1 d = 15 / 16 := by
    rw [hs1, ht]
    field_simp [h125, h16, h176, h5]
    ring
  have he2 := congrArg (PowerSeries.coeff 2) (nativeDelta_cleared h2 h5 h11)
  change PowerSeries.coeff 2
    ((nativeVSeries : K⟦X⟧) * (PowerSeries.C 5 + PowerSeries.C 8 * d) ^ 3) =
      PowerSeries.coeff 2
        (PowerSeries.C 4 - PowerSeries.C 16 * d + PowerSeries.C 64 * d ^ 3 -
          PowerSeries.C 64 * d ^ 4) at he2
  simp [coeff_two_mul, coeff_two_cube, coeff_two_fourth_of_origin_zero d hd0,
    PowerSeries.coeff_one_pow, hd0,
    nativeVSeries_coefficients.1, nativeVSeries_coefficients.2.1,
    nativeVSeries_coefficients.2.2] at he2
  have hs2 : PowerSeries.coeff 2 d =
      -(125 * (72 / 125 : K) + 600 * PowerSeries.coeff 1 d * (-33 / 125 : K) +
        960 * PowerSeries.coeff 1 d ^ 2 * (4 / 125 : K)) /
        (16 + 600 * (4 / 125 : K)) := by
    apply (eq_div_iff ht0).mpr
    linear_combination he2
  have hd2 : PowerSeries.coeff 2 d = 45 / 32 := by
    rw [hs2, hd1, ht]
    field_simp [h125, h16, h32, h256, h176, h5]
    ring
  exact ⟨hd1, hd2⟩

theorem nativeDelta_linear_unit (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (h11 : (11 : K) ≠ 0) :
    IsUnit (PowerSeries.coeff 1 (nativeDelta h2 h5 h11)) := by
  rw [(nativeDelta_coefficients h2 h5 h11).1]
  apply isUnit_iff_ne_zero.mpr
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]; exact mul_ne_zero h3 h5
  have h16 : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1
    norm_num
  exact div_ne_zero h15 h16

end WPFirstResidue.NativeCMCoordinate
