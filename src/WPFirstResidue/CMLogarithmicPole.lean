import WPMomentPrecision.Conic.WPRationalInfinitySeries
import Mathlib.Tactic

open scoped PowerSeries LaurentSeries

namespace WPFirstResidue.CMLogarithmicPole

variable {K : Type*} [Field K]

/-- The first two inverse coefficients retain the complete coordinate unit. -/
theorem inverse_first_coefficients (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.constantCoeff f⁻¹ = (PowerSeries.constantCoeff f)⁻¹ ∧
      PowerSeries.coeff 1 f⁻¹ = -PowerSeries.coeff 1 f /
        (PowerSeries.constantCoeff f) ^ 2 := by
  constructor
  · simp
  · have he := congrArg (PowerSeries.coeff 1) (PowerSeries.inv_mul_cancel f hf)
    rw [PowerSeries.coeff_one_mul, PowerSeries.constantCoeff_inv,
      PowerSeries.coeff_one, if_neg (by norm_num)] at he
    field_simp at he
    field_simp
    linear_combination he

/-- A simple CM pole contributes both its coordinate correction and its regular constant. -/
theorem complete_simple_pole_logarithmic_residue (f G D : K⟦X⟧) (A : K)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    ((HahnSeries.single (-1) A * ((f⁻¹ : K⟦X⟧) : K⸨X⸩) + (G : K⸨X⸩)) *
      (HahnSeries.single (-1) (-3 : K) + (D : K⸨X⸩))).coeff (-1) =
      A * (3 * PowerSeries.coeff 1 f / (PowerSeries.constantCoeff f) ^ 2 +
        PowerSeries.constantCoeff D / PowerSeries.constantCoeff f) -
      3 * PowerSeries.constantCoeff G := by
  have he :
      (HahnSeries.single (-1) A * ((f⁻¹ : K⟦X⟧) : K⸨X⸩) + (G : K⸨X⸩)) *
        (HahnSeries.single (-1) (-3 : K) + (D : K⸨X⸩)) =
      HahnSeries.single (-2) (A * (-3 : K)) * ((f⁻¹ : K⟦X⟧) : K⸨X⸩) +
        HahnSeries.single (-1) A * (((f⁻¹ * D : K⟦X⟧) : K⸨X⸩)) +
        HahnSeries.single (-1) (-3 : K) * (G : K⸨X⸩) +
        ((G * D : K⟦X⟧) : K⸨X⸩) := by
    have hs : (HahnSeries.single (-2) (A * (-3 : K)) : K⸨X⸩) =
        HahnSeries.single (-1) A * HahnSeries.single (-1) (-3 : K) := by
      rw [HahnSeries.single_mul_single]
      norm_num
    rw [PowerSeries.coe_mul, PowerSeries.coe_mul, hs]
    ring
  rw [he]
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_single_mul,
    show (-1 : ℤ) - -2 = 1 by norm_num, show (-1 : ℤ) - -1 = 0 by norm_num,
    PowerSeries.coeff_coe, show ¬ (1 : ℤ) < 0 by norm_num,
    show ¬ (0 : ℤ) < 0 by norm_num, show (-1 : ℤ) < 0 by norm_num,
    if_false, if_true, Int.natAbs_one, Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, add_zero]
  simp only [map_mul]
  rw [(inverse_first_coefficients f hf).1, (inverse_first_coefficients f hf).2]
  ring

/-- IR17's actual quadratic coordinate coefficients cancel the nonzero odd pole. -/
theorem native_coordinate_pole_cancellation (A beta : K)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0) :
    A * (3 * (45 / 32 : K) / (15 / 16 : K) ^ 2 +
      (-9 / 2 : K) / (15 / 16 : K)) - 3 * beta = -3 * beta := by
  have h16 : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1
    norm_num
  have h32 : (32 : K) ≠ 0 := by
    convert pow_ne_zero 5 h2 using 1
    norm_num
  have h15 : (15 : K) ≠ 0 := by
    convert mul_ne_zero h3 h5 using 1
    norm_num
  have h225 : (225 : K) ≠ 0 := by
    convert pow_ne_zero 2 h15 using 1
    norm_num
  field_simp [h2, h16, h32, h15, h225]
  ring

end WPFirstResidue.CMLogarithmicPole
