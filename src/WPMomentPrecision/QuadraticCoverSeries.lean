import WPMomentPrecision.QuadraticResidueTransport
import Mathlib.RingTheory.PowerSeries.Substitution

open scoped PowerSeries LaurentSeries
open WPRationalInfinitySeries WPMomentPrecision.QuadraticResidueTransport

namespace WPMomentPrecision.QuadraticCoverSeries

variable {K : Type*} [Field K]

noncomputable def coverSeries : K⟦X⟧ :=
  4 * PowerSeries.X ^ 2 * (coverUnit : K⟦X⟧)⁻¹ ^ 2

noncomputable def jacobianSeries : K⟦X⟧ :=
  8 * PowerSeries.X * (1 + PowerSeries.X ^ 2) * (coverUnit : K⟦X⟧)⁻¹ ^ 3

theorem coverSeries_cast : ((coverSeries : K⟦X⟧) : K⸨X⸩) = coverX localX := by
  simp only [coverSeries, PowerSeries.coe_mul, PowerSeries.coe_pow,
    powerSeries_inverse_cast (coverUnit : K⟦X⟧) (by rw [coverUnit_origin]; exact one_ne_zero),
    coverUnit_cast, map_ofNat, PowerSeries.coe_X, localX, coverX,
    div_eq_mul_inv, inv_pow]

theorem jacobianSeries_cast : ((jacobianSeries : K⟦X⟧) : K⸨X⸩) = coverJacobian localX := by
  simp only [jacobianSeries, PowerSeries.coe_mul, PowerSeries.coe_add, PowerSeries.coe_one,
    PowerSeries.coe_pow,
    powerSeries_inverse_cast (coverUnit : K⟦X⟧) (by rw [coverUnit_origin]; exact one_ne_zero),
    coverUnit_cast, map_ofNat, PowerSeries.coe_X, localX, coverJacobian,
    div_eq_mul_inv, inv_pow]

theorem coverSeries_origin : PowerSeries.constantCoeff (coverSeries : K⟦X⟧) = 0 := by
  simp [coverSeries]

theorem coverSeries_hasSubst : PowerSeries.HasSubst (coverSeries : K⟦X⟧) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' coverSeries_origin

/-- Every nonnegative monomial pulls back to the whole regular power series. -/
theorem nonnegative_cover_residue_zero (n : ℕ) :
    (coverX (localX : K⸨X⸩) ^ n * coverJacobian localX).coeff (-1) = 0 := by
  rw [← coverSeries_cast, ← jacobianSeries_cast, ← PowerSeries.coe_pow,
    ← PowerSeries.coe_mul, PowerSeries.coeff_coe, if_pos (by norm_num)]

theorem logarithmic_cover_residue (h4 : (4 : K) ≠ 0) :
    (coverX (localX : K⸨X⸩) ^ (-1 : ℤ) * coverJacobian localX).coeff (-1) = 2 := by
  have h4L : (4 : K⸨X⸩) ≠ 0 := by
    have hc : (HahnSeries.C (4 : K) : K⸨X⸩) = 4 := map_ofNat _ 4
    rw [← hc]
    exact HahnSeries.C_ne_zero h4
  rw [logarithmic_cover_normalform localX h4L localX_ne_zero coverUnit_ne_zero]
  have hlog : (2 / localX : K⸨X⸩) = HahnSeries.single (-1) (2 : K) := by
    have hc : (HahnSeries.C (2 : K) : K⸨X⸩) = 2 := map_ofNat _ 2
    rw [div_eq_mul_inv, ← hc, localX, HahnSeries.inv_single,
      HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have hreg : (4 * localX / (1 - localX ^ 2) : K⸨X⸩) =
      ((4 * PowerSeries.X * (coverUnit : K⟦X⟧)⁻¹ : K⟦X⟧) : K⸨X⸩) := by
    simp only [PowerSeries.coe_mul, powerSeries_inverse_cast (coverUnit : K⟦X⟧)
        (by rw [coverUnit_origin]; exact one_ne_zero), coverUnit_cast,
      map_ofNat, PowerSeries.coe_X, localX, div_eq_mul_inv]
  rw [hlog, hreg, HahnSeries.coeff_add, HahnSeries.coeff_single_same,
    PowerSeries.coeff_coe, if_pos (by norm_num), add_zero]

/-- Branchwise tame transport is literal for every integer monomial. -/
theorem monomial_cover_residue (h4 : (4 : K) ≠ 0) (j : ℤ) :
    (coverX (localX : K⸨X⸩) ^ j * coverJacobian localX).coeff (-1) =
      if j = -1 then 2 else 0 := by
  cases j with
  | ofNat n =>
    change (coverX (localX : K⸨X⸩) ^ (n : ℤ) * coverJacobian localX).coeff (-1) =
      if (n : ℤ) = -1 then 2 else 0
    rw [zpow_natCast, nonnegative_cover_residue_zero, if_neg (by omega)]
  | negSucc n =>
    cases n with
    | zero => exact logarithmic_cover_residue h4
    | succ k =>
      rw [show Int.negSucc (k + 1) = -(k : ℤ) - 2 by omega,
        negative_cover_residue_zero h4 k, if_neg (by omega)]

end WPMomentPrecision.QuadraticCoverSeries
