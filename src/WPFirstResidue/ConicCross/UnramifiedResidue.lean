import WPMomentPrecision.QuadraticLaurentPullback
import Mathlib.RingTheory.PowerSeries.Derivative

open scoped BigOperators Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPRationalInfinitySeries WPMomentPrecision.QuadraticResidueTransport
  WPMomentPrecision.QuadraticLaurentPullback

namespace WPFirstResidue.ConicCross

variable {K : Type*} [Field K]

def branchV (c z : K) : K := c * z / (1 + z ^ 2)
def branchVJacobian (c z : K) : K := c * (1 - z ^ 2) / (1 + z ^ 2) ^ 2

theorem branchV_negative_normalform (c z : K) (hc : c ≠ 0) (hz : z ≠ 0)
    (hu : 1 + z ^ 2 ≠ 0) (k : ℕ) :
    branchV c z ^ (-(k : ℤ) - 2) * branchVJacobian c z =
      (1 / c ^ (k + 1)) * (1 - z ^ 2) * (1 + z ^ 2) ^ k / z ^ (k + 2) := by
  rw [show -(k : ℤ) - 2 = -((k + 2 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]
  unfold branchV branchVJacobian
  rw [div_pow, inv_div, mul_pow]
  rw [show k + 2 = k + 1 + 1 by omega, pow_succ c,
    show (1 + z ^ 2) ^ (k + 1 + 1) = (1 + z ^ 2) ^ k * (1 + z ^ 2) ^ 2 by
      rw [← pow_add]]
  field_simp

theorem branchV_logarithmic_normalform (c z : K) (hc : c ≠ 0)
    (hz : z ≠ 0) (hu : 1 + z ^ 2 ≠ 0) :
    branchV c z ^ (-1 : ℤ) * branchVJacobian c z = 1 / z - 2 * z / (1 + z ^ 2) := by
  simp only [zpow_neg_one, branchV, branchVJacobian]
  field_simp
  ring

theorem binomial_middle_zero (m : ℕ) :
    ((1 - X : K[X]) * (1 + X) ^ (2 * m + 1)).coeff (m + 1) = 0 := by
  have hc : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one_add_X_pow, hc]
  ring

/-- The negative monomial cancellation is exact at every characteristic-p resonance. -/
theorem unramified_middle_zero (k : ℕ) :
    ((1 - X ^ 2 : K[X]) * (1 + X ^ 2) ^ k).coeff (k + 1) = 0 := by
  have he : (1 - X ^ 2 : K[X]) * (1 + X ^ 2) ^ k =
      Polynomial.expand K 2 ((1 - X) * (1 + X) ^ k) := by
    rw [Polynomial.expand_eq_comp_X_pow]
    simp only [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.add_comp,
      Polynomial.one_comp, Polynomial.X_comp, Polynomial.pow_comp]
  rw [he]
  have hk : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rcases hk with hk | hk
  · rw [hk, Polynomial.coeff_expand (by norm_num : 0 < 2), if_neg (by
      rintro ⟨n, hn⟩
      omega)]
  · rw [hk, show 2 * (k / 2) + 1 + 1 = 2 * (k / 2 + 1) by omega,
      Polynomial.coeff_expand_mul' (by norm_num : 0 < 2), binomial_middle_zero]

noncomputable def branchUnit : K⟦X⟧ := 1 + PowerSeries.X ^ 2
noncomputable def branchSeries (c : K) : K⟦X⟧ :=
  PowerSeries.C c * PowerSeries.X * (branchUnit : K⟦X⟧)⁻¹
noncomputable def branchJacobianSeries (c : K) : K⟦X⟧ :=
  PowerSeries.C c * (1 - PowerSeries.X ^ 2) * (branchUnit : K⟦X⟧)⁻¹ ^ 2

theorem branchUnit_origin : PowerSeries.constantCoeff (branchUnit : K⟦X⟧) = 1 := by
  simp [branchUnit]

theorem branchUnit_cast : ((branchUnit : K⟦X⟧) : K⸨X⸩) = 1 + localX ^ 2 := by
  simp [branchUnit, localX, PowerSeries.coe_pow]

theorem branchUnit_ne_zero : (1 + (localX : K⸨X⸩) ^ 2) ≠ 0 := by
  rw [← branchUnit_cast]
  intro hz
  have hc := congrArg (fun f : K⸨X⸩ => f.coeff 0) hz
  simp [PowerSeries.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    branchUnit_origin] at hc

theorem branchSeries_cast (c : K) : ((branchSeries c : K⟦X⟧) : K⸨X⸩) =
    branchV (HahnSeries.C c) localX := by
  simp only [branchSeries, PowerSeries.coe_mul, PowerSeries.coe_C, PowerSeries.coe_X,
    powerSeries_inverse_cast (branchUnit : K⟦X⟧) (by rw [branchUnit_origin]; exact one_ne_zero),
    branchUnit_cast, localX, branchV, div_eq_mul_inv]

theorem branchJacobianSeries_cast (c : K) :
    ((branchJacobianSeries c : K⟦X⟧) : K⸨X⸩) = branchVJacobian (HahnSeries.C c) localX := by
  simp only [branchJacobianSeries, PowerSeries.coe_mul, PowerSeries.coe_C, PowerSeries.coe_sub,
    PowerSeries.coe_pow, PowerSeries.coe_one, PowerSeries.coe_X,
    powerSeries_inverse_cast (branchUnit : K⟦X⟧) (by rw [branchUnit_origin]; exact one_ne_zero),
    branchUnit_cast, localX, branchVJacobian, div_eq_mul_inv, inv_pow]

theorem branchSeries_origin (c : K) : PowerSeries.constantCoeff (branchSeries c) = 0 := by
  simp [branchSeries]

theorem branchSeries_hasSubst (c : K) : PowerSeries.HasSubst (branchSeries c) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (branchSeries_origin c)

theorem branchSeries_derivative (c : K) :
    PowerSeries.derivative K (branchSeries c) = branchJacobianSeries c := by
  have hi := PowerSeries.inv_mul_cancel (branchUnit : K⟦X⟧)
    (by rw [branchUnit_origin]; exact one_ne_zero)
  dsimp only [branchUnit] at hi
  simp [branchSeries, branchJacobianSeries, branchUnit]
  linear_combination -PowerSeries.C c * (1 + PowerSeries.X ^ 2)⁻¹ * hi

theorem branchV_ne_zero (c : K) (hc : c ≠ 0) :
    branchV (HahnSeries.C c) (localX : K⸨X⸩) ≠ 0 :=
  div_ne_zero (mul_ne_zero (HahnSeries.C_ne_zero hc) localX_ne_zero) branchUnit_ne_zero

noncomputable def branchSeriesSubstitution (c : K) : K⟦X⟧ →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (PowerSeries.substAlgHom (branchSeries_hasSubst c)).toRingHom

theorem branchSeriesSubstitution_X (c : K) :
    branchSeriesSubstitution c (PowerSeries.X : K⟦X⟧) = branchV (HahnSeries.C c) localX := by
  change ((PowerSeries.substAlgHom (branchSeries_hasSubst c)
    (PowerSeries.X : K⟦X⟧) : K⟦X⟧) : K⸨X⸩) = _
  rw [PowerSeries.substAlgHom_X, branchSeries_cast]

theorem branchSeriesSubstitution_units (c : K) (hc : c ≠ 0)
    (y : Submonoid.powers (PowerSeries.X : K⟦X⟧)) :
    IsUnit (branchSeriesSubstitution c (y : K⟦X⟧)) := by
  rcases y with ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := hy
  rw [map_pow]
  apply IsUnit.pow
  rw [branchSeriesSubstitution_X]
  exact isUnit_iff_ne_zero.mpr (branchV_ne_zero c hc)

noncomputable def branchSubstitution (c : K) (hc : c ≠ 0) : K⸨X⸩ →+* K⸨X⸩ :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : K⟦X⟧))
    (S := K⸨X⸩) (branchSeriesSubstitution_units c hc)

theorem branchSubstitution_powerSeries (c : K) (hc : c ≠ 0) (f : K⟦X⟧) :
    branchSubstitution c hc (f : K⸨X⸩) = ((f.subst (branchSeries c) : K⟦X⟧) : K⸨X⸩) := by
  have he : branchSeriesSubstitution c f =
      ((f.subst (branchSeries c) : K⟦X⟧) : K⸨X⸩) := by
    change ((PowerSeries.substAlgHom (branchSeries_hasSubst c) f : K⟦X⟧) : K⸨X⸩) = _
    rw [PowerSeries.coe_substAlgHom]
  exact (IsLocalization.lift_eq (S := K⸨X⸩) (branchSeriesSubstitution_units c hc) f).trans he

theorem branchSubstitution_localX (c : K) (hc : c ≠ 0) :
    branchSubstitution c hc (localX : K⸨X⸩) = branchV (HahnSeries.C c) localX := by
  rw [show (localX : K⸨X⸩) = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) from
    PowerSeries.coe_X.symm, branchSubstitution_powerSeries,
    PowerSeries.subst_X (branchSeries_hasSubst c), branchSeries_cast]
  rw [PowerSeries.coe_X]
  rfl

theorem branchSubstitution_constant (c : K) (hc : c ≠ 0) (a : K) :
    branchSubstitution c hc (HahnSeries.C a) = HahnSeries.C a := by
  rw [← PowerSeries.coe_C, branchSubstitution_powerSeries, PowerSeries.subst_C]
  congr 1

theorem branchSubstitution_single (c : K) (hc : c ≠ 0) (j : ℤ) (a : K) :
    branchSubstitution c hc (HahnSeries.single j a) =
      HahnSeries.C a * branchV (HahnSeries.C c) localX ^ j := by
  have he : (HahnSeries.single j a : K⸨X⸩) = HahnSeries.C a * localX ^ j := by
    rw [localX, ← RatFunc.single_zpow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  rw [he, map_mul, branchSubstitution_constant, map_zpow₀, branchSubstitution_localX]

theorem branch_nonnegative_residue_zero (c : K) (n : ℕ) :
    (branchV (HahnSeries.C c) (localX : K⸨X⸩) ^ n *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) = 0 := by
  rw [← branchSeries_cast, ← branchJacobianSeries_cast, ← PowerSeries.coe_pow,
    ← PowerSeries.coe_mul, PowerSeries.coeff_coe, if_pos (by norm_num)]

theorem branch_logarithmic_residue (c : K) (hc : c ≠ 0) :
    (branchV (HahnSeries.C c) (localX : K⸨X⸩) ^ (-1 : ℤ) *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) = 1 := by
  rw [branchV_logarithmic_normalform _ _ (HahnSeries.C_ne_zero hc)
    localX_ne_zero branchUnit_ne_zero]
  have hlog : (1 / localX : K⸨X⸩) = HahnSeries.single (-1) (1 : K) := by
    rw [one_div, localX, HahnSeries.inv_single, inv_one]
  have hreg : (2 * localX / (1 + localX ^ 2) : K⸨X⸩) =
      ((2 * PowerSeries.X * (branchUnit : K⟦X⟧)⁻¹ : K⟦X⟧) : K⸨X⸩) := by
    simp only [PowerSeries.coe_mul, powerSeries_inverse_cast (branchUnit : K⟦X⟧)
      (by rw [branchUnit_origin]; exact one_ne_zero), branchUnit_cast, map_ofNat,
      PowerSeries.coe_X, localX, div_eq_mul_inv]
  rw [hlog, hreg, HahnSeries.coeff_sub, HahnSeries.coeff_single_same,
    PowerSeries.coeff_coe, if_pos (by norm_num), sub_zero]

theorem branch_negative_residue_zero (c : K) (hc : c ≠ 0) (k : ℕ) :
    (branchV (HahnSeries.C c) (localX : K⸨X⸩) ^ (-(k : ℤ) - 2) *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) = 0 := by
  rw [branchV_negative_normalform _ _ (HahnSeries.C_ne_zero hc)
    localX_ne_zero branchUnit_ne_zero k]
  let P : K[X] := (1 - Polynomial.X ^ 2) * (1 + Polynomial.X ^ 2) ^ k
  have hP : ((P : K⟦X⟧) : K⸨X⸩) = (1 - localX ^ 2) * (1 + localX ^ 2) ^ k := by
    simp [P, localX, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_sub,
      Polynomial.coe_pow, PowerSeries.coe_pow]
  have hs : (localX : K⸨X⸩) ^ (k + 2) = HahnSeries.single ((k + 2 : ℕ) : ℤ) 1 := by
    simp [localX]
  have he : (1 / (HahnSeries.C c) ^ (k + 1) : K⸨X⸩) * (1 - localX ^ 2) *
      (1 + localX ^ 2) ^ k / localX ^ (k + 2) =
      HahnSeries.single (-((k + 2 : ℕ) : ℤ)) (1 / c ^ (k + 1)) *
        ((P : K⟦X⟧) : K⸨X⸩) := by
    rw [mul_assoc, ← hP]
    calc
      _ = ((1 / (HahnSeries.C c) ^ (k + 1) : K⸨X⸩) * (localX ^ (k + 2))⁻¹) *
          ((P : K⟦X⟧) : K⸨X⸩) := by ring
      _ = _ := by
        have hC : (1 / (HahnSeries.C c) ^ (k + 1) : K⸨X⸩) =
            HahnSeries.C (1 / c ^ (k + 1)) := by simp only [map_div₀, map_one, map_pow]
        rw [hs, HahnSeries.inv_single, hC, HahnSeries.C_apply, HahnSeries.single_mul_single]
        simp
  rw [he, HahnSeries.coeff_single_mul]
  have hi : (-1 : ℤ) - (-((k + 2 : ℕ) : ℤ)) = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hi, PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_natCast,
    Polynomial.coeff_coe]
  rw [show P = (1 - Polynomial.X ^ 2) * (1 + Polynomial.X ^ 2) ^ k from rfl,
    unramified_middle_zero, mul_zero]

theorem branch_monomial_residue (c : K) (hc : c ≠ 0) (j : ℤ) :
    (branchV (HahnSeries.C c) (localX : K⸨X⸩) ^ j *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) = if j = -1 then 1 else 0 := by
  cases j with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, branch_nonnegative_residue_zero,
      if_neg (by omega)]
  | negSucc n =>
    cases n with
    | zero => exact branch_logarithmic_residue c hc
    | succ k =>
      rw [show Int.negSucc (k + 1) = -(k : ℤ) - 2 by omega,
        branch_negative_residue_zero c hc k, if_neg (by omega)]

theorem branch_single_residue (c : K) (hc : c ≠ 0) (j : ℤ) (a : K) :
    (branchSubstitution c hc (HahnSeries.single j a) *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) =
      (HahnSeries.single j a : K⸨X⸩).coeff (-1) := by
  rw [branchSubstitution_single, mul_assoc, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, branch_monomial_residue c hc]
  by_cases hj : j = -1
  · subst j; simp
  · simp [hj, HahnSeries.coeff_single_of_ne (Ne.symm hj)]

theorem branch_regular_residue_zero (c : K) (hc : c ≠ 0) (f : K⟦X⟧) :
    (branchSubstitution c hc (f : K⸨X⸩) *
      branchVJacobian (HahnSeries.C c) localX).coeff (-1) = 0 := by
  rw [branchSubstitution_powerSeries, ← branchJacobianSeries_cast,
    ← PowerSeries.coe_mul, PowerSeries.coeff_coe, if_pos (by norm_num)]

/-- Complete degree-one residue transport on either chosen infinity branch, with no branch sum. -/
theorem complete_unramified_residue_transport (c : K) (hc : c ≠ 0) (f : K⸨X⸩) :
    (branchSubstitution c hc f * branchVJacobian (HahnSeries.C c) localX).coeff (-1) =
      f.coeff (-1) := by
  classical
  have hdecomp := series_decomposition f
  have hr : (principalPart f).coeff (-1) = f.coeff (-1) := by
    have he := congrArg (fun g : K⸨X⸩ => g.coeff (-1)) hdecomp
    rw [HahnSeries.coeff_add, PowerSeries.coeff_coe, if_pos (by norm_num), add_zero] at he
    exact he.symm
  conv_lhs => rw [hdecomp]
  rw [map_add, add_mul, HahnSeries.coeff_add, branch_regular_residue_zero, add_zero]
  rw [principalPart, map_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  simp only [branch_single_residue c hc]
  simpa only [principalPart, HahnSeries.coeff_sum] using hr

end WPFirstResidue.ConicCross
