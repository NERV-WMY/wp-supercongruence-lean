import WPMomentPrecision.Conic.WPActualConicInfinitySource
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

open scoped PowerSeries LaurentSeries
open PowerSeries WPActualConicInfinitySource WPRamifiedRegularResonance

namespace WPActualConicWeightedResidue

/-- The complete Frobenius weight contributes only its constant before degree p. -/
theorem frobenius_weight_resonance (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (u w : (ZMod p)⟦X⟧) (hw : PowerSeries.coeff (p - 1) w = 0) :
    PowerSeries.coeff (p - 1) (u ^ p * w) = 0 := by
  let : CharP (ZMod p)⟦X⟧ p := charP_of_injective_ringHom PowerSeries.C_injective p
  obtain ⟨R, hR⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (u - PowerSeries.C (PowerSeries.constantCoeff u)) = 0 by simp)
  have hu : u = PowerSeries.C (PowerSeries.constantCoeff u) + PowerSeries.X * R := by
    linear_combination hR
  have hc : (PowerSeries.C (PowerSeries.constantCoeff u) : (ZMod p)⟦X⟧) ^ p =
      PowerSeries.C (PowerSeries.constantCoeff u) := by
    rw [← map_pow, ZMod.pow_card]
  rw [hu, add_pow_char, mul_pow, hc, add_mul, map_add, PowerSeries.coeff_C_mul, hw,
    mul_zero, zero_add, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- Laurent shifting converts the first resonance into the actual coefficient of v^-1. -/
theorem shifted_frobenius_residue (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (u w : (ZMod p)⟦X⟧) (hw : PowerSeries.coeff (p - 1) w = 0) :
    (HahnSeries.single (-(p : ℤ)) (1 : ZMod p) *
      ((u ^ p * w : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)).coeff (-1) = 0 := by
  have hi : (-1 : ℤ) - (-(p : ℤ)) = ((p - 1 : ℕ) : ℤ) := by omega
  rw [HahnSeries.coeff_single_mul, one_mul, hi, PowerSeries.coeff_coe,
    if_neg (by omega), Int.natAbs_natCast]
  exact frobenius_weight_resonance p hp u w hw

/-- L(v^-1)=v^-1 times this exact unit series; no tail is discarded. -/
noncomputable def conicLUnit (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ :=
  (3 * PowerSeries.X ^ 2 - 11) * (5 - PowerSeries.X ^ 2)⁻¹

theorem conicLUnit_origin (p : ℕ) [Fact p.Prime] :
    PowerSeries.constantCoeff (conicLUnit p) = (-11 : ZMod p) / 5 := by
  have h11 : PowerSeries.constantCoeff (11 : (ZMod p)⟦X⟧) = (11 : ZMod p) :=
    map_natCast PowerSeries.constantCoeff 11
  have h5 : PowerSeries.constantCoeff (5 : (ZMod p)⟦X⟧) = (5 : ZMod p) :=
    map_natCast PowerSeries.constantCoeff 5
  simp [conicLUnit, div_eq_mul_inv, h11, h5]

noncomputable def actualConicWeightedDensity (p : ℕ) [Fact p.Prime] : (ZMod p)⸨X⸩ :=
  HahnSeries.single (-(p : ℤ)) (1 : ZMod p) *
    ((conicLUnit p ^ p * (PowerSeries.C (1 / 3) *
      ((rankInfinitySeries p).subst (conicInfinitySeries p) *
        PowerSeries.derivative (ZMod p) (conicInfinitySeries p))) : (ZMod p)⟦X⟧) :
      (ZMod p)⸨X⸩)

/-- Entire IR19 weighted local density has zero residue, for both prime classes. -/
theorem actual_conic_weighted_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualConicWeightedDensity p).coeff (-1) = 0 := by
  apply shifted_frobenius_residue p (by omega)
  rw [PowerSeries.coeff_C_mul, actual_rank_conic_resonance_zero p hp, mul_zero]

end WPActualConicWeightedResidue
