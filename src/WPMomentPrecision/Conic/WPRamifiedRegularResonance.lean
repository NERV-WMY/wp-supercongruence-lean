import WPActualGaussProper
import Mathlib.RingTheory.PowerSeries.Derivative

open scoped PowerSeries
open PowerSeries

namespace WPRamifiedRegularResonance

/-- The canonical first-digit primitive retains every coefficient, including its resonances. -/
noncomputable def digitPrimitive (p : ℕ) [Fact p.Prime] (g : (ZMod p)⟦X⟧) :
    (ZMod p)⟦X⟧ :=
  PowerSeries.mk (fun n => PowerSeries.coeff (n - 1) g / (n : ZMod p))

theorem digitPrimitive_derivative_low (p n : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hn : n < p - 1) (g : (ZMod p)⟦X⟧) :
    PowerSeries.coeff n (PowerSeries.derivative (ZMod p) (digitPrimitive p g)) =
      PowerSeries.coeff n g := by
  have hunit : ((n + 1 : ℕ) : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p (n + 1) (by omega) (by omega)
  rw [PowerSeries.coeff_derivative, digitPrimitive, PowerSeries.coeff_mk,
    Nat.add_sub_cancel, ← Nat.cast_add_one]
  field_simp

theorem digitPrimitive_remainder (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (g : (ZMod p)⟦X⟧) :
    (PowerSeries.X : (ZMod p)⟦X⟧) ^ (p - 1) ∣
      g - PowerSeries.derivative (ZMod p) (digitPrimitive p g) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro n hn
  rw [map_sub, digitPrimitive_derivative_low p n hp hn, sub_self]

theorem derivative_resonance_zero (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (f : (ZMod p)⟦X⟧) :
    PowerSeries.coeff (p - 1) (PowerSeries.derivative (ZMod p) f) = 0 := by
  rw [PowerSeries.coeff_derivative, ← Nat.cast_add_one, show p - 1 + 1 = p by omega]
  simp

/-- A regular source pulled through order at least two has no first Cartier resonance. -/
theorem ramified_regular_resonance_zero (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (g u : (ZMod p)⟦X⟧) :
    PowerSeries.coeff (p - 1)
      (g.subst (PowerSeries.X ^ 2 * u) *
        PowerSeries.derivative (ZMod p) (PowerSeries.X ^ 2 * u)) = 0 := by
  let s : (ZMod p)⟦X⟧ := PowerSeries.X ^ 2 * u
  have hs : PowerSeries.HasSubst s :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [s])
  obtain ⟨R, hR⟩ := digitPrimitive_remainder p hp g
  have htail : (g - PowerSeries.derivative (ZMod p) (digitPrimitive p g)).subst s *
      PowerSeries.derivative (ZMod p) s =
      PowerSeries.X ^ (2 * (p - 1)) *
        (u ^ (p - 1) * R.subst s * PowerSeries.derivative (ZMod p) s) := by
    rw [hR, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs]
    dsimp [s]
    rw [mul_pow, ← pow_mul]
    ring
  have hz : PowerSeries.coeff (p - 1)
      ((g - PowerSeries.derivative (ZMod p) (digitPrimitive p g)).subst s *
        PowerSeries.derivative (ZMod p) s) = 0 := by
    rw [htail, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hd := derivative_resonance_zero p hp ((digitPrimitive p g).subst s)
  rw [PowerSeries.derivative_subst hs] at hd
  rw [PowerSeries.subst_sub hs, sub_mul, map_sub] at hz
  change PowerSeries.coeff (p - 1) (g.subst s * PowerSeries.derivative (ZMod p) s) = 0
  linear_combination hz + hd

noncomputable def conicInfinitySeries (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ :=
  PowerSeries.X ^ 3 * (4 - 3 * PowerSeries.X ^ 2)⁻¹

/-- Exact IR19 local substitution s=v^3/(4-3v^2), with its complete regular source. -/
theorem actual_conic_resonance_zero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (g : (ZMod p)⟦X⟧) :
    PowerSeries.coeff (p - 1) (g.subst (conicInfinitySeries p) *
      PowerSeries.derivative (ZMod p) (conicInfinitySeries p)) = 0 := by
  have he : conicInfinitySeries p = PowerSeries.X ^ 2 *
      (PowerSeries.X * (4 - 3 * PowerSeries.X ^ 2)⁻¹) := by
    unfold conicInfinitySeries
    ring
  rw [he]
  exact ramified_regular_resonance_zero p (by omega) g _

end WPRamifiedRegularResonance
