import Mathlib.RingTheory.LaurentSeries

open scoped LaurentSeries
open HahnSeries

namespace WPForcedSourceStokes

noncomputable section

variable {K : Type*} [Field K]

noncomputable def geometricPowerSeries (q : K) : PowerSeries K :=
  PowerSeries.mk (fun n => q^n)

@[simp] theorem geometric_power_series_coeff (q : K) (n : ℕ) :
    PowerSeries.coeff n (geometricPowerSeries q) = q^n := by
  simp [geometricPowerSeries]

theorem geometric_power_series_identity (q : K) :
    (1-PowerSeries.C q*PowerSeries.X)*geometricPowerSeries q = 1 := by
  have hX (n : ℕ) : PowerSeries.coeff n
      (PowerSeries.X*geometricPowerSeries q) = if 1≤n then q^(n-1) else 0 := by
    simpa only [pow_one, geometric_power_series_coeff] using
      PowerSeries.coeff_X_pow_mul' (geometricPowerSeries q) 1 n
  rw [sub_mul, one_mul, mul_assoc]
  ext n
  cases n with
  | zero =>
    simp [geometricPowerSeries]
  | succ n =>
    simp [hX, pow_succ, mul_comm]

noncomputable def geometricPoleSeries (c : K) : PowerSeries K :=
  -PowerSeries.C c⁻¹*geometricPowerSeries c⁻¹

theorem geometric_pole_power_series_identity (c : K) (hc : c≠0) :
    (PowerSeries.X-PowerSeries.C c)*geometricPoleSeries c = 1 := by
  unfold geometricPoleSeries
  calc
    _ = (1-PowerSeries.C c⁻¹*PowerSeries.X)*geometricPowerSeries c⁻¹ := by
      have h : PowerSeries.C c*PowerSeries.C c⁻¹ = (1 : PowerSeries K) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      linear_combination geometricPowerSeries c⁻¹*h
    _ = 1 := geometric_power_series_identity _

theorem geometric_pole_inverse (c : K) (hc : c≠0) :
    (single (1 : ℤ) (1 : K)-HahnSeries.C c)⁻¹ =
      (geometricPoleSeries c : LaurentSeries K) := by
  have hprod := congrArg (fun F : PowerSeries K => (F : LaurentSeries K))
    (geometric_pole_power_series_identity c hc)
  simp only [PowerSeries.coe_mul, PowerSeries.coe_sub, PowerSeries.coe_X,
    PowerSeries.coe_C, PowerSeries.coe_one] at hprod
  have hn : (single (1 : ℤ) (1 : K)-HahnSeries.C c : LaurentSeries K) ≠ 0 := by
    intro h
    have h0 := congrArg (fun F : LaurentSeries K => F.coeff 0) h
    simp [HahnSeries.C_apply, hc] at h0
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn, hprod]

theorem geometric_pole_residue (a b : ℕ) (l c : K) (hc : c≠0) :
    ((single ((a : ℤ)-(b : ℤ)) (l^b) : LaurentSeries K) *
      (single (1 : ℤ) 1-HahnSeries.C c)⁻¹).coeff (-1) =
      if a<b then -(l^b*(c⁻¹)^(b-a)) else 0 := by
  rw [geometric_pole_inverse c hc, coeff_single_mul, PowerSeries.coeff_coe]
  by_cases hab : a<b
  · have hi : ¬(-1-((a : ℤ)-(b : ℤ))<0) := by omega
    have hn : Int.natAbs (-1-((a : ℤ)-(b : ℤ))) = b-a-1 := by omega
    rw [if_neg hi, hn, if_pos hab]
    simp only [geometricPoleSeries, neg_mul, map_neg,
      PowerSeries.coeff_C_mul, geometric_power_series_coeff]
    have hpow : (c⁻¹)^(b-a) = (c⁻¹)^(b-a-1)*c⁻¹ := by
      calc
        _ = (c⁻¹)^((b-a-1)+1) := congrArg (fun n : ℕ => (c⁻¹)^n) (by omega)
        _ = _ := pow_succ _ _
    rw [hpow]
    ring
  · have hi : -1-((a : ℤ)-(b : ℤ))<0 := by omega
    rw [if_pos hi, if_neg hab, mul_zero]

theorem geometric_unit_pole_residue (a b : ℕ) (l : K) :
    ((single ((a : ℤ)-(b : ℤ)) (l^b) : LaurentSeries K) *
      (single (1 : ℤ) 1-1)⁻¹).coeff (-1) =
      if a<b then -(l^b) else 0 := by
  simpa using geometric_pole_residue a b l (1 : K) one_ne_zero

theorem geometric_diagonal_pole_residue (a b : ℕ) (l : K) (hl : l≠0) :
    ((single ((a : ℤ)-(b : ℤ)) (l^b) : LaurentSeries K) *
      (single (1 : ℤ) 1-HahnSeries.C l)⁻¹).coeff (-1) =
      if a<b then -(l^a) else 0 := by
  rw [geometric_pole_residue a b l l hl]
  split_ifs with hab
  · have hb : b=a+(b-a) := by omega
    have hb' : l^b=l^a*l^(b-a) := by
      calc
        _ = l^(a+(b-a)) := congrArg (fun n : ℕ => l^n) hb
        _ = _ := pow_add _ _ _
    rw [hb', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hl), mul_one]
  · rfl

end

end WPForcedSourceStokes
