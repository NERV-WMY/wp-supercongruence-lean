import WPFirstResidue.ConicCross.FieldExtension
import WPFirstResidue.LaurentDifferential

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualNativeHasse
  WPFirstResidue.ConicRankDensity WPMomentPrecision.ConicCoordinates
  WPMomentPrecision.QuadraticResidueTransport

namespace WPFirstResidue.ConicCross

variable {K E : Type*} [Field K] [Field E]

def branchU (a z : K) : K := (1 + z ^ 2) / (2 * a * z)
def branchUJacobian (a z : K) : K := (z ^ 2 - 1) / (2 * a * z ^ 2)
def chartTJacobian (a z : K) : K := 4 * z / (a * (1 - z ^ 2) ^ 2)
def chartWJacobian (z : K) : K := 2 * (1 + z ^ 2) / (1 - z ^ 2) ^ 2

theorem chart_x (z : K) : conicW z ^ 2 = coverX z := by
  unfold conicW coverX
  rw [div_pow]
  ring

theorem chart_u (a z : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hz : z ≠ 0) (hu : 1 - z ^ 2 ≠ 0) : conicT a z / conicW z = branchU a z := by
  unfold conicT conicW branchU
  field_simp

theorem chart_v (a z : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hz : z ≠ 0) (hu : 1 + z ^ 2 ≠ 0) :
    (branchV (2 * a) z)⁻¹ = branchU a z := by
  unfold branchV branchU
  field_simp

theorem chart_w_jacobian (z : K) (hu : 1 - z ^ 2 ≠ 0) :
    2 * conicW z * chartWJacobian z = coverJacobian z := by
  unfold conicW chartWJacobian coverJacobian
  field_simp
  ring

theorem chart_x_jacobian (a z : K) (ha : a ^ 2 = 5) (ha0 : a ≠ 0)
    (hu : 1 - z ^ 2 ≠ 0) :
    10 * conicT a z * chartTJacobian a z = coverJacobian z := by
  unfold conicT chartTJacobian coverJacobian
  field_simp
  linear_combination -8 * z * (1 + z ^ 2) * ha

/-- The negative du/dt and the signed reciprocal dv/du remain literal. -/
theorem chart_u_jacobian (a z : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hz : z ≠ 0) (_hu : 1 - z ^ 2 ≠ 0) :
    (-1 / conicW z ^ 3) * chartTJacobian a z = branchUJacobian a z := by
  unfold conicW chartTJacobian branchUJacobian
  field_simp
  ring

theorem chart_v_jacobian (a z : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hz : z ≠ 0) (hu : 1 + z ^ 2 ≠ 0) :
    -((branchV (2 * a) z)⁻¹) ^ 2 * branchVJacobian (2 * a) z = branchUJacobian a z := by
  unfold branchV branchVJacobian branchUJacobian
  field_simp
  ring

/-- Actual original x-line cross differential coefficient, retaining the full native denominator. -/
noncomputable def nativeCrossDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (x : K) : K :=
  (nativeHField p).eval₂ f (Q x) * (1 - V x) ^ ((p - 1) / 2) /
    (nativeField p (p / 6)).eval₂ f (V x) *
    (8 / (4 * x - 1) + 1 / (x - 4))

theorem map_nativeCrossDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (g : K →+* E) (x : K) :
    g (nativeCrossDensity p f x) = nativeCrossDensity p (g.comp f) (g x) := by
  simp only [nativeCrossDensity, map_mul, map_div₀, Polynomial.hom_eval₂, map_pow,
    Q, V, map_sub, map_one, map_ofNat, map_add]

/-- Complete actual conic chart transport; no Hasse value at a residue point is assumed invertible. -/
theorem actual_cross_chart_density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (a z : K) (ha : a ^ 2 = 5) (ha0 : a ≠ 0)
    (h2 : (2 : K) ≠ 0) (h5 : (5 : K) ≠ 0) (hz : z ≠ 0)
    (hminus : 1 - z ^ 2 ≠ 0) (_hplus : 1 + z ^ 2 ≠ 0)
    (hA : 1 - conicT a z ^ 2 ≠ 0) (hB : 4 * conicT a z ^ 2 - 1 ≠ 0) :
    nativeCrossDensity p f (coverX z) * coverJacobian z =
      6 * L (branchU a z) ^ p * nativeOmegaDensity p f (branchU a z) *
        branchUJacobian a z := by
  have hc := conic_parameterization a z ha ha0 hminus
  have hw : conicW z ≠ 0 := div_ne_zero (mul_ne_zero h2 hz) hminus
  have hv := native_V_on_conic (conicT a z) (conicW z) h5 hc
  have hq := native_Q_on_conic (conicT a z) (conicW z) h5 hw hc
  have hqu : Q (conicW z ^ 2) = q (branchU a z) := by
    rw [hq, chart_u a z ha0 h2 hz hminus]
  have ht := actual_native_cross_density p (by omega) f ((nativeHField p).map f)
    (conicT a z) (conicW z) h5 hw hA hB hc
  simp only [Polynomial.eval_map] at ht
  have he := congrArg (fun g : K => g * chartTJacobian a z) ht
  rw [chart_u a z ha0 h2 hz hminus] at he
  rw [← hv, ← hqu] at he
  have hx := chart_x_jacobian a z ha ha0 hminus
  have hu := chart_u_jacobian a z ha0 h2 hz hminus
  unfold nativeCrossDensity nativeOmegaDensity
  rw [← chart_x z, ← hx, ← hu, ← hqu]
  linear_combination he

noncomputable def chartTSeries (a : K) : K⟦X⟧ :=
  PowerSeries.C a⁻¹ * (1 + PowerSeries.X ^ 2) *
    (WPMomentPrecision.QuadraticResidueTransport.coverUnit : K⟦X⟧)⁻¹

noncomputable def chartTJacobianSeries (a : K) : K⟦X⟧ :=
  4 * PowerSeries.C a⁻¹ * PowerSeries.X * (coverUnit : K⟦X⟧)⁻¹ ^ 2

theorem actual_chart_x_derivative :
    PowerSeries.derivative K (WPMomentPrecision.QuadraticCoverSeries.coverSeries : K⟦X⟧) =
      WPMomentPrecision.QuadraticCoverSeries.jacobianSeries := by
  have hi := PowerSeries.inv_mul_cancel (coverUnit : K⟦X⟧)
    (by rw [coverUnit_origin]; exact one_ne_zero)
  dsimp only [coverUnit] at hi
  have derivativeFour := (PowerSeries.derivative K).map_natCast 4
  change PowerSeries.derivative K (4 : K⟦X⟧) = 0 at derivativeFour
  simp [WPMomentPrecision.QuadraticCoverSeries.coverSeries,
    WPMomentPrecision.QuadraticCoverSeries.jacobianSeries, coverUnit, derivativeFour]
  linear_combination -8 * PowerSeries.X * (1 - PowerSeries.X ^ 2)⁻¹ ^ 2 * hi

theorem actual_chart_t_derivative (a : K) :
    PowerSeries.derivative K (chartTSeries a) = chartTJacobianSeries a := by
  have hi := PowerSeries.inv_mul_cancel (coverUnit : K⟦X⟧)
    (by rw [coverUnit_origin]; exact one_ne_zero)
  dsimp only [coverUnit] at hi
  simp [chartTSeries, chartTJacobianSeries, coverUnit]
  linear_combination -2 * PowerSeries.C a⁻¹ * PowerSeries.X *
    (1 - PowerSeries.X ^ 2)⁻¹ * hi

theorem chartTJacobianSeries_cast (a : K) :
    ((chartTJacobianSeries a : K⟦X⟧) : K⸨X⸩) =
      chartTJacobian (HahnSeries.C a) (localX : K⸨X⸩) := by
  simp only [chartTJacobianSeries, PowerSeries.coe_mul, PowerSeries.coe_C,
    PowerSeries.coe_pow, PowerSeries.coe_X,
    WPRationalInfinitySeries.powerSeries_inverse_cast (coverUnit : K⟦X⟧)
      (by rw [coverUnit_origin]; exact one_ne_zero),
    coverUnit_cast, map_ofNat, map_inv₀, localX, chartTJacobian,
    div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem chartTSeries_origin (a : K) :
    PowerSeries.constantCoeff (chartTSeries a) = a⁻¹ := by
  simp [chartTSeries, coverUnit]

theorem chartTSeries_cast (a : K) (_ha : a ≠ 0) :
    ((chartTSeries a : K⟦X⟧) : K⸨X⸩) = conicT (HahnSeries.C a) localX := by
  simp only [chartTSeries, PowerSeries.coe_mul, PowerSeries.coe_C, PowerSeries.coe_add,
    PowerSeries.coe_one, PowerSeries.coe_pow, PowerSeries.coe_X,
    WPRationalInfinitySeries.powerSeries_inverse_cast (coverUnit : K⟦X⟧)
      (by rw [coverUnit_origin]; exact one_ne_zero),
    coverUnit_cast, localX, conicT, map_inv₀, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The original x Jacobian is the derivative of the complete Laurent chart. -/
theorem actual_chart_x_laurent_derivative :
    LaurentSeries.derivative K (coverX (localX : K⸨X⸩)) =
      coverJacobian (localX : K⸨X⸩) := by
  rw [← WPMomentPrecision.QuadraticCoverSeries.coverSeries_cast,
    WPFirstResidue.LaurentDifferential.derivative_powerSeries,
    actual_chart_x_derivative, WPMomentPrecision.QuadraticCoverSeries.jacobianSeries_cast]

theorem actual_chart_t_laurent_derivative (a : K) (ha : a ≠ 0) :
    LaurentSeries.derivative K (conicT (HahnSeries.C a) (localX : K⸨X⸩)) =
      chartTJacobian (HahnSeries.C a) (localX : K⸨X⸩) := by
  rw [← chartTSeries_cast a ha, WPFirstResidue.LaurentDifferential.derivative_powerSeries,
    actual_chart_t_derivative, chartTJacobianSeries_cast]

theorem actual_chart_v_laurent_derivative (c : K) :
    LaurentSeries.derivative K (branchV (HahnSeries.C c) (localX : K⸨X⸩)) =
      branchVJacobian (HahnSeries.C c) (localX : K⸨X⸩) := by
  rw [← branchSeries_cast, WPFirstResidue.LaurentDifferential.derivative_powerSeries,
    branchSeries_derivative, branchJacobianSeries_cast]

/-- The pole of u is differentiated in the full Laurent field, retaining its negative sign. -/
theorem actual_chart_u_laurent_derivative (a : K) (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    LaurentSeries.derivative K (branchU (HahnSeries.C a) (localX : K⸨X⸩)) =
      branchUJacobian (HahnSeries.C a) (localX : K⸨X⸩) := by
  have haL : (HahnSeries.C a : K⸨X⸩) ≠ 0 := HahnSeries.C_ne_zero ha
  have h2L : (2 : K⸨X⸩) ≠ 0 := by
    simpa only [map_ofNat] using (HahnSeries.C_ne_zero (Γ := ℤ) h2)
  have hv := chart_v (HahnSeries.C a) (localX : K⸨X⸩) haL h2L
    localX_ne_zero branchUnit_ne_zero
  have hj := chart_v_jacobian (HahnSeries.C a) (localX : K⸨X⸩) haL h2L
    localX_ne_zero branchUnit_ne_zero
  have hdv := actual_chart_v_laurent_derivative (2 * a)
  simp only [map_mul, map_ofNat] at hdv
  rw [← hv, WPFirstResidue.LaurentDifferential.derivative_inverse, hdv]
  calc
    _ = -((branchV (2 * HahnSeries.C a) (localX : K⸨X⸩))⁻¹) ^ 2 *
        branchVJacobian (2 * HahnSeries.C a) (localX : K⸨X⸩) := by ring
    _ = _ := hj

theorem chartT_first_factor_origin_ne_zero (a : K) (ha : a ^ 2 = 5)
    (ha0 : a ≠ 0) (h4 : (4 : K) ≠ 0) : 1 - (a⁻¹) ^ 2 ≠ 0 := by
  intro h
  have he : a ^ 2 - 1 = 0 := by
    field_simp [ha0] at h
    linear_combination h
  apply h4
  linear_combination he - ha

theorem chartT_second_factor_origin_ne_zero (a : K) (ha : a ^ 2 = 5)
    (ha0 : a ≠ 0) : 4 * (a⁻¹) ^ 2 - 1 ≠ 0 := by
  intro h
  have he : 4 - a ^ 2 = 0 := by
    field_simp [ha0] at h
    linear_combination h
  apply (one_ne_zero : (1 : K) ≠ 0)
  linear_combination -he - ha

theorem chartT_first_factor_ne_zero (a : K) (ha : a ^ 2 = 5)
    (ha0 : a ≠ 0) (h4 : (4 : K) ≠ 0) :
    1 - conicT (HahnSeries.C a) (localX : K⸨X⸩) ^ 2 ≠ 0 := by
  rw [← chartTSeries_cast a ha0]
  intro hz
  have hc := congrArg (fun F : K⸨X⸩ => F.coeff 0) hz
  rw [← PowerSeries.coe_one, ← PowerSeries.coe_pow, ← PowerSeries.coe_sub] at hc
  rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_zero] at hc
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_one, map_pow,
    chartTSeries_origin, HahnSeries.coeff_zero] at hc
  exact chartT_first_factor_origin_ne_zero a ha ha0 h4 hc

theorem chartT_second_factor_ne_zero (a : K) (ha : a ^ 2 = 5) (ha0 : a ≠ 0) :
    4 * conicT (HahnSeries.C a) (localX : K⸨X⸩) ^ 2 - 1 ≠ 0 := by
  rw [← chartTSeries_cast a ha0]
  intro hz
  have h4L : (4 : K⸨X⸩) = ((4 : K⟦X⟧) : K⸨X⸩) := (map_ofNat _ 4).symm
  have hc := congrArg (fun F : K⸨X⸩ => F.coeff 0) hz
  rw [h4L, ← PowerSeries.coe_pow, ← PowerSeries.coe_mul,
    ← PowerSeries.coe_one, ← PowerSeries.coe_sub] at hc
  rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_zero] at hc
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_mul, map_one,
    map_ofNat, map_pow, chartTSeries_origin, HahnSeries.coeff_zero] at hc
  exact chartT_second_factor_origin_ne_zero a ha ha0 hc

end WPFirstResidue.ConicCross
