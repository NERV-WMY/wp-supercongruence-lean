import WPFirstResidue.ConicCross.Geometry
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualConicWeightedResidue
  WPFirstResidue.ConicRankDensity WPMomentPrecision.ConicCoordinates
  WPMomentPrecision.QuadraticResidueTransport WPMomentPrecision.QuadraticLaurentPullback

namespace WPFirstResidue.ConicCross

variable {K : Type*} [Field K]

theorem field_small_nat_ne_zero (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n) (hnp : n < p) (f : ZMod p →+* K) : (n : K) ≠ 0 := by
  have hu := WPActualGaussProper.small_cast_ne_zero p n hn hnp
  simpa only [map_natCast] using (map_ne_zero f).mpr hu

theorem extension_branch_weighted_density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (c : K) (hc : c ≠ 0) :
    branchSubstitution c hc (coefficientExtension f (actualConicWeightedDensity p)) =
      L (branchV (HahnSeries.C c) (localX : K⸨X⸩))⁻¹ ^ p *
        (-((branchV (HahnSeries.C c) (localX : K⸨X⸩))⁻¹) ^ 2 *
          nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
            (branchV (HahnSeries.C c) (localX : K⸨X⸩))⁻¹) := by
  rw [actual_weighted_source_over_extension p hp f]
  simp only [map_mul, map_pow, map_neg, map_inv₀, map_nativeOmegaDensity,
    branchSubstitution_field_coefficients, branchSubstitution_localX,
    L, map_div₀, map_sub, map_one, map_ofNat]

/-- Residue zero is transported from the actual full source into one chosen conic branch. -/
theorem actual_weighted_branch_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (c : K) (hc : c ≠ 0) :
    (branchSubstitution c hc (coefficientExtension f (actualConicWeightedDensity p)) *
      branchVJacobian (HahnSeries.C c) (localX : K⸨X⸩)).coeff (-1) = 0 := by
  rw [complete_unramified_residue_transport,
    actual_weighted_residue_zero_over_extension p hp f]

theorem actual_weighted_chart_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (f : ZMod p →+* K) (a : K) (ha0 : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    (L (branchU (HahnSeries.C a) (localX : K⸨X⸩)) ^ p *
      nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
        (branchU (HahnSeries.C a) (localX : K⸨X⸩)) *
      branchUJacobian (HahnSeries.C a) (localX : K⸨X⸩)).coeff (-1) = 0 := by
  have hc : 2 * a ≠ 0 := mul_ne_zero h2 ha0
  have haL : (HahnSeries.C a : K⸨X⸩) ≠ 0 := HahnSeries.C_ne_zero ha0
  have h2L : (2 : K⸨X⸩) ≠ 0 := by
    simpa only [map_ofNat] using (HahnSeries.C_ne_zero (Γ := ℤ) h2)
  have hC : (HahnSeries.C (2 * a) : K⸨X⸩) = 2 * HahnSeries.C a := by
    simp only [map_mul, map_ofNat]
  have hv := chart_v (HahnSeries.C a) (localX : K⸨X⸩) haL h2L
    localX_ne_zero branchUnit_ne_zero
  have hj := chart_v_jacobian (HahnSeries.C a) (localX : K⸨X⸩) haL h2L
    localX_ne_zero branchUnit_ne_zero
  have hs := actual_weighted_branch_residue_zero p hp f (2 * a) hc
  rw [extension_branch_weighted_density p hp f, hC, hv] at hs
  have he : L (branchU (HahnSeries.C a) (localX : K⸨X⸩)) ^ p *
      (-((branchU (HahnSeries.C a) (localX : K⸨X⸩))) ^ 2 *
        nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
          (branchU (HahnSeries.C a) (localX : K⸨X⸩))) *
      branchVJacobian (2 * HahnSeries.C a) (localX : K⸨X⸩) =
      L (branchU (HahnSeries.C a) (localX : K⸨X⸩)) ^ p *
        nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
          (branchU (HahnSeries.C a) (localX : K⸨X⸩)) *
        branchUJacobian (HahnSeries.C a) (localX : K⸨X⸩) := by
    rw [hv] at hj
    rw [← hj]
    ring
  rw [he] at hs
  exact hs

theorem original_cross_quadratic_substitution (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) (h4 : (4 : K) ≠ 0) :
    coverSubstitution h4
      (nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f) (localX : K⸨X⸩)) =
      nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
        (coverX (localX : K⸨X⸩)) := by
  rw [map_nativeCrossDensity, quadraticSubstitution_field_coefficients,
    coverSubstitution_localX]

/-- The original x residue vanishes through branchwise factors two and one. -/
theorem actual_native_cross_residue_zero_over_extension (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (f : ZMod p →+* K) (a : K) (ha : a ^ 2 = 5) :
    (nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
      (localX : K⸨X⸩)).coeff (-1) = 0 := by
  have h2 : (2 : K) ≠ 0 := field_small_nat_ne_zero p 2 (by omega) (by omega) f
  have h4 : (4 : K) ≠ 0 := field_small_nat_ne_zero p 4 (by omega) (by omega) f
  have h5 : (5 : K) ≠ 0 := field_small_nat_ne_zero p 5 (by omega) (by omega) f
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ha
    exact h5 ha.symm
  have haL : (HahnSeries.C a : K⸨X⸩) ^ 2 = 5 := by
    simpa only [map_pow, map_ofNat] using congrArg (HahnSeries.C (Γ := ℤ)) ha
  have h2L : (2 : K⸨X⸩) ≠ 0 := by
    simpa only [map_ofNat] using (HahnSeries.C_ne_zero (Γ := ℤ) h2)
  have h5L : (5 : K⸨X⸩) ≠ 0 := by
    simpa only [map_ofNat] using (HahnSeries.C_ne_zero (Γ := ℤ) h5)
  have ht := actual_cross_chart_density p hp ((HahnSeries.C : K →+* K⸨X⸩).comp f)
    (HahnSeries.C a) (localX : K⸨X⸩) haL (HahnSeries.C_ne_zero ha0)
    h2L h5L localX_ne_zero coverUnit_ne_zero branchUnit_ne_zero
    (chartT_first_factor_ne_zero a ha ha0 h4) (chartT_second_factor_ne_zero a ha ha0)
  have hs := actual_weighted_chart_residue_zero p hp f a ha0 h2
  have hchart : (nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
      (coverX (localX : K⸨X⸩)) * coverJacobian (localX : K⸨X⸩)).coeff (-1) = 0 := by
    rw [ht]
    have h6 : (6 : K⸨X⸩) = HahnSeries.C (6 : K) := (map_ofNat _ 6).symm
    rw [show 6 * L (branchU (HahnSeries.C a) (localX : K⸨X⸩)) ^ p *
      nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
        (branchU (HahnSeries.C a) (localX : K⸨X⸩)) *
      branchUJacobian (HahnSeries.C a) (localX : K⸨X⸩) =
      HahnSeries.C (6 : K) * (L (branchU (HahnSeries.C a) (localX : K⸨X⸩)) ^ p *
        nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
          (branchU (HahnSeries.C a) (localX : K⸨X⸩)) *
        branchUJacobian (HahnSeries.C a) (localX : K⸨X⸩)) by rw [h6]; ring,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hs, smul_zero]
  have hquad := complete_quadratic_residue_transport h4
    (nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f) (localX : K⸨X⸩))
  rw [original_cross_quadratic_substitution, hchart] at hquad
  exact (mul_eq_zero.mp hquad.symm).resolve_left h2

theorem coefficientExtension_nativeCrossDensity (p : ℕ) [Fact p.Prime]
    (f : ZMod p →+* K) :
    coefficientExtension f
      (nativeCrossDensity p (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) localX) =
      nativeCrossDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f) (localX : K⸨X⸩) := by
  rw [map_nativeCrossDensity, coefficientExtension_coefficients,
    coefficientExtension_localX]

/-- No square-root choice or geometric residue-equality hypothesis remains in the base-field export. -/
theorem actual_native_cross_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeCrossDensity p (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩)
      (localX : (ZMod p)⸨X⸩)).coeff (-1) = 0 := by
  let K := AlgebraicClosure (ZMod p)
  let f := algebraMap (ZMod p) K
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (5 : K) (by norm_num : 0 < (2 : ℕ))
  have he := actual_native_cross_residue_zero_over_extension p hp f a ha
  rw [← coefficientExtension_nativeCrossDensity p f, coefficientExtension_coeff] at he
  exact (map_eq_zero f).mp he

noncomputable def actualNativeCrossRational (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) :=
  nativeCrossDensity p RatFunc.C RatFunc.X

/-- The zero coefficient belongs to the original actual rational cross differential. -/
theorem actual_rational_cross_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (actualNativeCrossRational p)).coeff (-1) = 0 := by
  have hX : algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ RatFunc.X =
      (localX : (ZMod p)⸨X⸩) := RatFunc.coe_X
  have hf : (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩).comp RatFunc.C =
      (HahnSeries.C : ZMod p →+* (ZMod p)⸨X⸩) :=
    rational_coefficient_hom_laurent.trans coefficient_algebraMap_laurent
  rw [actualNativeCrossRational, map_nativeCrossDensity, hf, hX]
  exact actual_native_cross_residue_zero p hp

end WPFirstResidue.ConicCross
