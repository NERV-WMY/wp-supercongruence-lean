import WPFirstResidue.ConicRankDensity
import WPFirstResidue.ConicCross.UnramifiedResidue

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicWeightedResidue WPFirstResidue.ConicRankDensity
  WPMomentPrecision.QuadraticResidueTransport

namespace WPFirstResidue.ConicCross

variable {K E : Type*} [Field K] [Field E]

/-- The literal coefficient map, including every negative Laurent coefficient. -/
noncomputable def coefficientExtension (f : K →+* E) : K⸨X⸩ →+* E⸨X⸩ where
  toFun F := F.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom

theorem coefficientExtension_coeff (f : K →+* E) (F : K⸨X⸩) (j : ℤ) :
    (coefficientExtension f F).coeff j = f (F.coeff j) := rfl

theorem coefficientExtension_constant (f : K →+* E) (a : K) :
    coefficientExtension f (HahnSeries.C a) = HahnSeries.C (f a) :=
  HahnSeries.map_C a f

theorem coefficientExtension_localX (f : K →+* E) :
    coefficientExtension f (localX : K⸨X⸩) = (localX : E⸨X⸩) := by
  ext j
  simp only [coefficientExtension_coeff, localX, HahnSeries.coeff_single]
  by_cases hj : j = 1
  · simp [hj]
  · simp [hj]

theorem coefficientExtension_coefficients (f : K →+* E) :
    (coefficientExtension f).comp (HahnSeries.C : K →+* K⸨X⸩) =
      (HahnSeries.C : E →+* E⸨X⸩).comp f := by
  apply RingHom.ext
  intro a
  exact coefficientExtension_constant f a

theorem actual_weighted_residue_zero_over_extension (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (f : ZMod p →+* K) :
    (coefficientExtension f (actualConicWeightedDensity p)).coeff (-1) = 0 := by
  rw [coefficientExtension_coeff, actual_conic_weighted_residue_zero p hp, map_zero]

theorem actual_weighted_source_over_extension (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (f : ZMod p →+* K) :
    coefficientExtension f (actualConicWeightedDensity p) =
      WPMomentPrecision.ConicCoordinates.L (localX : K⸨X⸩)⁻¹ ^ p *
        (-((localX : K⸨X⸩)⁻¹) ^ 2 *
          nativeOmegaDensity p ((HahnSeries.C : K →+* K⸨X⸩).comp f)
            (localX : K⸨X⸩)⁻¹) := by
  have hv : conicLocalVariable p = (localX : (ZMod p)⸨X⸩) := PowerSeries.coe_X
  have hf : (coefficientExtension f).comp (algebraMap (ZMod p) (ZMod p)⸨X⸩) =
      (HahnSeries.C : K →+* K⸨X⸩).comp f := by
    rw [coefficient_algebraMap_laurent]
    exact coefficientExtension_coefficients f
  rw [actual_native_weighted_infinity_density p hp, hv]
  simp only [map_mul, map_pow, map_neg, map_inv₀, map_nativeOmegaDensity,
    hf, coefficientExtension_localX, WPMomentPrecision.ConicCoordinates.L,
    map_div₀, map_sub, map_one, map_ofNat]

theorem branchSubstitution_coefficients (c : K) (hc : c ≠ 0) :
    (branchSubstitution c hc).comp (HahnSeries.C : K →+* K⸨X⸩) = HahnSeries.C := by
  apply RingHom.ext
  intro a
  exact branchSubstitution_constant c hc a

theorem branchSubstitution_field_coefficients (c : K) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (f : ZMod p →+* K) :
    (branchSubstitution c hc).comp ((HahnSeries.C : K →+* K⸨X⸩).comp f) =
      (HahnSeries.C : K →+* K⸨X⸩).comp f := by
  apply RingHom.ext
  intro a
  exact branchSubstitution_constant c hc (f a)

theorem quadraticSubstitution_field_coefficients (h4 : (4 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] (f : ZMod p →+* K) :
    (WPMomentPrecision.QuadraticLaurentPullback.coverSubstitution h4).comp
      ((HahnSeries.C : K →+* K⸨X⸩).comp f) =
      (HahnSeries.C : K →+* K⸨X⸩).comp f := by
  apply RingHom.ext
  intro a
  exact WPMomentPrecision.QuadraticLaurentPullback.coverSubstitution_constant h4 (f a)

end WPFirstResidue.ConicCross
