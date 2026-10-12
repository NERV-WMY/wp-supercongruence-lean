import WPFirstResidue.RankDensity.Source

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualConicInfinityAttachment
  WPRamifiedRegularResonance WPRationalInfinitySeries WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.ConicRankDensity

variable {K L : Type*} [Field K] [Field L]

theorem coefficient_algebraMap_laurent :
    algebraMap K K⸨X⸩ = (HahnSeries.C : K →+* K⸨X⸩) := by
  apply RingHom.ext
  intro a
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
  exact PowerSeries.coe_C a

theorem rational_C_laurent (a : K) :
    algebraMap (RatFunc K) K⸨X⸩ (RatFunc.C a) = HahnSeries.C a := by
  rw [← RatFunc.algebraMap_C]
  simpa only [RatFunc.coePolynomial, Polynomial.coe_C, PowerSeries.coe_C] using
    (RatFunc.coe_coe (Polynomial.C a)).symm

theorem rational_coefficient_hom_laurent :
    (algebraMap (RatFunc K) K⸨X⸩).comp RatFunc.C = algebraMap K K⸨X⸩ := by
  apply RingHom.ext
  intro a
  change algebraMap (RatFunc K) K⸨X⸩ (RatFunc.C a) = algebraMap K K⸨X⸩ a
  rw [rational_C_laurent, coefficient_algebraMap_laurent]

theorem powerSeries_natCast_laurent (n : ℕ) :
    (((n : K⟦X⟧) : K⟦X⟧) : K⸨X⸩) = (n : K⸨X⸩) :=
  map_natCast (algebraMap K⟦X⟧ K⸨X⸩) n

theorem polynomial_reflect_eval₂ (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (f : K →+* L) (s : L) (hs : s ≠ 0) :
    (P.reflect m).eval₂ f s = s ^ m * P.eval₂ f s⁻¹ := by
  have he := WPActualHasseReciprocal.eval_reflect m (P.map f)
    (Polynomial.natDegree_map_le.trans hP) s hs
  simpa only [Polynomial.reflect_map, Polynomial.eval_map] using he

theorem polynomial_subst_laurent (P : K[X]) (s : K⟦X⟧) (hs : PowerSeries.HasSubst s) :
    (((P : K⟦X⟧).subst s : K⟦X⟧) : K⸨X⸩) =
      P.eval₂ (algebraMap K K⸨X⸩) (s : K⸨X⸩) := by
  rw [PowerSeries.subst_coe hs, Polynomial.aeval_def]
  change (algebraMap K⟦X⟧ K⸨X⸩) (P.eval₂ (algebraMap K K⟦X⟧) s) = _
  rw [Polynomial.hom_eval₂]
  congr 1

theorem polynomial_subst_origin (P : K[X]) (s : K⟦X⟧)
    (hs : PowerSeries.HasSubst s) (hs0 : PowerSeries.constantCoeff s = 0) :
    PowerSeries.constantCoeff ((P : K⟦X⟧).subst s) = P.coeff 0 := by
  rw [PowerSeries.subst_coe hs, Polynomial.aeval_def, Polynomial.hom_eval₂, hs0,
    Polynomial.eval₂_at_zero]
  simp

/-- Substitute the complete rational rank density, using the actual cleared denominator. -/
theorem actual_rank_substituted_representation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (s : (ZMod p)⟦X⟧) (hs : PowerSeries.HasSubst s)
    (hsorigin : PowerSeries.constantCoeff s = 0) (hs0 : (s : (ZMod p)⸨X⸩) ≠ 0) :
    (((rankInfinitySeries p).subst s : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      -(s : (ZMod p)⸨X⸩)⁻¹ ^ 2 *
        nativeRankDensity p (algebraMap (ZMod p) (ZMod p)⸨X⸩)
          (s : (ZMod p)⸨X⸩)⁻¹ := by
  let m := 2 * (p / 6)
  let P := rankDensityNumerator p
  let D := rankDensityDenominator p
  let f := algebraMap (ZMod p) (ZMod p)⸨X⸩
  have hP : P.natDegree ≤ m := rankDensityNumerator_degree p
  have hD : D.natDegree ≤ m + 2 := (rankDensityDenominator_degree p hp).le
  have hunit : PowerSeries.constantCoeff
      (((D.reflect (m + 2) : (ZMod p)⟦X⟧).subst s)) ≠ 0 := by
    rw [polynomial_subst_origin _ _ hs hsorigin]
    simpa only [Polynomial.constantCoeff_coe] using rankInfinityDenominator_unit p hp
  have hcast : (((D.reflect (m + 2) : (ZMod p)⟦X⟧).subst s :
      (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) ≠ 0 := by
    intro he
    have hz : (D.reflect (m + 2) : (ZMod p)⟦X⟧).subst s = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ)
        (by simpa only [PowerSeries.coe_zero] using he)
    have hcc := congrArg (PowerSeries.constantCoeff (R := ZMod p)) hz
    exact hunit (by simpa using hcc)
  rw [polynomial_subst_laurent _ _ hs] at hcast
  have hc := congrArg (fun a : (ZMod p)⟦X⟧ =>
      ((a.subst s : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩))
    (rankInfinitySeries_cleared p hp)
  have hn := PowerSeries.coe_substAlgHom (R := ZMod p) hs
  simp only [← hn, map_mul, map_neg] at hc
  simp only [hn, polynomial_subst_laurent _ _ hs] at hc
  change (((rankInfinitySeries p).subst s : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) *
      (D.reflect (m + 2)).eval₂ f (s : (ZMod p)⸨X⸩) =
      -(P.reflect m).eval₂ f (s : (ZMod p)⸨X⸩) at hc
  have hDz : D.eval₂ f (s : (ZMod p)⸨X⸩)⁻¹ ≠ 0 := by
    rw [polynomial_reflect_eval₂ (m + 2) D hD f _ hs0] at hcast
    exact (mul_ne_zero_iff.mp hcast).2
  calc
    _ = -(P.reflect m).eval₂ f (s : (ZMod p)⸨X⸩) /
        (D.reflect (m + 2)).eval₂ f (s : (ZMod p)⸨X⸩) :=
      (eq_div_iff hcast).mpr hc
    _ = _ := by
      rw [polynomial_reflect_eval₂ m P hP f _ hs0,
        polynomial_reflect_eval₂ (m + 2) D hD f _ hs0, pow_add]
      unfold nativeRankDensity
      dsimp only [P, D, f] at hDz ⊢
      field_simp [hs0, hDz]

/-- v is the literal infinity coordinate 1/u. -/
noncomputable def conicLocalVariable (p : ℕ) [Fact p.Prime] : (ZMod p)⸨X⸩ :=
  ((PowerSeries.X : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)

theorem conicLocalVariable_ne_zero (p : ℕ) [Fact p.Prime] :
    conicLocalVariable p ≠ 0 := by
  rw [conicLocalVariable, PowerSeries.coe_X]
  exact HahnSeries.single_ne_zero one_ne_zero

theorem conicInfinitySeries_origin (p : ℕ) [Fact p.Prime] :
    PowerSeries.constantCoeff (conicInfinitySeries p) = 0 := by
  simp [conicInfinitySeries]

theorem conicInfinitySeries_hasSubst (p : ℕ) [Fact p.Prime] :
    PowerSeries.HasSubst (conicInfinitySeries p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (conicInfinitySeries_origin p)

theorem conic_infinity_denominator_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff (4 - 3 * PowerSeries.X ^ 2 : (ZMod p)⟦X⟧) ≠ 0 := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  simpa [map_ofNat] using h4

theorem conicInfinitySeries_laurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((conicInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      conicLocalVariable p ^ 3 / (4 - 3 * conicLocalVariable p ^ 2) := by
  rw [conicInfinitySeries, PowerSeries.coe_mul,
    powerSeries_inverse_cast _ (conic_infinity_denominator_unit p hp)]
  simp only [PowerSeries.coe_pow, PowerSeries.coe_sub, PowerSeries.coe_mul,
    map_ofNat, div_eq_mul_inv, conicLocalVariable]

theorem conic_infinity_denominator_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    4 - 3 * conicLocalVariable p ^ 2 ≠ 0 := by
  have hunit := conic_infinity_denominator_unit p hp
  intro he
  have hcast : (((4 - 3 * PowerSeries.X ^ 2 : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)) =
      4 - 3 * conicLocalVariable p ^ 2 := by
    simp only [PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow,
      map_ofNat, conicLocalVariable]
  rw [← hcast] at he
  have hc := congrArg (fun F : (ZMod p)⸨X⸩ => F.coeff 0) he
  rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_zero] at hc
  exact hunit hc

theorem conicInfinitySeries_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((conicInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) ≠ 0 := by
  rw [conicInfinitySeries_laurent p hp]
  exact div_ne_zero (pow_ne_zero _ (conicLocalVariable_ne_zero p))
    (conic_infinity_denominator_ne_zero p hp)

/-- The actual substitution is exactly s=1/T(1/v), retaining the entire cubic denominator. -/
theorem conicInfinitySeries_inverse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (((conicInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩))⁻¹ =
      cubic (conicLocalVariable p)⁻¹ := by
  rw [conicInfinitySeries_laurent p hp]
  unfold cubic
  field_simp [conicLocalVariable_ne_zero p, conic_infinity_denominator_ne_zero p hp]

/-- Exact derivative of the complete s(v); no finite truncation is used. -/
theorem conicInfinitySeries_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.derivative (ZMod p) (conicInfinitySeries p) =
      3 * PowerSeries.X ^ 2 * (4 - PowerSeries.X ^ 2) *
        (4 - 3 * PowerSeries.X ^ 2)⁻¹ ^ 2 := by
  have hi := PowerSeries.inv_mul_cancel
    (4 - 3 * PowerSeries.X ^ 2 : (ZMod p)⟦X⟧)
    (conic_infinity_denominator_unit p hp)
  have derivativeFour := (PowerSeries.derivative (ZMod p)).map_natCast 4
  change PowerSeries.derivative (ZMod p) (4 : (ZMod p)⟦X⟧) = 0 at derivativeFour
  have derivativeThree := (PowerSeries.derivative (ZMod p)).map_natCast 3
  change PowerSeries.derivative (ZMod p) (3 : (ZMod p)⟦X⟧) = 0 at derivativeThree
  simp [conicInfinitySeries, derivativeFour, derivativeThree]
  linear_combination -3 * PowerSeries.X ^ 2 * (4 - 3 * PowerSeries.X ^ 2)⁻¹ * hi

set_option maxHeartbeats 1000000 in
/-- ds/dv=-s^2 (dT/du) (du/dv), with both literal negative signs. -/
theorem conicInfinitySeries_signed_jacobian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((PowerSeries.derivative (ZMod p) (conicInfinitySeries p) :
        (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      -((conicInfinitySeries p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) ^ 2 *
        (3 * (4 * ((conicLocalVariable p)⁻¹) ^ 2 - 1)) *
        (-((conicLocalVariable p)⁻¹) ^ 2) := by
  rw [conicInfinitySeries_derivative p hp, conicInfinitySeries_laurent p hp]
  simp only [PowerSeries.coe_mul, PowerSeries.coe_sub, PowerSeries.coe_pow,
    map_ofNat,
    powerSeries_inverse_cast _ (conic_infinity_denominator_unit p hp)]
  change 3 * conicLocalVariable p ^ 2 * (4 - conicLocalVariable p ^ 2) *
    (4 - 3 * conicLocalVariable p ^ 2)⁻¹ ^ 2 = _
  field_simp [conicLocalVariable_ne_zero p, conic_infinity_denominator_ne_zero p hp]

end WPFirstResidue.ConicRankDensity
