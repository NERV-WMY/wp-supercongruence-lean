import WPMomentPrecision.QuadraticCoverSeries
import Mathlib.RingTheory.PowerSeries.Trunc

open scoped BigOperators PowerSeries LaurentSeries RatFunc
open WPMomentPrecision.QuadraticResidueTransport WPMomentPrecision.QuadraticCoverSeries

namespace WPMomentPrecision.QuadraticLaurentPullback

variable {K : Type*} [Field K]

noncomputable def seriesSubstitution : K⟦X⟧ →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (PowerSeries.substAlgHom (coverSeries_hasSubst :
      PowerSeries.HasSubst (coverSeries : K⟦X⟧))).toRingHom

theorem seriesSubstitution_X : seriesSubstitution (PowerSeries.X : K⟦X⟧) =
    coverX (localX : K⸨X⸩) := by
  change ((PowerSeries.substAlgHom (coverSeries_hasSubst :
    PowerSeries.HasSubst (coverSeries : K⟦X⟧))
      (PowerSeries.X : K⟦X⟧) : K⟦X⟧) : K⸨X⸩) = _
  rw [PowerSeries.substAlgHom_X, coverSeries_cast]

theorem coverX_ne_zero (h4 : (4 : K) ≠ 0) : coverX (localX : K⸨X⸩) ≠ 0 := by
  have h4L : (4 : K⸨X⸩) ≠ 0 := by
    have hc : (HahnSeries.C (4 : K) : K⸨X⸩) = 4 := map_ofNat _ 4
    rw [← hc]
    exact HahnSeries.C_ne_zero h4
  exact div_ne_zero (mul_ne_zero h4L (pow_ne_zero 2 localX_ne_zero))
    (pow_ne_zero 2 coverUnit_ne_zero)

theorem seriesSubstitution_units (h4 : (4 : K) ≠ 0)
    (y : Submonoid.powers (PowerSeries.X : K⟦X⟧)) :
    IsUnit (seriesSubstitution (y : K⟦X⟧)) := by
  rcases y with ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := hy
  rw [map_pow]
  apply IsUnit.pow
  rw [seriesSubstitution_X]
  exact isUnit_iff_ne_zero.mpr (coverX_ne_zero h4)

/-- Literal substitution of the complete Laurent series through the quadratic cover. -/
noncomputable def coverSubstitution (h4 : (4 : K) ≠ 0) : K⸨X⸩ →+* K⸨X⸩ :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : K⟦X⟧))
    (S := K⸨X⸩) (seriesSubstitution_units h4)

theorem coverSubstitution_powerSeries (h4 : (4 : K) ≠ 0) (f : K⟦X⟧) :
    coverSubstitution h4 (f : K⸨X⸩) = ((f.subst coverSeries : K⟦X⟧) : K⸨X⸩) := by
  have he : seriesSubstitution f = ((f.subst coverSeries : K⟦X⟧) : K⸨X⸩) := by
    change ((PowerSeries.substAlgHom (coverSeries_hasSubst :
      PowerSeries.HasSubst (coverSeries : K⟦X⟧)) f : K⟦X⟧) : K⸨X⸩) = _
    rw [PowerSeries.coe_substAlgHom]
  exact (IsLocalization.lift_eq (S := K⸨X⸩) (seriesSubstitution_units h4) f).trans he

theorem coverSubstitution_localX (h4 : (4 : K) ≠ 0) :
    coverSubstitution h4 (localX : K⸨X⸩) = coverX localX := by
  rw [show (localX : K⸨X⸩) = ((PowerSeries.X : K⟦X⟧) : K⸨X⸩) from
      PowerSeries.coe_X.symm, coverSubstitution_powerSeries,
    PowerSeries.subst_X coverSeries_hasSubst, coverSeries_cast]
  rw [PowerSeries.coe_X]
  rfl

theorem coverSubstitution_constant (h4 : (4 : K) ≠ 0) (c : K) :
    coverSubstitution h4 (HahnSeries.C c) = HahnSeries.C c := by
  rw [← PowerSeries.coe_C, coverSubstitution_powerSeries, PowerSeries.subst_C]
  congr 1

theorem coverSubstitution_single (h4 : (4 : K) ≠ 0) (j : ℤ) (c : K) :
    coverSubstitution h4 (HahnSeries.single j c) =
      HahnSeries.C c * coverX localX ^ j := by
  have he : (HahnSeries.single j c : K⸨X⸩) =
      HahnSeries.C c * localX ^ j := by
    rw [localX, ← RatFunc.single_zpow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    simp
  rw [he, map_mul, coverSubstitution_constant, map_zpow₀, coverSubstitution_localX]

theorem single_pullback_residue (h4 : (4 : K) ≠ 0) (j : ℤ) (c : K) :
    (coverSubstitution h4 (HahnSeries.single j c) * coverJacobian localX).coeff (-1) =
      2 * (HahnSeries.single j c : K⸨X⸩).coeff (-1) := by
  rw [coverSubstitution_single, mul_assoc, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, monomial_cover_residue h4]
  by_cases hj : j = -1
  · subst j
    simp [mul_comm]
  · simp [hj, HahnSeries.coeff_single_of_ne (Ne.symm hj)]

theorem regular_pullback_residue_zero (h4 : (4 : K) ≠ 0) (f : K⟦X⟧) :
    (coverSubstitution h4 (f : K⸨X⸩) * coverJacobian localX).coeff (-1) = 0 := by
  rw [coverSubstitution_powerSeries, ← jacobianSeries_cast, ← PowerSeries.coe_mul,
    PowerSeries.coeff_coe, if_pos (by norm_num)]

/-- The localization map substitutes into the original polynomial, coefficient for coefficient. -/
theorem coverSubstitution_polynomial (h4 : (4 : K) ≠ 0) (P : Polynomial K) :
    coverSubstitution h4 ((P : K⟦X⟧) : K⸨X⸩) =
      P.eval₂ HahnSeries.C (coverX localX) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.coe_add, PowerSeries.coe_add, map_add, Polynomial.eval₂_add, hP, hQ]
  | monomial n c =>
    have he : (((Polynomial.monomial n c : Polynomial K) : K⟦X⟧) : K⸨X⸩) =
        HahnSeries.C c * localX ^ n := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow,
        Polynomial.coe_C, Polynomial.coe_X, PowerSeries.coe_mul, PowerSeries.coe_pow,
        PowerSeries.coe_C, PowerSeries.coe_X]
      rfl
    rw [he, map_mul, map_pow, coverSubstitution_constant,
      coverSubstitution_localX, Polynomial.eval₂_monomial]

/-- Actual rational numerator and denominator transport, with no assumed residue equality. -/
theorem coverSubstitution_rational (h4 : (4 : K) ≠ 0) (P D : Polynomial K) :
    coverSubstitution h4 (algebraMap (RatFunc K) K⸨X⸩
      (algebraMap (Polynomial K) (RatFunc K) P /
        algebraMap (Polynomial K) (RatFunc K) D)) =
      P.eval₂ HahnSeries.C (coverX localX) / D.eval₂ HahnSeries.C (coverX localX) := by
  have hP : algebraMap (RatFunc K) K⸨X⸩
      (algebraMap (Polynomial K) (RatFunc K) P) = ((P : K⟦X⟧) : K⸨X⸩) := by
    simpa only [RatFunc.coePolynomial] using (RatFunc.coe_coe P).symm
  have hD : algebraMap (RatFunc K) K⸨X⸩
      (algebraMap (Polynomial K) (RatFunc K) D) = ((D : K⟦X⟧) : K⸨X⸩) := by
    simpa only [RatFunc.coePolynomial] using (RatFunc.coe_coe D).symm
  rw [map_div₀, hP, hD, map_div₀,
    coverSubstitution_polynomial, coverSubstitution_polynomial]

noncomputable def principalPart (f : K⸨X⸩) : K⸨X⸩ :=
  ∑ n ∈ Finset.range (-f.order).toNat,
    HahnSeries.single (-((n + 1 : ℕ) : ℤ)) (f.coeff (-((n + 1 : ℕ) : ℤ)))

noncomputable def regularPart (f : K⸨X⸩) : K⟦X⟧ :=
  PowerSeries.mk (fun n => f.coeff (n : ℤ))

theorem principalPart_nonnegative (f : K⸨X⸩) (n : ℕ) :
    (principalPart f).coeff (n : ℤ) = 0 := by
  classical
  simp only [principalPart, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact HahnSeries.coeff_single_of_ne (by omega)

theorem principalPart_negative (f : K⸨X⸩) (n : ℕ) :
    (principalPart f).coeff (Int.negSucc n) =
      if n < (-f.order).toNat then f.coeff (Int.negSucc n) else 0 := by
  classical
  simp only [principalPart, HahnSeries.coeff_sum]
  by_cases hn : n < (-f.order).toNat
  · rw [if_pos hn, Finset.sum_eq_single n]
    · rw [show -((n + 1 : ℕ) : ℤ) = Int.negSucc n by omega,
        HahnSeries.coeff_single_same]
    · intro b _ hb
      exact HahnSeries.coeff_single_of_ne (by omega)
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hb' := Finset.mem_range.mp hb
    exact HahnSeries.coeff_single_of_ne (by omega)

/-- Exact principal and regular decomposition; neither coefficient band is discarded. -/
theorem series_decomposition (f : K⸨X⸩) :
    f = principalPart f + ((regularPart f : K⟦X⟧) : K⸨X⸩) := by
  ext j
  rw [HahnSeries.coeff_add, PowerSeries.coeff_coe]
  cases j with
  | ofNat n =>
    change f.coeff (n : ℤ) = (principalPart f).coeff (n : ℤ) +
      if (n : ℤ) < 0 then 0 else PowerSeries.coeff (Int.natAbs (n : ℤ)) (regularPart f)
    rw [principalPart_nonnegative, if_neg (by omega), Int.natAbs_natCast,
      regularPart, PowerSeries.coeff_mk, zero_add]
  | negSucc n =>
    rw [if_pos (by omega), add_zero, principalPart_negative]
    by_cases hn : n < (-f.order).toNat
    · rw [if_pos hn]
    · rw [if_neg hn]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      omega

/-- Complete tame residue transport for every Laurent series and either conic branch. -/
theorem complete_quadratic_residue_transport (h4 : (4 : K) ≠ 0) (f : K⸨X⸩) :
    (coverSubstitution h4 f * coverJacobian localX).coeff (-1) = 2 * f.coeff (-1) := by
  classical
  have hdecomp := series_decomposition f
  have hr : (principalPart f).coeff (-1) = f.coeff (-1) := by
    have he := congrArg (fun g : K⸨X⸩ => g.coeff (-1)) hdecomp
    rw [HahnSeries.coeff_add, PowerSeries.coeff_coe, if_pos (by norm_num), add_zero] at he
    exact he.symm
  conv_lhs => rw [hdecomp]
  rw [map_add, add_mul, HahnSeries.coeff_add,
    regular_pullback_residue_zero, add_zero]
  rw [principalPart, map_sum, Finset.sum_mul, HahnSeries.coeff_sum]
  simp only [single_pullback_residue h4]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [principalPart, HahnSeries.coeff_sum] using hr

end WPMomentPrecision.QuadraticLaurentPullback
