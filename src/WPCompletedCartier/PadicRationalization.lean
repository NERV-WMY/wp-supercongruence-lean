import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

namespace WPCompletedCartier.PadicRationalization

noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev ScalarLocalization := Localization (Submonoid.powers (p : ℤ_[p]))

/-- The existing actual fraction-field theorem and the actual unit-times-p-power
decomposition of a nonzero p-adic integer give a bounded p-power denominator.
No field isomorphism is assumed in obtaining this identity. -/
theorem bounded_power_denominator (x : ℚ_[p]) :
    ∃ n : ℕ, ∃ a : ℤ_[p], x * (p : ℚ_[p]) ^ n = (a : ℚ_[p]) := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  let v := PadicInt.unitCoeff hb0
  have hv0 : ((v : ℤ_[p]) : ℚ_[p]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr (Units.ne_zero v)
  have hbcast : (b : ℚ_[p]) = ((v : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ b.valuation := by
    have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (PadicInt.unitCoeff_spec hb0)
    simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using h
  have hv : (((↑v⁻¹ : ℤ_[p]) : ℚ_[p])) * ((v : ℤ_[p]) : ℚ_[p]) = 1 := by
    have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) (Units.inv_mul v)
    simpa only [PadicInt.coe_mul, PadicInt.coe_one] using h
  refine ⟨b.valuation, (↑v⁻¹ : ℤ_[p]) * a, ?_⟩
  rw [← hx]
  change ((a : ℚ_[p]) / (b : ℚ_[p])) * (p : ℚ_[p]) ^ b.valuation = _
  apply mul_right_cancel₀ hv0
  calc
    _ = ((a : ℚ_[p]) / (b : ℚ_[p])) *
        (((v : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ b.valuation) := by ring
    _ = ((a : ℚ_[p]) / (b : ℚ_[p])) * (b : ℚ_[p]) := by rw [← hbcast]
    _ = (a : ℚ_[p]) := div_mul_cancel₀ _ (PadicInt.coe_ne_zero.mpr hb0)
    _ = (((↑v⁻¹ : ℤ_[p]) * a : ℤ_[p]) : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p]) := by
      rw [PadicInt.coe_mul]
      calc
        _ = ((((↑v⁻¹ : ℤ_[p]) : ℚ_[p])) * ((v : ℤ_[p]) : ℚ_[p])) * (a : ℚ_[p]) := by
          rw [hv, one_mul]
        _ = _ := by ring

theorem exists_integral_power_multiple (x : ℚ_[p]) :
    ∃ n : ℕ, ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
  obtain ⟨n, a, ha⟩ := bounded_power_denominator p x
  refine ⟨n, ?_⟩
  rw [mul_comm, ha]
  exact a.property

/-- Qp is the actual localization of Zp at powers of its prime. -/
instance qpIsLocalization : IsLocalization (Submonoid.powers (p : ℤ_[p])) ℚ_[p] :=
  IsLocalization.Away.mk (p : ℤ_[p])
    (by
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_natCast] using
        (show (p : ℚ_[p]) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero))
    (by
      intro x
      simpa only [map_natCast, PadicInt.algebraMap_apply] using bounded_power_denominator p x)
    (by
      intro a b hab
      refine ⟨0, ?_⟩
      have h : a = b := PadicInt.ext hab
      simpa only [pow_zero, one_mul] using h)

/-- The scalar identification used to turn the constructed localized Cartier
map into an operator over the literal p-adic field. -/
def padicLocalizationEquiv : ScalarLocalization p ≃ₐ[ℤ_[p]] ℚ_[p] :=
  IsLocalization.algEquiv (Submonoid.powers (p : ℤ_[p])) (ScalarLocalization p) ℚ_[p]

def padicLocalizationRingEquiv : ScalarLocalization p ≃+* ℚ_[p] :=
  (padicLocalizationEquiv p).toRingEquiv

@[simp] theorem padicLocalizationEquiv_algebraMap (a : ℤ_[p]) :
    padicLocalizationEquiv p (algebraMap ℤ_[p] (ScalarLocalization p) a) = (a : ℚ_[p]) :=
  (padicLocalizationEquiv p).commutes a

@[simp] theorem padicLocalizationEquiv_symm_coe (a : ℤ_[p]) :
    (padicLocalizationEquiv p).symm (a : ℚ_[p]) =
      algebraMap ℤ_[p] (ScalarLocalization p) a := by
  rw [← padicLocalizationEquiv_algebraMap p a, AlgEquiv.symm_apply_apply]

def powerDenominator (n : ℕ) : Submonoid.powers (p : ℤ_[p]) := ⟨(p : ℤ_[p]) ^ n, n, rfl⟩

theorem padicLocalizationEquiv_fraction (a : ℤ_[p]) (n : ℕ) :
    padicLocalizationEquiv p
        (IsLocalization.mk' (ScalarLocalization p) a (powerDenominator p n)) =
      (a : ℚ_[p]) / (p : ℚ_[p]) ^ n := by
  have hmap : Eq (α := ℚ_[p])
      (padicLocalizationEquiv p
        (IsLocalization.mk' (ScalarLocalization p) a (powerDenominator p n)))
      (IsLocalization.mk' ℚ_[p] a (powerDenominator p n)) := by
    change (IsLocalization.algEquiv (Submonoid.powers (p : ℤ_[p]))
      (ScalarLocalization p) ℚ_[p])
      (IsLocalization.mk' (ScalarLocalization p) a (powerDenominator p n)) = _
    exact IsLocalization.algEquiv_mk' (M := Submonoid.powers (p : ℤ_[p]))
      (S := ScalarLocalization p) (Q := ℚ_[p]) a (powerDenominator p n)
  have hspec : Eq (α := ℚ_[p])
      (IsLocalization.mk' ℚ_[p] a (powerDenominator p n) *
        algebraMap ℤ_[p] ℚ_[p] (powerDenominator p n : ℤ_[p]))
      (algebraMap ℤ_[p] ℚ_[p] a) :=
    IsLocalization.mk'_spec ℚ_[p] a (powerDenominator p n)
  have hproduct : Eq (α := ℚ_[p])
      (IsLocalization.mk' ℚ_[p] a (powerDenominator p n) * (p : ℚ_[p]) ^ n)
      (a : ℚ_[p]) := by
    simpa only [powerDenominator, map_pow, map_natCast, PadicInt.algebraMap_apply] using hspec
  have hfraction : Eq (α := ℚ_[p])
      (IsLocalization.mk' ℚ_[p] a (powerDenominator p n))
      ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) :=
    (eq_div_iff (pow_ne_zero n
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℚ_[p]) ≠ 0))).mpr hproduct
  exact hmap.trans hfraction

end
end WPCompletedCartier.PadicRationalization
