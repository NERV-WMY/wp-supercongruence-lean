import WPResidueFrobenius.Laurent

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def integralGenerator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n+1) :
    FClosed (Parameter.integralTenth p hp) :=
  ⟨numeratorGenerator (Parameter.integralTenth p hp) a n,
    numeratorGenerator_mem_closed _ a n ha⟩

def integralClass (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n+1) :
    ClosedResidueQuotient (Parameter.integralTenth p hp) :=
  Submodule.Quotient.mk (integralGenerator p hp a n ha)

def specializeQuotient :=
  IntegralTransport.quotientMap (Parameter.integralSpecialization p hp hp7 hp19)
    (Parameter.u : Parameter.ParameterRing ℤ_[p]) (Parameter.integralTenth p hp)
    (Parameter.integralSpecialization_u p hp hp7 hp19)

def specializedFullVector (v : WPGammaClosedNumeratorBounds.Space p) : Fin 11 → ℤ_[p] :=
  fun i => Parameter.integralSpecialization p hp hp7 hp19
    ((Fin.append
      (v.1 - Pi.single 0 (ActualConnection.boundaryScalar ℤ_[p]
        (Parameter.padic_six_unit p hp) * ∑ j, v.2 j)) v.2) i)

theorem specialize_numerator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n+1) :
    specializeQuotient p hp hp7 hp19
      (WPReview.ResidueNumeratorOperators.qNumerator ℤ_[p] a n ha) = integralClass p hp a n ha := by
  rw [WPReview.ResidueNumeratorOperators.qNumerator, specializeQuotient,
    IntegralTransport.quotientMap_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact IntegralTransport.actualMap_numeratorGenerator _ _ _ _ a n

theorem specialize_fullSection (v : WPGammaClosedNumeratorBounds.Space p) :
    specializeQuotient p hp hp7 hp19 (WPGammaClosedNumeratorBounds.fullSection p hp v) =
      Actual.elevenQuotientSection (Parameter.integralTenth p hp)
        (specializedFullVector p hp hp7 hp19 v) := by
  rw [WPGammaClosedNumeratorBounds.fullSection, WPReview.ResidueClosedConnection.fullSection_raw]
  exact ActualSpecialization.transportedQuotientMap_elevenSection _ _ _ _ _

theorem integralGenerator_coordinates_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n+1) : ∃ w : Fin 11 → ℤ_[p],
    ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 (integralGenerator p hp a n ha) =
      (p : ℤ)^(((n/p)-5)/5) • w := by
  obtain ⟨v, hv⟩ := WPReview.ResidueClosedCanonicalBounds.actual_closed_classes_bound p hp a n ha
  have hs := congrArg (specializeQuotient p hp hp7 hp19) hv
  rw [specialize_numerator, map_zsmul, specialize_fullSection] at hs
  refine ⟨specializedFullVector p hp hp7 hp19 v, ?_⟩
  have he := congrArg (ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).symm hs
  change (ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).symm
    (integralClass p hp a n ha) = _
  rw [map_zsmul, ← ActualSpecialization.integralConstantQuotientEquiv_apply p hp hp7 hp19,
    LinearEquiv.symm_apply_apply] at he
  exact he

def fieldGenerator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n+1) :
    FClosed (1/10 : ℚ_[p]) :=
  ⟨numeratorGenerator (1/10 : ℚ_[p]) a n, numeratorGenerator_mem_closed _ a n ha⟩

def integralToField :=
  IntegralTransport.closedMap (IntegralTransport.padicCoefficientMap p)
    (Parameter.integralTenth p hp) (1/10 : ℚ_[p])
    (ParameterSpecialization.integralTenth_in_field p hp)

theorem integralToField_generator (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n+1) :
    integralToField p hp (integralGenerator p hp a n ha) = fieldGenerator p a n ha := by
  apply Subtype.ext
  exact IntegralTransport.actualMap_numeratorGenerator _ _ _ _ a n

theorem integralToField_coordinates (g : FClosed (Parameter.integralTenth p hp)) :
    ActualSpecialization.tenthClosedCoordinates ℚ_[p] (integralToField p hp g) =
      fun i => IntegralTransport.padicCoefficientMap p
        (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g i) := by
  let c := ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g
  have hs : Actual.elevenQuotientSection (Parameter.integralTenth p hp) c =
      Submodule.Quotient.mk g := by
    change (ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19)
      ((ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).symm
        (Submodule.Quotient.mk g)) = _
    exact LinearEquiv.apply_symm_apply _ _
  have he := congrArg (ActualSpecialization.integralConstantQuotientMap p hp) hs
  rw [ActualSpecialization.integralConstantQuotientMap_section] at he
  change Actual.elevenQuotientSection (1/10 : ℚ_[p])
    (fun i => IntegralTransport.padicCoefficientMap p (c i)) =
      Submodule.Quotient.mk (integralToField p hp g) at he
  have hc := congrArg (ActualSpecialization.tenthQuotientEquiv ℚ_[p]).symm he
  rw [← ActualSpecialization.tenthQuotientEquiv_apply, LinearEquiv.symm_apply_apply] at hc
  exact hc.symm

include hp hp7 hp19 in
theorem fieldGenerator_coordinates_bound (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n+1) : ∃ w : Fin 11 → ℤ_[p],
    ActualSpecialization.tenthClosedCoordinates ℚ_[p] (fieldGenerator p a n ha) =
      fun i => (p : ℚ_[p])^(((n/p)-5)/5) * IntegralTransport.padicCoefficientMap p (w i) := by
  obtain ⟨w, hw⟩ := integralGenerator_coordinates_bound p hp hp7 hp19 a n ha
  refine ⟨w, ?_⟩
  rw [← integralToField_generator p hp, integralToField_coordinates p hp hp7 hp19, hw]
  funext i
  simp [Algebra.smul_def]

end WPResidueFrobenius
