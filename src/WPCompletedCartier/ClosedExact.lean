import WPCompletedCartier.AdicSeries

namespace WPCompletedCartier.ClosedExact

noncomputable section
open WPResidueQuotient WPResidueQuotient.Adic
open WPResidueQuotient.ActualCompletion

section DerivativeFactor

variable {R : Type*} [CommRing R]

def derivativeIntoExact (u : R) (i : Fin 5) :
    FClosed u →ₗ[R] exactSubmodule u :=
  (DClosed u i).codRestrict (exactSubmodule u) (DClosed_mem_exact u i)

theorem derivative_factor (u : R) (i : Fin 5) :
    (exactSubmodule u).subtype.comp (derivativeIntoExact u i) = DClosed u i := by
  ext x
  rfl

theorem completed_derivative_factor (u q : R) (i : Fin 5)
    (x : Completion q (FClosed u)) :
    completeMap q (exactSubmodule u).subtype
      (completeMap (M := FClosed u) (N := exactSubmodule u) q
        (derivativeIntoExact u i) x) = completeMap q (DClosed u i) x := by
  rw [← completeMap_comp, derivative_factor]

end DerivativeFactor

section Numerical

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

local notation "u" => Parameter.integralTenth p hp
local notation "V" => Completion (p : ℤ_[p]) (FClosed u)
local notation "T" => LinearMap.range (constantCompletedExactInclusion p hp)

include hp7 hp19 in
theorem completed_exact_isClosed : IsClosed (T : Set V) := by
  rw [← constantCoordinatesZp_kernel p hp hp7 hp19]
  change IsClosed ((constantCoordinatesZp p hp hp7 hp19) ⁻¹' {0})
  exact isClosed_singleton.preimage (continuous_constantCoordinatesZp p hp hp7 hp19)

set_option maxHeartbeats 800000 in
/-- The module commutation premise is proved for the constructed Cartier elsewhere.
This theorem supplies its exact closed-range descent from that identity. -/
theorem module_exact_preserved (C : FClosed u →ₗ[ℤ_[p]] V)
    (hD : ∀ i g, C (DClosed u i g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (C g)) :
    exactSubmodule u ≤ (T).comap C := by
  change (⨆ i : Fin 5, LinearMap.range (DClosed u i)) ≤ (T).comap C
  apply iSup_le
  intro i x hx
  obtain ⟨g, rfl⟩ := hx
  change C (DClosed u i g) ∈ T
  rw [hD]
  refine ⟨(p : ℤ_[p]) • completeMap (M := FClosed u) (N := exactSubmodule u)
    (p : ℤ_[p]) (derivativeIntoExact u i) (C g), ?_⟩
  change completeMap (p : ℤ_[p]) (exactSubmodule u).subtype
    ((p : ℤ_[p]) • completeMap (M := FClosed u) (N := exactSubmodule u)
      (p : ℤ_[p]) (derivativeIntoExact u i) (C g)) = _
  rw [map_smul, completed_derivative_factor]

include hp7 hp19 in
theorem completed_exact_preserved (C : FClosed u →ₗ[ℤ_[p]] V)
    (hD : ∀ i g, C (DClosed u i g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (C g)) :
    T ≤ (T).comap (AdicSeries.extension (p : ℤ_[p]) C) := by
  intro x hx
  let S := LinearMap.range ((ofModule (p : ℤ_[p])).comp (exactSubmodule u).subtype)
  have hS : ∀ y ∈ S, AdicSeries.extension (p : ℤ_[p]) C y ∈ T := by
    rintro y ⟨g, rfl⟩
    rw [LinearMap.comp_apply, AdicSeries.extension_ofModule]
    exact module_exact_preserved p hp C hD g.property
  have hxcl : x ∈ closure (S : Set V) := by
    change x ∈ closure (Set.range ((ofModule (p : ℤ_[p])).comp (exactSubmodule u).subtype))
    rw [constant_exact_closure p hp hp7 hp19]
    exact hx
  have ho := AdicSeries.mapsTo_closure (AdicSeries.extension (p : ℤ_[p]) C)
    (AdicSeries.continuous_extension _ _) S T hS hxcl
  rw [(completed_exact_isClosed p hp hp7 hp19).closure_eq] at ho
  exact ho

include hp7 hp19 in
def quotientOperator (C : FClosed u →ₗ[ℤ_[p]] V)
    (hD : ∀ i g, C (DClosed u i g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (C g)) :
    (V ⧸ T) →ₗ[ℤ_[p]] (V ⧸ T) :=
  (T).mapQ T (AdicSeries.extension (p : ℤ_[p]) C)
    (completed_exact_preserved p hp hp7 hp19 C hD)

@[simp] theorem quotientOperator_mk (C : FClosed u →ₗ[ℤ_[p]] V)
    (hD : ∀ i g, C (DClosed u i g) =
      (p : ℤ_[p]) • completeMap (p : ℤ_[p]) (DClosed u i) (C g)) (x : V) :
    quotientOperator p hp hp7 hp19 C hD (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (AdicSeries.extension (p : ℤ_[p]) C x) := rfl

end Numerical

end

end WPCompletedCartier.ClosedExact
