import WPResidueQuotient.ActualSpecialization

/-!
The actual constant-family quotient equivalences construct coordinates on
the actual closed modules and split off their actual logarithmic images.
The integral wrapper uses the proved good-prime constant quotient, including
its independence through the actual p-adic field map.
-/

namespace WPResidueQuotient.ActualSpecialization

noncomputable section

section Coordinates

variable {R : Type*} [CommRing R] (u : R)
variable (e : (Fin 11 → R) ≃ₗ[R] ClosedResidueQuotient u)
variable (he : ∀ a : Fin 11 → R, e a = Actual.elevenQuotientSection u a)

def quotientCoordinates : FClosed u →ₗ[R] (Fin 11 → R) :=
  e.symm.toLinearMap.comp (exactSubmodule u).mkQ

include he in
theorem quotientCoordinates_section (a : Fin 11 → R) :
    quotientCoordinates u e (Actual.elevenSection u a) = a := by
  change e.symm (Actual.elevenQuotientSection u a) = a
  rw [← he]
  exact e.symm_apply_apply a

include he in
theorem quotientCoordinates_element (i : Fin 11) :
    quotientCoordinates u e (Actual.elevenClosedElement u i) = Pi.single i 1 := by
  rw [← Actual.elevenSection_single]
  exact quotientCoordinates_section u e he (Pi.single i 1)

theorem quotientCoordinates_ker : (quotientCoordinates u e).ker = exactSubmodule u := by
  ext g
  change e.symm ((exactSubmodule u).mkQ g) = 0 ↔ g ∈ exactSubmodule u
  constructor
  · intro h
    have hx : (exactSubmodule u).mkQ g = 0 := by
      have hx := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hx
    exact (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).1 hx
  · intro h
    have hz : (exactSubmodule u).mkQ g = 0 :=
      (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).2 h
    rw [hz, map_zero]

theorem quotientCoordinates_exact (g : exactSubmodule u) :
    quotientCoordinates u e (g : FClosed u) = 0 := by
  change e.symm ((exactSubmodule u).mkQ g) = 0
  have hz : (exactSubmodule u).mkQ (g : FClosed u) = 0 :=
    (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).2 g.property
  rw [hz, map_zero]

include he in
theorem quotientCoordinates_residual_exact (g : FClosed u) :
    g - Actual.elevenSection u (quotientCoordinates u e g) ∈ exactSubmodule u := by
  rw [← quotientCoordinates_ker u e]
  change quotientCoordinates u e (g - Actual.elevenSection u (quotientCoordinates u e g)) = 0
  rw [map_sub, quotientCoordinates_section u e he, sub_self]

include he in
def quotientExactProjection : FClosed u →ₗ[R] exactSubmodule u :=
  (LinearMap.id - (Actual.elevenSection u).comp (quotientCoordinates u e)).codRestrict
    (exactSubmodule u) (quotientCoordinates_residual_exact u e he)

include he in
def closedSplitFromQuotient : FClosed u ≃ₗ[R] ((exactSubmodule u) × (Fin 11 → R)) where
  toLinearMap := (quotientExactProjection u e he).prod (quotientCoordinates u e)
  invFun x := (x.1 : FClosed u) + Actual.elevenSection u x.2
  left_inv g := by
    change (g - Actual.elevenSection u (quotientCoordinates u e g)) +
      Actual.elevenSection u (quotientCoordinates u e g) = g
    exact sub_add_cancel _ _
  right_inv x := by
    rcases x with ⟨g, a⟩
    apply Prod.ext
    · apply Subtype.ext
      change ((g : FClosed u) + Actual.elevenSection u a) -
        Actual.elevenSection u (quotientCoordinates u e
          ((g : FClosed u) + Actual.elevenSection u a)) = (g : FClosed u)
      rw [map_add, quotientCoordinates_exact, quotientCoordinates_section u e he,
        zero_add, add_sub_cancel_right]
    · change quotientCoordinates u e ((g : FClosed u) + Actual.elevenSection u a) = a
      rw [map_add, quotientCoordinates_exact, quotientCoordinates_section u e he, zero_add]

@[simp] theorem closedSplitFromQuotient_symm_apply
    (g : exactSubmodule u) (a : Fin 11 → R) :
    (closedSplitFromQuotient u e he).symm (g, a) =
      (g : FClosed u) + Actual.elevenSection u a := rfl

end Coordinates

section Interior

variable {R : Type*} [CommRing R] [IsDomain R] (u v : R)
variable (huv : v * (6 * u) = 1)
variable (e : (Fin 11 → R) ≃ₗ[R] ClosedResidueQuotient u)
variable (he : ∀ a : Fin 11 → R, e a = Actual.elevenQuotientSection u a)

include huv he in
theorem quotientCoordinates_interior_boundary_zero
    (g : FClosed u) (hg : g ∈ Actual.interiorInClosed u) (j : Fin 6) :
    quotientCoordinates u e g (Fin.natAdd 5 j) = 0 := by
  let hu' := Actual.uUnitOfInverse u v huv
  have hz : vertexCoordinateMap u hu' g = 0 :=
    vertexCoordinateMap_interior_zero u hu' g hg
  have hx := exactSubmodule_le_vertexCoordinateMap_ker u hu'
    (quotientCoordinates_residual_exact u e he g)
  change vertexCoordinateMap u hu'
    (g - Actual.elevenSection u (quotientCoordinates u e g)) = 0 at hx
  rw [map_sub, hz, zero_sub] at hx
  have hs := congrFun (neg_eq_zero.mp hx) j
  rw [Actual.vertexCoordinateMap_section u v huv
    (quotientCoordinates u e g) j, Pi.zero_apply] at hs
  exact (mul_eq_zero.mp hs).resolve_left (neg_ne_zero.mpr (Units.ne_zero hu'.unit⁻¹))

include huv he in
theorem quotientCoordinates_interior_image :
    (Actual.interiorInClosed u).map (quotientCoordinates u e) = Actual.interiorCoordinates R := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact quotientCoordinates_interior_boundary_zero u v huv e he g hg
  · intro ha
    refine ⟨Actual.elevenSection u a, Actual.elevenSection_interior_of_boundary_zero u a ha, ?_⟩
    exact quotientCoordinates_section u e he a

end Interior

variable (K : Type*) [Field K] [CharZero K]

def tenthClosedCoordinates : FClosed (1 / 10 : K) →ₗ[K] (Fin 11 → K) :=
  quotientCoordinates (1 / 10) (tenthQuotientEquiv K)

theorem tenthClosedCoordinates_ker : (tenthClosedCoordinates K).ker = exactSubmodule (1 / 10 : K) :=
  quotientCoordinates_ker (1 / 10) (tenthQuotientEquiv K)

theorem tenthClosedCoordinates_gamma (i : Fin 5) :
    tenthClosedCoordinates K (Actual.gammaClosedElement (1 / 10 : K) i) =
      Pi.single (Fin.castAdd 6 i) 1 := by
  rw [← Actual.elevenClosedElement_left]
  exact quotientCoordinates_element (1 / 10) (tenthQuotientEquiv K)
    (tenthQuotientEquiv_apply K) (Fin.castAdd 6 i)

theorem tenthClosedCoordinates_boundary (i : Fin 6) :
    tenthClosedCoordinates K (vertexBoundaryElement (1 / 10 : K) i) =
      Pi.single (Fin.natAdd 5 i) 1 := by
  rw [← Actual.elevenClosedElement_right]
  exact quotientCoordinates_element (1 / 10) (tenthQuotientEquiv K)
    (tenthQuotientEquiv_apply K) (Fin.natAdd 5 i)

def tenthClosedSplitEquiv : FClosed (1 / 10 : K) ≃ₗ[K]
    ((exactSubmodule (1 / 10 : K)) × (Fin 11 → K)) :=
  closedSplitFromQuotient (1 / 10) (tenthQuotientEquiv K) (tenthQuotientEquiv_apply K)

theorem tenthClosedCoordinates_interior_image :
    (Actual.interiorInClosed (1 / 10 : K)).map (tenthClosedCoordinates K) =
      Actual.interiorCoordinates K :=
  quotientCoordinates_interior_image (1 / 10 : K) (5 / 3) (by norm_num)
    (tenthQuotientEquiv K) (tenthQuotientEquiv_apply K)

section Padic

variable (p : ℕ) [Fact p.Prime]

def integralConstantCoordinates (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    FClosed (Parameter.integralTenth p hp) →ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  quotientCoordinates (Parameter.integralTenth p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)

theorem integralConstantCoordinates_ker
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    (integralConstantCoordinates p hp hp7 hp19).ker = exactSubmodule (Parameter.integralTenth p hp) :=
  quotientCoordinates_ker (Parameter.integralTenth p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)

theorem integralConstantCoordinates_gamma
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) (i : Fin 5) :
    integralConstantCoordinates p hp hp7 hp19
        (Actual.gammaClosedElement (Parameter.integralTenth p hp) i) =
      Pi.single (Fin.castAdd 6 i) 1 := by
  rw [← Actual.elevenClosedElement_left]
  exact quotientCoordinates_element (Parameter.integralTenth p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)
    (integralConstantQuotientEquiv_apply p hp hp7 hp19) (Fin.castAdd 6 i)

theorem integralConstantCoordinates_boundary
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) (i : Fin 6) :
    integralConstantCoordinates p hp hp7 hp19
        (vertexBoundaryElement (Parameter.integralTenth p hp) i) =
      Pi.single (Fin.natAdd 5 i) 1 := by
  rw [← Actual.elevenClosedElement_right]
  exact quotientCoordinates_element (Parameter.integralTenth p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)
    (integralConstantQuotientEquiv_apply p hp hp7 hp19) (Fin.natAdd 5 i)

def integralConstantClosedSplitEquiv
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    FClosed (Parameter.integralTenth p hp) ≃ₗ[ℤ_[p]]
      ((exactSubmodule (Parameter.integralTenth p hp)) × (Fin 11 → ℤ_[p])) :=
  closedSplitFromQuotient (Parameter.integralTenth p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)
    (integralConstantQuotientEquiv_apply p hp hp7 hp19)

theorem integralConstantCoordinates_interior_image
    (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    (Actual.interiorInClosed (Parameter.integralTenth p hp)).map
        (integralConstantCoordinates p hp hp7 hp19) = Actual.interiorCoordinates ℤ_[p] :=
  quotientCoordinates_interior_image (Parameter.integralTenth p hp)
    (integralConstantInverseSix p hp) (integralConstantInverseSix_identity p hp)
    (integralConstantQuotientEquiv p hp hp7 hp19)
    (integralConstantQuotientEquiv_apply p hp hp7 hp19)

end Padic

end

end WPResidueQuotient.ActualSpecialization
