import WPResidueQuotient.RationalSpecialization

/-!
Finite coordinates descend through the proved actual specialization kernel.
The source equivalence is input data to this transport construction; the
ActualSpecialization wrappers instantiate it with the proved actual residue
coordinates. Injectivity at the constant parameter is established anew from
the scalar kernel, rather than inferred from generic independence alone.
-/

namespace WPResidueQuotient.Specialization

noncomputable section

open Parameter

variable (K : Type*) [Field K] [CharZero K]
variable (c : K) (hc : Polynomial.eval c (denominatorPolynomial K) ≠ 0)
variable (n : ℕ)

variable (e : (Fin n → ParameterRing K) ≃ₗ[ParameterRing K]
  ClosedResidueQuotient (Parameter.u : ParameterRing K))
variable (f : (Fin n → K) →ₗ[K]
  ClosedResidueQuotient (fieldSpecialization K c hc (Parameter.u : ParameterRing K)))
variable (hcomm : ∀ a : Fin n → ParameterRing K,
  quotientMap (fieldSpecialization K c hc) Parameter.u (e a) =
    f (fun i => fieldSpecialization K c hc (a i)))

include hcomm in
theorem fieldSpecializedSection_injective : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).1
  apply le_antisymm
  · intro a ha
    change f a = 0 at ha
    have hlift : ∀ i : Fin n, ∃ r : ParameterRing K,
        fieldSpecialization K c hc r = a i :=
      fun i => fieldSpecialization_surjective K c hc (a i)
    choose b hb using hlift
    have hz : quotientMap (fieldSpecialization K c hc) Parameter.u (e b) = 0 := by
      rw [hcomm]
      simpa only [hb] using ha
    obtain ⟨q, hq⟩ := (quotientMap_eq_zero_iff (fieldSpecialization K c hc)
      (fieldFiberParameter K c) (fieldSpecialization_eq_zero_iff K c hc)
      (fieldSpecialization_surjective K c hc) Parameter.u (e b)).1 hz
    have he := congrArg e.symm hq
    rw [e.symm_apply_apply, map_smul] at he
    change a = 0
    ext i
    have hi := congrArg (fun z : Fin n → ParameterRing K =>
      fieldSpecialization K c hc (z i)) he
    simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, map_mul, fieldFiberParameter_specializes,
      zero_mul, hb] using hi
  · exact bot_le

omit [CharZero K] in
include hcomm in
theorem fieldSpecializedSection_surjective : Function.Surjective f := by
  intro q
  obtain ⟨r, hr⟩ := quotientMap_surjective (fieldSpecialization K c hc)
    (fieldSpecialization_surjective K c hc) Parameter.u q
  refine ⟨fun i => fieldSpecialization K c hc (e.symm r i), ?_⟩
  rw [← hcomm, e.apply_symm_apply, hr]

include hcomm in
/-- Coordinates on the literal actual constant family, with injectivity proved through its kernel. -/
def fieldSpecializedSectionEquiv : (Fin n → K) ≃ₗ[K]
    ClosedResidueQuotient (fieldSpecialization K c hc (Parameter.u : ParameterRing K)) :=
  LinearEquiv.ofBijective f
    ⟨fieldSpecializedSection_injective K c hc n e f hcomm,
      fieldSpecializedSection_surjective K c hc n e f hcomm⟩

@[simp] theorem fieldSpecializedSectionEquiv_apply (a : Fin n → K) :
    fieldSpecializedSectionEquiv K c hc n e f hcomm a = f a := rfl

end

end WPResidueQuotient.Specialization
