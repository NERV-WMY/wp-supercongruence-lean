import WPResidueFrobenius.Completed
import WPResidueFrobenius.Generators

noncomputable section

set_option maxHeartbeats 2000000

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

theorem elevenRawMatrix_gamma (i : Fin 11) (j : Fin 5) :
    elevenRawMatrix p hp hp7 hp19 i (Fin.castAdd 6 j) = gammaRawMatrix p hp hp7 hp19 i j := by
  apply PadicInt.ext
  simp only [elevenRawMatrix, elevenRawColumn, Fin.addCases_left, gammaRawMatrix]

theorem coordinatePhi_preserves_interior (v : Fin 11 → ℤ_[p])
    (hv : v ∈ Actual.interiorCoordinates ℤ_[p]) :
    coordinatePhi p hp hp7 hp19 v ∈ Actual.interiorCoordinates ℤ_[p] := by
  intro b
  have hv' : ∀ j : Fin 6, v (Fin.natAdd 5 j) = 0 := hv
  rw [coordinatePhi_apply, Fin.sum_univ_add (a := 5) (b := 6)]
  simp only [elevenRawMatrix_gamma, gammaRawMatrix_boundary_zero, zero_mul,
    hv', mul_zero, Finset.sum_const_zero, add_zero]

def gammaRawInteriorMatrix : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  fun i j => gammaRawMatrix p hp hp7 hp19 (Fin.castAdd 6 i) j

def interiorPhi : (Fin 5 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 5 → ℤ_[p]) :=
  Matrix.toLin' (gammaRawInteriorMatrix p hp hp7 hp19)

theorem interiorPhi_apply (v : Fin 5 → ℤ_[p]) (i : Fin 5) :
    interiorPhi p hp hp7 hp19 v i = ∑ j, gammaRawInteriorMatrix p hp hp7 hp19 i j * v j := rfl

theorem inclusion_left (v : Fin 5 → ℤ_[p]) (j : Fin 5) :
    ActualCompletion.moduleInteriorInclusion v (Fin.castAdd 6 j) = v j := by
  change (if h : j.val < 5 then v ⟨j.val,h⟩ else 0) = v j
  rw [dif_pos j.isLt]

theorem inclusion_right (v : Fin 5 → ℤ_[p]) (j : Fin 6) :
    ActualCompletion.moduleInteriorInclusion v (Fin.natAdd 5 j) = 0 := by
  change (if h : 5+j.val < 5 then v ⟨5+j.val,h⟩ else 0) = 0
  rw [dif_neg (by omega)]

theorem coordinatePhi_interior (v : Fin 5 → ℤ_[p]) :
    coordinatePhi p hp hp7 hp19 (ActualCompletion.moduleInteriorInclusion v) =
      ActualCompletion.moduleInteriorInclusion (interiorPhi p hp hp7 hp19 v) := by
  funext i
  refine Fin.addCases (m := 5) (n := 6) (fun i => ?_) (fun i => ?_) i
  · rw [coordinatePhi_apply, Fin.sum_univ_add (a := 5) (b := 6), inclusion_left,
      interiorPhi_apply]
    simp only [inclusion_left, inclusion_right, mul_zero, Finset.sum_const_zero, add_zero,
      elevenRawMatrix_gamma, gammaRawInteriorMatrix]
  · rw [inclusion_right]
    exact coordinatePhi_preserves_interior p hp hp7 hp19 _ (inclusion_right p v) i

def completedInteriorImage : Submodule ℤ_[p] (CompletedClosedQuotient p hp) :=
  LinearMap.range ((LinearMap.range (ActualCompletion.constantCompletedExactInclusion p hp)).mkQ.comp
    (ActualCompletion.completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p])))

theorem completedInteriorImage_eq : completedInteriorImage p hp =
    (Actual.interiorCoordinates ℤ_[p]).comap (completedCoordinates p hp hp7 hp19) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    change completedCoordinates p hp hp7 hp19 (Submodule.Quotient.mk
      (ActualCompletion.completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) x)) ∈
        Actual.interiorCoordinates ℤ_[p]
    rw [completedCoordinates_mk, ← ActualCompletion.constantInteriorZp_image p hp hp7 hp19]
    exact ⟨_, LinearMap.mem_range_self _ x, rfl⟩
  · intro hg
    change completedCoordinates p hp hp7 hp19 g ∈ Actual.interiorCoordinates ℤ_[p] at hg
    rw [← ActualCompletion.constantInteriorZp_image p hp hp7 hp19] at hg
    obtain ⟨x, ⟨y, rfl⟩, hxy⟩ := hg
    refine ⟨y, ?_⟩
    apply (ActualCompletion.constantQuotientZpEquiv p hp hp7 hp19).injective
    change completedCoordinates p hp hp7 hp19 (Submodule.Quotient.mk
      (ActualCompletion.completedInteriorInclusion (Parameter.integralTenth p hp) (p : ℤ_[p]) y)) = _
    rw [completedCoordinates_mk]
    exact hxy

theorem PhiU_preserves_actual_interior (g : CompletedClosedQuotient p hp)
    (hg : g ∈ completedInteriorImage p hp) : PhiU p hp hp7 hp19 g ∈ completedInteriorImage p hp := by
  rw [completedInteriorImage_eq p hp hp7 hp19] at hg ⊢
  change completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19 g) ∈ Actual.interiorCoordinates ℤ_[p]
  rw [PhiU_coordinates]
  exact coordinatePhi_preserves_interior p hp hp7 hp19 _ hg

def PhiUInterior : completedInteriorImage p hp →ₗ[ℤ_[p]] completedInteriorImage p hp :=
  ((PhiU p hp hp7 hp19).comp (completedInteriorImage p hp).subtype).codRestrict
    (completedInteriorImage p hp) fun g => PhiU_preserves_actual_interior p hp hp7 hp19 g g.property

theorem continuous_PhiUInterior : Continuous (PhiUInterior p hp hp7 hp19) := by
  apply Continuous.subtype_mk
  exact (continuous_PhiU p hp hp7 hp19).comp continuous_subtype_val

theorem PhiUInterior_coordinates (g : completedInteriorImage p hp) :
    ActualCompletion.moduleInteriorProjection
      (completedCoordinates p hp hp7 hp19 (PhiUInterior p hp hp7 hp19 g)) =
        interiorPhi p hp hp7 hp19 (ActualCompletion.moduleInteriorProjection
          (completedCoordinates p hp hp7 hp19 g)) := by
  have hg : completedCoordinates p hp hp7 hp19 g ∈ Actual.interiorCoordinates ℤ_[p] := by
    exact (le_of_eq (completedInteriorImage_eq p hp hp7 hp19)) g.property
  rw [← ActualCompletion.moduleInteriorInclusion_range] at hg
  obtain ⟨v, hv⟩ := hg
  change ActualCompletion.moduleInteriorProjection
    (completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19 g)) = _
  rw [PhiU_coordinates, ← hv, coordinatePhi_interior]
  have hleft (w : Fin 5 → ℤ_[p]) : ActualCompletion.moduleInteriorProjection
      (ActualCompletion.moduleInteriorInclusion w) = w :=
    DFunLike.congr_fun ActualCompletion.moduleInteriorProjection_leftInverse w
  rw [hleft, hleft]

theorem PhiU_gamma_column (j : Fin 5) :
    completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19
      (moduleClass p hp (Actual.gammaClosedElement (Parameter.integralTenth p hp) j))) =
        fun i => gammaRawMatrix p hp hp7 hp19 i j := by
  have h := PhiU_moduleClass_raw p hp hp7 hp19 (Actual.gammaClosedElement (Parameter.integralTenth p hp) j)
  rw [presentedPullback_gamma p hp hp7 hp19] at h
  funext i
  apply PadicInt.ext
  exact (congrFun h i).symm

theorem PhiU_gamma_T128_mod_p8 (i : Fin 11) (j : Fin 5) :
    ∃ z : ℤ_[p], completedCoordinates p hp hp7 hp19 (PhiU p hp hp7 hp19
      (moduleClass p hp (Actual.gammaClosedElement (Parameter.integralTenth p hp) j))) i -
        gammaT128Matrix p hp hp7 hp19 i j = (p : ℤ_[p])^8*z := by
  rw [PhiU_gamma_column]
  exact gammaT128Matrix_mod_p8 p hp hp7 hp19 i j

theorem PhiU_factorial_generator_raw (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n+1) :
    (fun i => IntegralTransport.padicCoefficientMap p (completedCoordinates p hp hp7 hp19
      (PhiU p hp hp7 hp19 (moduleClass p hp (integralGenerator p hp a n ha))) i)) =
        rawPullbackCoordinates p hp (n+1) (by omega)
          (laurentMonomial (fun i => (a i : ℤ))) (monomial_supported p a (n+1) ha) := by
  rw [← PhiU_moduleClass_raw, presentedPullback_generator p hp hp7 hp19]

end WPResidueFrobenius
