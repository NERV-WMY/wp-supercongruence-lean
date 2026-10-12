import WPResidueFrobenius.QuotientDescent
import WPResidueFrobenius.Truncation

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open WPResidueQuotient IsUltrametricDist

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def boundaryRawColumn (b : Fin 6) : Fin 11 → ℚ_[p] :=
  rawPullbackCoordinates p hp 1 (by omega) (laurentVertex b)
    (laurentVertex_mem_numeratorFiltration b)

include hp7 hp19 in
theorem boundaryRawColumn_norm (i : Fin 11) (b : Fin 6) :
    ‖boundaryRawColumn p hp b i‖ ≤ 1 := by
  rw [boundaryRawColumn, rawPullbackCoordinates,
    tsum_apply (rawPullbackTerm_coordinates_summable p hp hp7 hp19 _ _ _ _)]
  apply norm_tsum_le_of_forall_le
  intro k
  simpa using rawPullbackTerm_coordinate_precision p hp hp7 hp19 1 k 0
    (by omega) (laurentVertex b) (laurentVertex_mem_numeratorFiltration b) i
    (pullback_gain_nonnegative p 1 k (Fact.out : p.Prime) hp hp7 (by omega) (by omega))

include hp7 hp19 in
theorem presentedPullback_gamma (j : Fin 5) :
    presentedPullback p hp (Actual.gammaClosedElement (Parameter.integralTenth p hp) j) =
      gammaRawColumn p hp j := by
  have hP := (numeratorFiltration ℤ_[p] (j.val+1)).smul_mem
    (j.val.factorial : ℤ_[p]) (gammaNumerator_supported p (j.val+1))
  have he : ((Actual.gammaClosedElement (Parameter.integralTenth p hp) j : FClosed _) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) (j.val+1)
        ((j.val.factorial : ℤ_[p]) • gammaNumerator p) := by
    simp only [Actual.gammaClosedElement, gammaNumerator, poleLinearMap_apply,
      factorialPole, mul_one, Algebra.smul_def]
    simp only [map_natCast]
  rw [presentedPullback_eq p hp hp7 hp19 _ (j.val+1) (by omega) _ hP he,
    plainPullbackCoordinates_smul, plainPullbackCoordinates, map_natCast, Nat.add_sub_cancel,
    smul_smul]
  have hfac : (j.val.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  rw [mul_comm, inv_mul_cancel₀ hfac, one_smul]
  rfl

include hp7 hp19 in
theorem presentedPullback_boundary (b : Fin 6) :
    presentedPullback p hp (vertexBoundaryElement (Parameter.integralTenth p hp) b) =
      boundaryRawColumn p hp b := by
  have he : ((vertexBoundaryElement (Parameter.integralTenth p hp) b : FClosed _) : ActualRing _) =
      poleLinearMap (Parameter.integralTenth p hp) 1 (laurentVertex b) := by
    simp only [vertexBoundaryElement, WPResidueQuotient.b, actualVertex,
      poleLinearMap_apply, pow_one]
  rw [presentedPullback_eq p hp hp7 hp19 _ 1 (by omega) _
    (laurentVertex_mem_numeratorFiltration b) he, plainPullbackCoordinates]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rfl

def elevenRawColumn : Fin 11 → Fin 11 → ℚ_[p] :=
  fun j => Fin.addCases (m := 5) (n := 6)
    (gammaRawColumn p hp) (boundaryRawColumn p hp) j

include hp7 hp19 in
theorem presentedPullback_eleven (j : Fin 11) :
    presentedPullback p hp (Actual.elevenClosedElement (Parameter.integralTenth p hp) j) =
      elevenRawColumn p hp j := by
  refine Fin.addCases (m := 5) (n := 6) (fun j => ?_) (fun j => ?_) j
  · simpa only [Actual.elevenClosedElement_left, elevenRawColumn, Fin.addCases_left] using
      presentedPullback_gamma p hp hp7 hp19 j
  · simpa only [Actual.elevenClosedElement_right, elevenRawColumn, Fin.addCases_right] using
      presentedPullback_boundary p hp hp7 hp19 j

include hp7 hp19 in
theorem elevenRawColumn_norm (i j : Fin 11) : ‖elevenRawColumn p hp j i‖ ≤ 1 := by
  refine Fin.addCases (m := 5) (n := 6) (fun j => ?_) (fun j => ?_) j
  · simpa only [elevenRawColumn, Fin.addCases_left] using gammaRawColumn_norm p hp hp7 hp19 i j
  · simpa only [elevenRawColumn, Fin.addCases_right] using boundaryRawColumn_norm p hp hp7 hp19 i j

/-- Every entry is the integral value of its literal convergent Laurent pullback. -/
def elevenRawMatrix : Matrix (Fin 11) (Fin 11) ℤ_[p] :=
  fun i j => ⟨elevenRawColumn p hp j i, elevenRawColumn_norm p hp hp7 hp19 i j⟩

def coordinatePhi : (Fin 11 → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 11 → ℤ_[p]) :=
  Matrix.toLin' (elevenRawMatrix p hp hp7 hp19)

theorem coordinatePhi_apply (v : Fin 11 → ℤ_[p]) (i : Fin 11) :
    coordinatePhi p hp hp7 hp19 v i = ∑ j : Fin 11, elevenRawMatrix p hp hp7 hp19 i j * v j := rfl

theorem coordinatePhi_coe (v : Fin 11 → ℤ_[p]) (i : Fin 11) :
    IntegralTransport.padicCoefficientMap p (coordinatePhi p hp hp7 hp19 v i) =
      ∑ j : Fin 11, elevenRawColumn p hp j i * IntegralTransport.padicCoefficientMap p (v j) := by
  rw [coordinatePhi_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem quotientPullback_coordinates (g : ClosedResidueQuotient (Parameter.integralTenth p hp)) :
    quotientPullback p hp hp7 hp19 g = fun i => IntegralTransport.padicCoefficientMap p
      (coordinatePhi p hp hp7 hp19
        ((ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).symm g) i) := by
  obtain ⟨v, rfl⟩ := (ActualSpecialization.integralConstantQuotientEquiv p hp hp7 hp19).surjective g
  rw [LinearEquiv.symm_apply_apply]
  change presentedPullbackLinear p hp hp7 hp19
    (Actual.elevenSection (Parameter.integralTenth p hp) v) = fun i =>
      IntegralTransport.padicCoefficientMap p (coordinatePhi p hp hp7 hp19 v i)
  rw [Actual.elevenSection_apply, map_sum]
  simp only [map_smul, presentedPullbackLinear_apply,
    presentedPullback_eleven p hp hp7 hp19]
  funext i
  rw [coordinatePhi_coe]
  simp only [Finset.sum_apply, Algebra.smul_def, mul_comm]
  rfl

theorem presentedPullback_coordinates (g : FClosed (Parameter.integralTenth p hp)) :
    presentedPullback p hp g = fun i => IntegralTransport.padicCoefficientMap p
      (coordinatePhi p hp hp7 hp19 (ActualSpecialization.integralConstantCoordinates p hp hp7 hp19 g) i) :=
  quotientPullback_coordinates p hp hp7 hp19 (Submodule.Quotient.mk g)

theorem continuous_coordinatePhi : Continuous (coordinatePhi p hp hp7 hp19) := by
  apply continuous_pi
  intro i
  change Continuous (fun v : Fin 11 → ℤ_[p] =>
    ∑ j : Fin 11, elevenRawMatrix p hp hp7 hp19 i j * v j)
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

end WPResidueFrobenius
