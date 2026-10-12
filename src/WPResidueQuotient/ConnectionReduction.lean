import WPResidueQuotient.ActualConnection
import WPResidueQuotient.ActualReduction

/-!
The boundary column is an unconditional identity in the actual quotient.
Its discarded primitive is Gamma one, which lies in the allowed module.
The scalar derivative is included before concluding the corrected column.
-/

namespace WPResidueQuotient.ActualConnection

noncomputable section
open scoped BigOperators

variable (K : Type*) [CommRing K]

theorem boundary_reduction_closed (h6 : IsUnit (6 : K)) (i : Fin 6) :
    vertexGammaTwoClosed K i =
      boundaryScalar K h6 • (gammaClosed K 1 - gammaClosed K 0) +
        boundaryScalar K h6 •
          ∑ k : Fin 6, DikClosed (parameter K) i k (gammaClosed K 0) := by
  have hinv : boundaryScalar K h6 * (6 * parameter K) = 1 := by
    rw [mul_comm]
    exact six_parameter_mul_boundaryScalar K h6
  have h := numeratorReduction_normalized (parameter K) (boundaryScalar K h6) hinv
    (0 : Fin 6 → ℕ) i 0
  rw [numeratorGenerator_add] at h
  have hm : actualMonomial (parameter K) (fun _ : Fin 6 => (0 : ℤ)) = 1 :=
    actualMonomial_zero K
  simp only [Pi.zero_apply, Nat.cast_zero, mul_zero, Finset.sum_const_zero,
    add_zero, sub_zero, zero_add] at h
  simp only [numeratorGenerator, Pi.zero_apply, Nat.cast_zero, hm, one_mul] at h
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub,
    Submodule.coe_sum, Algebra.smul_def, DikClosed_coe]
  simpa only [vertexGammaTwoClosed, gammaClosed, Gamma_succ] using h

theorem qVertexGammaTwo_reduction (h6 : IsUnit (6 : K)) (i : Fin 6) :
    qVertexGammaTwo K i = boundaryScalar K h6 • (qGamma K 1 - qGamma K 0) := by
  let primitive : FClosed (parameter K) := boundaryScalar K h6 •
    ∑ k : Fin 6, DikClosed (parameter K) i k (gammaClosed K 0)
  have hn : primitive ∈ exactSubmodule (parameter K) := by
    apply (exactSubmodule (parameter K)).smul_mem
    exact (exactSubmodule (parameter K)).sum_mem
      (fun k _ => DikClosed_mem_exact (parameter K) i k (gammaClosed K 0))
  have hz : (exactSubmodule (parameter K)).mkQ primitive = 0 :=
    (Submodule.Quotient.mk_eq_zero (exactSubmodule (parameter K))).mpr hn
  have h := congrArg (exactSubmodule (parameter K)).mkQ (boundary_reduction_closed K h6 i)
  change (exactSubmodule (parameter K)).mkQ (vertexGammaTwoClosed K i) =
    (exactSubmodule (parameter K)).mkQ
      (boundaryScalar K h6 • (gammaClosed K 1 - gammaClosed K 0) + primitive) at h
  rw [map_add, hz, add_zero, map_smul, map_sub] at h
  exact h

theorem quotientTheta_boundary_reduced (h6 : IsUnit (6 : K)) (i : Fin 6) :
    quotientTheta K (qBoundary K i) =
      boundaryScalar K h6 • (qGamma K 1 - qGamma K 0) - qBoundary K i := by
  rw [quotientTheta_boundary, qVertexGammaTwo_reduction K h6 i]

theorem quotientTheta_correctedBoundary_actual (h6 : IsUnit (6 : K)) (i : Fin 6) :
    quotientTheta K (correctedBoundary K h6 i) = -correctedBoundary K h6 i :=
  quotientTheta_correctedBoundary K h6 i (qVertexGammaTwo_reduction K h6 i)

end
end WPResidueQuotient.ActualConnection
