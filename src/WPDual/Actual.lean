import WPDual.Scaling

noncomputable section

namespace WPDual

open WPPsi

variable (p : ℕ) [Fact p.Prime]

theorem pairing_nondegenerate_right (w : StateSpace p)
    (h : ∀ v : StateSpace p, pairing p v w = 0) : w = 0 := by
  funext i
  have hi := h (Pi.single i (1 : K p))
  simpa [pairing, dotProduct, Pi.single_apply] using hi

theorem actual_dual_iterate_fifth_zero (hp7 : 7 ≤ p) (v : StateSpace p) :
    (fun w => (dualNabla p)^[p] w - dualNabla p w)^[5] v = 0 := by
  have he := LinearMap.congr_fun (actual_dual_fifth_zero p hp7) v
  rw [Module.End.pow_apply] at he
  have hs : (fun w => (dualNabla p)^[p] w - dualNabla p w) =
      (dualNabla p ^ p - dualNabla p : StateEnd p) := by
    funext w
    simp only [LinearMap.sub_apply, Module.End.pow_apply]
  rw [hs]
  exact he

theorem actual_six_rescaled_iterate_fifth_zero (hp7 : 7 ≤ p) (v : StateSpace p) :
    (fun w => (sixNabla p)^[p] w - sixNabla p w)^[5] v = 0 := by
  have he := LinearMap.congr_fun (actual_six_rescaled_fifth_zero p hp7) v
  rw [Module.End.pow_apply] at he
  have hs : (fun w => (sixNabla p)^[p] w - sixNabla p w) =
      (sixNabla p ^ p - sixNabla p : StateEnd p) := by
    funext w
    simp only [LinearMap.sub_apply, Module.End.pow_apply]
  rw [hs]
  exact he

theorem sixPsi_is_matrix (hp7 : 7 ≤ p) :
    sixPsi p = matrixAction p ((6 : K p) • dualPsiMatrix p) := by
  rw [six_pcurvature_scaling, dualPsi_is_matrix p hp7]
  apply LinearMap.ext
  intro v
  funext i
  change (6 : ZMod p) • (∑ j, dualPsiMatrix p i j * v j) =
    ∑ j, ((6 : K p) * dualPsiMatrix p i j) * v j
  rw [Algebra.smul_def, map_ofNat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sixPsiMatrix_fifth_zero : ((6 : K p) • dualPsiMatrix p) ^ 5 = 0 := by
  rw [smul_pow, dualPsiMatrix_fifth_zero, smul_zero]

end WPDual
