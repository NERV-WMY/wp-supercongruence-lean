import WPResidueQuotient

noncomputable section

namespace WPReview.ResidueConnection

open scoped BigOperators
open WPResidueQuotient

variable (K : Type*) [CommRing K]

abbrev Coeff := ActualConnection.Coeff K
abbrev Residue := ClosedResidueQuotient (ActualConnection.parameter K)

/-- The five literal factorial residue classes, with no supplied basis. -/
def gammaSection : (Fin 5 → Coeff K) →ₗ[Coeff K] Residue K :=
  Fintype.linearCombination (Coeff K) (fun i : Fin 5 => ActualConnection.qGamma K i.val)

theorem gammaSection_apply (v : Fin 5 → Coeff K) :
    gammaSection K v = ∑ i : Fin 5, v i • ActualConnection.qGamma K i.val :=
  Fintype.linearCombination_apply _ _ _

@[simp] theorem gammaSection_single (i : Fin 5) :
    gammaSection K (Pi.single i 1) = ActualConnection.qGamma K i.val := by
  classical
  rw [gammaSection, Fintype.linearCombination_apply_single, one_smul]

/-- The matrix comes from the actual sixth-pole identity in the quotient. -/
def gammaM : Matrix (Fin 5) (Fin 5) (Coeff K) :=
  !![-1, 0, 0, 0, Parameter.discriminantInverse;
     1, -2, 0, 0, -31 * Parameter.discriminantInverse;
     0, 1, -3, 0, 90 * Parameter.discriminantInverse;
     0, 0, 1, -4, -65 * Parameter.discriminantInverse;
     0, 0, 0, 1, 15 * Parameter.discriminantInverse - 5]

theorem actual_connection_column (h6 : IsUnit (6 : K)) (j : Fin 5) :
    ActualConnection.quotientTheta K (ActualConnection.qGamma K j.val) =
      ∑ i : Fin 5, gammaM K i j • ActualConnection.qGamma K i.val := by
  fin_cases j
  · rw [ActualConnection.quotientTheta_Gamma]
    simp [gammaM, Fin.sum_univ_succ, neg_smul]
    abel
  · rw [ActualConnection.quotientTheta_Gamma]
    simp [gammaM, Fin.sum_univ_succ, neg_smul]
    rw [← Nat.cast_smul_eq_nsmul (Coeff K) 2]
    abel
  · rw [ActualConnection.quotientTheta_Gamma]
    simp [gammaM, Fin.sum_univ_succ, neg_smul]
    rw [← Nat.cast_smul_eq_nsmul (Coeff K) 3]
    abel
  · rw [ActualConnection.quotientTheta_Gamma]
    simp [gammaM, Fin.sum_univ_succ, neg_smul]
    rw [← Nat.cast_smul_eq_nsmul (Coeff K) 4]
    abel
  · rw [ActualConnection.quotientTheta_fifth_column K h6]
    simp [gammaM, Fin.sum_univ_succ]
    simp only [smul_add, smul_sub, sub_smul, mul_smul]
    rw [smul_comm Parameter.discriminantInverse (31 : ℕ),
      smul_comm Parameter.discriminantInverse (90 : ℕ),
      smul_comm Parameter.discriminantInverse (65 : ℕ),
      smul_comm Parameter.discriminantInverse (15 : ℕ)]
    simp only [← Nat.cast_smul_eq_nsmul (Coeff K)]
    abel

def coefficientEuler : (Fin 5 → Coeff K) →ₗ[K] (Fin 5 → Coeff K) where
  toFun v := fun i => Parameter.theta (v i)
  map_add' v w := by
    funext i
    exact map_add Parameter.theta (v i) (w i)
  map_smul' a v := by
    funext i
    exact Parameter.theta.toLinearMap.map_smul a (v i)

def gammaNabla : (Fin 5 → Coeff K) →ₗ[K] (Fin 5 → Coeff K) :=
  coefficientEuler K + (gammaM K).mulVecLin.restrictScalars K

theorem gammaNabla_apply (v : Fin 5 → Coeff K) (i : Fin 5) :
    gammaNabla K v i = Parameter.theta (v i) + ∑ j : Fin 5, gammaM K i j * v j := rfl

theorem gammaNabla_leibniz (a : Coeff K) (v : Fin 5 → Coeff K) :
    gammaNabla K (a • v) = Parameter.theta a • v + a • gammaNabla K v := by
  funext i
  simp only [gammaNabla_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    Derivation.leibniz]
  have hs : (∑ j : Fin 5, gammaM K i j * (a * v j)) =
      ∑ j : Fin 5, a * (gammaM K i j * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, ← Finset.mul_sum]
  ring

/-- Intertwining is proved from the actual derivative and allowed exact
reductions. It is not a premise about an abstract coordinate module. -/
theorem gammaSection_connection (h6 : IsUnit (6 : K)) (v : Fin 5 → Coeff K) :
    ActualConnection.quotientTheta K (gammaSection K v) =
      gammaSection K (gammaNabla K v) := by
  classical
  rw [gammaSection_apply, map_sum]
  simp only [ActualConnection.quotientTheta_smul,
    actual_connection_column K h6, Finset.sum_add_distrib, Finset.smul_sum]
  rw [gammaSection_apply]
  simp only [gammaNabla_apply, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, mul_comm]

theorem actual_qGamma_eq_family (i : Fin 5) :
    ActualConnection.qGamma K i.val =
      MellinFactors.gammaQuotientFamily (ActualConnection.parameter K) i := by
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact Gamma_succ (ActualConnection.parameter K) i.val

section Integral

variable (p : ℕ) [Fact p.Prime]

/-- Independence is inherited from the actual integral Mellin functional,
not asserted as a basis assumption for the coordinate connection. -/
theorem integral_gammaSection_injective :
    Function.Injective (gammaSection ℤ_[p]) := by
  have hi :=
    (MellinFactors.integralGammaQuotientFamily_independent p).fintypeLinearCombination_injective
  have hf : (fun i : Fin 5 => ActualConnection.qGamma ℤ_[p] i.val) =
      MellinFactors.gammaQuotientFamily (ActualConnection.parameter ℤ_[p]) := by
    funext i
    exact actual_qGamma_eq_family ℤ_[p] i
  simpa only [gammaSection, hf] using hi

theorem integral_gammaSection_connection (hp : 7 ≤ p) (v : Fin 5 → Coeff ℤ_[p]) :
    ActualConnection.quotientTheta ℤ_[p] (gammaSection ℤ_[p] v) =
      gammaSection ℤ_[p] (gammaNabla ℤ_[p] v) :=
  gammaSection_connection ℤ_[p] (Parameter.padic_six_unit p hp) v

theorem integral_actual_connection_coordinates (hp : 7 ≤ p)
    (v w : Fin 5 → Coeff ℤ_[p]) :
    ActualConnection.quotientTheta ℤ_[p] (gammaSection ℤ_[p] v) =
      gammaSection ℤ_[p] w ↔ gammaNabla ℤ_[p] v = w := by
  rw [integral_gammaSection_connection p hp]
  exact (integral_gammaSection_injective p).eq_iff

end Integral

end WPReview.ResidueConnection
