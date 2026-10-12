import WPResidueFrobenius.Convergence

noncomputable section

namespace WPResidueFrobenius

open scoped BigOperators Topology
open Filter WPResidueQuotient IsUltrametricDist

variable (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)

def gammaNumerator : WPResidueQuotient.LaurentPolynomial ℤ_[p] := 1

theorem gammaNumerator_supported (r : ℕ) :
    gammaNumerator p ∈ numeratorFiltration ℤ_[p] r := one_mem_numeratorFiltration r

def gammaRawColumn (j : Fin 5) : Fin 11 → ℚ_[p] :=
  rawPullbackCoordinates p hp (j.val+1) (by omega) (gammaNumerator p)
    (gammaNumerator_supported p (j.val+1))

/-- The literal finite raw pullback retains precisely k=0,...,122. -/
def gammaT128Column (j : Fin 5) : Fin 11 → ℚ_[p] :=
  ∑ k ∈ Finset.range 123, ActualSpecialization.tenthClosedCoordinates ℚ_[p]
    (rawPullbackTerm p hp (j.val+1) k (by omega) (gammaNumerator p)
      (gammaNumerator_supported p (j.val+1)))

include hp7 hp19 in
theorem gammaRawColumn_T128_norm (i : Fin 11) (j : Fin 5) :
    ‖gammaRawColumn p hp j i - gammaT128Column p hp j i‖ ≤ (p : ℝ)^(-8 : ℤ) := by
  let f (k : ℕ) : ℚ_[p] := ActualSpecialization.tenthClosedCoordinates ℚ_[p]
    (rawPullbackTerm p hp (j.val+1) k (by omega) (gammaNumerator p)
      (gammaNumerator_supported p (j.val+1))) i
  have hs : Summable f := by
    exact (Pi.summable.mp (rawPullbackTerm_coordinates_summable p hp hp7 hp19
      (j.val+1) (by omega) (gammaNumerator p) (gammaNumerator_supported p _))) i
  have hsplit := hs.sum_add_tsum_nat_add 123
  have he : gammaRawColumn p hp j i - gammaT128Column p hp j i = ∑' k, f (k+123) := by
    rw [gammaRawColumn, rawPullbackCoordinates, gammaT128Column,
      tsum_apply (rawPullbackTerm_coordinates_summable p hp hp7 hp19 _ _ _ _)]
    simp only [Finset.sum_apply]
    exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsplit)).symm
  rw [he]
  apply norm_tsum_le_of_forall_le
  intro k
  exact rawPullbackTerm_coordinate_precision p hp hp7 hp19 (j.val+1) (k+123) 8
    (by omega) (gammaNumerator p) (gammaNumerator_supported p _) i
    (pullback_gain_T128 p (j.val+1) (k+123) (Fact.out : p.Prime) hp hp7
      (by omega) (by omega) (by omega))

include hp7 hp19 in
theorem gammaRawColumn_norm (i : Fin 11) (j : Fin 5) : ‖gammaRawColumn p hp j i‖ ≤ 1 := by
  rw [gammaRawColumn, rawPullbackCoordinates,
    tsum_apply (rawPullbackTerm_coordinates_summable p hp hp7 hp19 _ _ _ _)]
  apply norm_tsum_le_of_forall_le
  intro k
  simpa using rawPullbackTerm_coordinate_precision p hp hp7 hp19 (j.val+1) k 0
    (by omega) (gammaNumerator p) (gammaNumerator_supported p _) i
    (pullback_gain_nonnegative p (j.val+1) k (Fact.out : p.Prime) hp hp7
      (by omega) (by omega))

include hp7 hp19 in
theorem gammaT128Column_norm (i : Fin 11) (j : Fin 5) : ‖gammaT128Column p hp j i‖ ≤ 1 := by
  unfold gammaT128Column
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_forall_le_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro k _
  simpa using rawPullbackTerm_coordinate_precision p hp hp7 hp19 (j.val+1) k 0
    (by omega) (gammaNumerator p) (gammaNumerator_supported p _) i
    (pullback_gain_nonnegative p (j.val+1) k (Fact.out : p.Prime) hp hp7
      (by omega) (by omega))

/-- Integral entries are constructed from the actual raw series, using its norm proof. -/
def gammaRawMatrix : Matrix (Fin 11) (Fin 5) ℤ_[p] :=
  fun i j => ⟨gammaRawColumn p hp j i, gammaRawColumn_norm p hp hp7 hp19 i j⟩

/-- Integral entries of the literal finite T128 raw column matrix. -/
def gammaT128Matrix : Matrix (Fin 11) (Fin 5) ℤ_[p] :=
  fun i j => ⟨gammaT128Column p hp j i, gammaT128Column_norm p hp hp7 hp19 i j⟩

theorem gammaT128Matrix_mod_p8 (i : Fin 11) (j : Fin 5) :
    ∃ z : ℤ_[p], gammaRawMatrix p hp hp7 hp19 i j - gammaT128Matrix p hp hp7 hp19 i j =
      (p : ℤ_[p])^8*z := by
  let d : ℚ_[p] := gammaRawColumn p hp j i - gammaT128Column p hp j i
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnorm : ‖d / (p : ℚ_[p])^8‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow]
    apply (div_le_one₀ (zpow_pos (by positivity : (0 : ℝ) < p) _)).mpr
    exact gammaRawColumn_T128_norm p hp hp7 hp19 i j
  refine ⟨⟨d / (p : ℚ_[p])^8, hnorm⟩, ?_⟩
  apply PadicInt.ext
  change d = (p : ℚ_[p])^8*(d/(p : ℚ_[p])^8)
  field_simp

theorem gammaRawIntegral_interior (r k : ℕ) (hr : 1 ≤ r) :
    ((rawIntegralGenerator p hp r k hr (gammaNumerator p)
      (gammaNumerator_supported p r) : FClosed (Parameter.integralTenth p hp)) :
        ActualRing (Parameter.integralTenth p hp)) ∈ FInterior (Parameter.integralTenth p hp) := by
  apply factorialNumeratorMap_mem_interior
  have hsupport : pullbackNumerator p hp (gammaNumerator p) k ∈
      numeratorFiltration ℤ_[p] (p*k) := by
    simpa [pullbackNumerator, gammaNumerator] using
      numeratorFiltration_pow (G p hp) p k (G_supported p hp)
  apply numeratorFiltration_mono _ hsupport
  have hp0 := (Fact.out : p.Prime).pos
  have hpr := Nat.mul_pos hp0 (by omega : 0 < r)
  rw [Nat.mul_add]
  omega

theorem gammaRawTerm_interior (r k : ℕ) (hr : 1 ≤ r) :
    ((rawPullbackTerm p hp r k hr (gammaNumerator p)
      (gammaNumerator_supported p r) : FClosed (1/10 : ℚ_[p])) : ActualRing (1/10 : ℚ_[p])) ∈
        FInterior (1/10 : ℚ_[p]) := by
  apply (FInterior (1/10 : ℚ_[p])).smul_mem
  exact IntegralTransport.actualMap_preserves_interior
    (IntegralTransport.padicCoefficientMap p) (Parameter.integralTenth p hp) (1/10 : ℚ_[p])
    (ParameterSpecialization.integralTenth_in_field p hp) (gammaRawIntegral_interior p hp r k hr)

theorem gammaRawTerm_boundary_zero (r k : ℕ) (hr : 1 ≤ r) (b : Fin 6) :
    ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr (gammaNumerator p)
        (gammaNumerator_supported p r)) (Fin.natAdd 5 b) = 0 := by
  have hcoords : ActualSpecialization.tenthClosedCoordinates ℚ_[p]
      (rawPullbackTerm p hp r k hr (gammaNumerator p)
        (gammaNumerator_supported p r)) ∈ Actual.interiorCoordinates ℚ_[p] := by
    rw [← ActualSpecialization.tenthClosedCoordinates_interior_image ℚ_[p]]
    exact ⟨_, gammaRawTerm_interior p hp r k hr, rfl⟩
  exact hcoords b

include hp7 hp19 in
theorem gammaRawColumn_boundary_zero (b : Fin 6) (j : Fin 5) :
    gammaRawColumn p hp j (Fin.natAdd 5 b) = 0 := by
  rw [gammaRawColumn, rawPullbackCoordinates,
    tsum_apply (rawPullbackTerm_coordinates_summable p hp hp7 hp19 _ _ _ _)]
  simp only [gammaRawTerm_boundary_zero, tsum_zero]

theorem gammaT128Column_boundary_zero (b : Fin 6) (j : Fin 5) :
    gammaT128Column p hp j (Fin.natAdd 5 b) = 0 := by
  simp only [gammaT128Column, Finset.sum_apply, gammaRawTerm_boundary_zero,
    Finset.sum_const_zero]

theorem gammaRawMatrix_boundary_zero (b : Fin 6) (j : Fin 5) :
    gammaRawMatrix p hp hp7 hp19 (Fin.natAdd 5 b) j = 0 := by
  apply PadicInt.ext
  exact gammaRawColumn_boundary_zero p hp hp7 hp19 b j

theorem gammaT128Matrix_boundary_zero (b : Fin 6) (j : Fin 5) :
    gammaT128Matrix p hp hp7 hp19 (Fin.natAdd 5 b) j = 0 := by
  apply PadicInt.ext
  exact gammaT128Column_boundary_zero p hp b j

def gammaT128InteriorMatrix : Matrix (Fin 5) (Fin 5) ℤ_[p] :=
  fun i j => gammaT128Matrix p hp hp7 hp19 (Fin.castAdd 6 i) j

end WPResidueFrobenius
