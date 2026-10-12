import WPResidueQuotient.VertexExact

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

def vertexBoundaryElement {R : Type*} [CommRing R] (u : R) (j : Fin 6) : FClosed u :=
  ⟨b u j, b_mem_closed u j⟩

def vertexCoordinateMap {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) : FClosed u →ₗ[R] (Fin 6 → R) :=
  LinearMap.pi (fun v => vertexFunctional u hu v)

@[simp] theorem vertexCoordinateMap_apply {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (g : FClosed u) (v : Fin 6) :
    vertexCoordinateMap u hu g v = vertexFunctional u hu v g := rfl

/-- The actual boundary classes give a normalized section of the six vertex coordinates. -/
def vertexBoundarySection {R : Type*} [CommRing R] (u : R) :
    (Fin 6 → R) →ₗ[R] FClosed u where
  toFun c := ∑ j : Fin 6, (-u * c j) • vertexBoundaryElement u j
  map_add' c d := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    simp only [RingHom.id_apply]
    ring

@[simp] theorem vertexBoundarySection_apply {R : Type*} [CommRing R]
    (u : R) (c : Fin 6 → R) :
    vertexBoundarySection u c = ∑ j : Fin 6, (-u * c j) • vertexBoundaryElement u j := rfl

theorem vertexCoordinateMap_boundaryElement {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (j v : Fin 6) :
    vertexCoordinateMap u hu (vertexBoundaryElement u j) v =
      -(↑hu.unit⁻¹ : R) * (if j = v then 1 else 0) :=
  vertexFunctional_b u hu v j

theorem vertexCoordinateMap_boundarySection {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (c : Fin 6 → R) :
    vertexCoordinateMap u hu (vertexBoundarySection u c) = c := by
  ext v
  simp only [vertexBoundarySection_apply, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, vertexCoordinateMap_boundaryElement, smul_eq_mul]
  calc
    (∑ j : Fin 6, (-u * c j) * (-(↑hu.unit⁻¹ : R) * (if j = v then 1 else 0))) =
        ∑ j : Fin 6, if j = v then c j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = v
      · simp only [if_pos hj, mul_one]
        calc
          (-u * c j) * -(↑hu.unit⁻¹ : R) = c j * ((↑hu.unit⁻¹ : R) * u) := by ring
          _ = c j := by rw [hu.val_inv_mul, mul_one]
      · simp only [if_neg hj, mul_zero]
    _ = c v := by simp

theorem vertexBoundarySection_injective {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) : Function.Injective (vertexBoundarySection u) := by
  intro c d h
  have hc := congrArg (vertexCoordinateMap u hu) h
  simpa only [vertexCoordinateMap_boundarySection] using hc

theorem vertexCoordinateMap_surjective {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) : Function.Surjective (vertexCoordinateMap u hu) :=
  fun c => ⟨vertexBoundarySection u c, vertexCoordinateMap_boundarySection u hu c⟩

theorem vertexCoordinateMap_interior_zero {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (g : FClosed u) (hg : (g : ActualRing u) ∈ FInterior u) :
    vertexCoordinateMap u hu g = 0 := by
  ext v
  exact vertexFunctional_interior_zero u hu v g hg

theorem exactSubmodule_le_vertexCoordinateMap_ker {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) : exactSubmodule u ≤ (vertexCoordinateMap u hu).ker := by
  intro g hg
  ext v
  exact exactSubmodule_le_vertexFunctional_ker u hu v hg

theorem Gamma_positive_mem_interior {R : Type*} [CommRing R] (u : R)
    (m : ℕ) (hm : 0 < m) : Gamma u m ∈ FInterior u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Gamma_succ]
  exact factorialPole_mem_interior u n

theorem vertexCoordinateMap_Gamma_positive_zero {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (m : ℕ) (hm : 0 < m) :
    vertexCoordinateMap u hu ⟨Gamma u m,
      FInterior_le_FClosed u (Gamma_positive_mem_interior u m hm)⟩ = 0 :=
  vertexCoordinateMap_interior_zero u hu _ (Gamma_positive_mem_interior u m hm)

/-- Descent through the actual logarithmic-image quotient. -/
def vertexQuotientMap {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) : ClosedResidueQuotient u →ₗ[R] (Fin 6 → R) :=
  (exactSubmodule u).liftQ (vertexCoordinateMap u hu)
    (exactSubmodule_le_vertexCoordinateMap_ker u hu)

@[simp] theorem vertexQuotientMap_mkQ {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (g : FClosed u) :
    vertexQuotientMap u hu ((exactSubmodule u).mkQ g) = vertexCoordinateMap u hu g := rfl

def vertexQuotientSection {R : Type*} [CommRing R] (u : R) :
    (Fin 6 → R) →ₗ[R] ClosedResidueQuotient u :=
  (exactSubmodule u).mkQ.comp (vertexBoundarySection u)

theorem vertexQuotientMap_section {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (c : Fin 6 → R) :
    vertexQuotientMap u hu (vertexQuotientSection u c) = c :=
  vertexCoordinateMap_boundarySection u hu c

end

end WPResidueQuotient
