import WPResidueQuotient.VertexFunctional

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

theorem b_mem_closed {R : Type*} [CommRing R] (u : R) (j : Fin 6) :
    b u j ∈ FClosed u := by
  have h := factorialNumeratorMap_mem_closed u 0 (laurentVertex_mem_numeratorFiltration j)
  simpa only [factorialNumeratorMap_apply, factorialPole, Nat.factorial_zero,
    Nat.cast_one, zero_add, pow_one, one_mul, b, actualVertex] using h

theorem b_pole_presentation {R : Type*} [CommRing R] (u : R) (j : Fin 6) :
    b u j = poleLinearMap u 1 (laurentVertex j) := by
  simp only [b, actualVertex, poleLinearMap_apply, pow_one]

theorem vertexFunctional_b {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v j : Fin 6) :
    vertexFunctional u hu v ⟨b u j, b_mem_closed u j⟩ =
      -(↑hu.unit⁻¹ : R) * (if j = v then 1 else 0) := by
  rw [vertexFunctional_eq_presentation u hu v _ 1 (laurentVertex j)
    (laurentVertex_mem_numeratorFiltration j) (b_pole_presentation u j)]
  simp only [pow_one, one_nsmul, laurentVertex, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  simp only [sixVertex_injective.eq_iff]

theorem logarithmicDerivation_coefficient {R : Type*} [CommRing R]
    (w : Exponents →+ ℤ) (P : LaurentPolynomial R) (x : Exponents) :
    (logarithmicDerivation w P).coeff x = (w x : R) * P.coeff x := by
  classical
  induction P using AddMonoidAlgebra.induction_on with
  | of y =>
      by_cases hy : y = x
      · subst y
        simp [AddMonoidAlgebra.of_apply]
      · simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.coeff_single,
          Ne.symm hy]
  | add P Q hP hQ =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
      ring
  | smul c P hP =>
      simp only [Derivation.map_smul, AddMonoidAlgebra.coeff_smul_apply,
        smul_eq_mul, hP]
      ring

theorem logarithmicDerivation_preserves_numeratorFiltration {R : Type*} [CommRing R]
    (w : Exponents →+ ℤ) (m : ℕ) {P : LaurentPolynomial R}
    (hP : P ∈ numeratorFiltration R m) :
    logarithmicDerivation w P ∈ numeratorFiltration R m := by
  classical
  rw [mem_numeratorFiltration]
  intro x hx
  have hx' := Finsupp.mem_support_iff.1 hx
  rw [logarithmicDerivation_coefficient] at hx'
  have hPx : P.coeff x ≠ 0 := by
    intro h
    rw [h, mul_zero] at hx'
    exact hx' rfl
  exact (mem_numeratorFiltration m P).1 hP x (Finsupp.mem_support_iff.2 hPx)

theorem actualD_algebraMap_numerator {R : Type*} [CommRing R]
    (u : R) (i : Fin 5) (P : LaurentPolynomial R) :
    actualD u i (algebraMap (LaurentPolynomial R) (ActualRing u) P) =
      algebraMap (LaurentPolynomial R) (ActualRing u)
        (logarithmicDerivation (coordinateWeight i) P) := by
  exact extendDerivation_algebraMap (torusPolynomial u)
    (logarithmicDerivation (coordinateWeight i)) P

def logarithmicPoleNumerator {R : Type*} [CommRing R] (u : R) (i : Fin 5)
    (m : ℕ) (P : LaurentPolynomial R) : LaurentPolynomial R :=
  logarithmicDerivation (coordinateWeight i) P * torusPolynomial u +
    (m : R) • (u • (P * (laurentVertex i.castSucc - laurentVertex (Fin.last 5))))

theorem logarithmicPoleNumerator_supported {R : Type*} [CommRing R]
    (u : R) (i : Fin 5) (m : ℕ) {P : LaurentPolynomial R}
    (hP : P ∈ numeratorFiltration R m) :
    logarithmicPoleNumerator u i m P ∈ numeratorFiltration R (m + 1) := by
  apply (numeratorFiltration R (m + 1)).add_mem
  · exact numeratorFiltration_mul_f u m
      (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) m hP)
  · apply (numeratorFiltration R (m + 1)).smul_mem
    apply (numeratorFiltration R (m + 1)).smul_mem
    rw [mul_sub]
    exact (numeratorFiltration R (m + 1)).sub_mem
      (numeratorFiltration_mul hP (laurentVertex_mem_numeratorFiltration i.castSucc))
      (numeratorFiltration_mul hP (laurentVertex_mem_numeratorFiltration (Fin.last 5)))

/-- The derivative is expressed with an actual common numerator at the next allowed pole. -/
theorem actualD_poleLinearMap_succ {R : Type*} [CommRing R] (u : R)
    (i : Fin 5) (n : ℕ) (P : LaurentPolynomial R) :
    actualD u i (poleLinearMap u (n + 1) P) =
      poleLinearMap u (n + 2) (logarithmicPoleNumerator u i (n + 1) P) := by
  rw [logarithmicPoleNumerator, map_add]
  have hr := poleLinearMap_raise u (n + 1) 1
    (logarithmicDerivation (coordinateWeight i) P)
  simp only [pow_one] at hr
  rw [hr]
  simp only [poleLinearMap_apply]
  rw [Derivation.leibniz, actualD_algebraMap_numerator, Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, actualD_inverseF, Algebra.smul_def,
    Algebra.algebraMap_self, RingHom.id_apply, map_mul, map_sub, map_natCast,
    nsmul_eq_mul, laurentVertex, actualVertex, pow_succ]
  rw [← IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (ActualRing u)]
  rw [show (5 : Fin 6) = Fin.last 5 from rfl]
  ring

theorem single_vertex_top_coefficient {R : Type*} [CommRing R] (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) (v w : Fin 6) :
    (P * laurentVertex w).coeff ((m + 1) • sixVertex v) =
      (if v = w then 1 else 0) * P.coeff (m • sixVertex v) := by
  classical
  simp only [laurentVertex, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one, ← sub_eq_add_neg]
  by_cases hvw : v = w
  · subst w
    rw [if_pos rfl, one_mul, nsmul_succ_sub_vertex]
  · rw [if_neg hvw, zero_mul]
    exact coefficient_at_off_vertex_shift_zero m hP v w hvw

theorem sixVertex_coordinate (i : Fin 5) (v : Fin 6) :
    sixVertex v i = (if v = i.castSucc then 1 else 0) - (if v = Fin.last 5 then 1 else 0) := by
  change (Pi.single v (1 : ℤ) : Fin 6 → ℤ) i.castSucc -
    (Pi.single v (1 : ℤ) : Fin 6 → ℤ) (Fin.last 5) = _
  simp [Pi.single_apply, eq_comm]

theorem logarithmicPoleNumerator_top_coefficient_zero {R : Type*} [CommRing R]
    (u : R) (i : Fin 5) (m : ℕ) {P : LaurentPolynomial R}
    (hP : P ∈ numeratorFiltration R m) (v : Fin 6) :
    (logarithmicPoleNumerator u i m P).coeff ((m + 1) • sixVertex v) = 0 := by
  unfold logarithmicPoleNumerator
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  rw [torusPolynomial_top_coefficient u m
    (logarithmicDerivation_preserves_numeratorFiltration (coordinateWeight i) m hP) v]
  rw [logarithmicDerivation_coefficient]
  rw [mul_sub]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rw [single_vertex_top_coefficient m hP v i.castSucc,
    single_vertex_top_coefficient m hP v (Fin.last 5)]
  rw [map_nsmul, coordinateWeight_apply, sixVertex_coordinate]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub,
    Int.cast_ite, Int.cast_one, Int.cast_zero]
  ring

theorem vertexFunctional_DClosed_zero {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (i : Fin 5) (g : FClosed u) :
    vertexFunctional u hu v (DClosed u i g) = 0 := by
  obtain ⟨m, P, hm, _, hP, hg⟩ := FClosed_common_pole u g.property
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hD : ((DClosed u i g : FClosed u) : ActualRing u) =
      poleLinearMap u (n + 2) (logarithmicPoleNumerator u i (n + 1) P) := by
    change actualD u i g = _
    rw [hg, actualD_poleLinearMap_succ]
  rw [vertexFunctional_eq_presentation u hu v (DClosed u i g) (n + 2)
    (logarithmicPoleNumerator u i (n + 1) P)
    (logarithmicPoleNumerator_supported u i (n + 1) hP) hD]
  rw [logarithmicPoleNumerator_top_coefficient_zero u i (n + 1) hP v, mul_zero]

/-- All six functionals annihilate the actual logarithmic-image submodule. -/
theorem exactSubmodule_le_vertexFunctional_ker {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) :
    exactSubmodule u ≤ (vertexFunctional u hu v).ker := by
  unfold exactSubmodule
  apply iSup_le
  intro i g hg
  obtain ⟨h, rfl⟩ := hg
  exact vertexFunctional_DClosed_zero u hu v i h

end

end WPResidueQuotient
