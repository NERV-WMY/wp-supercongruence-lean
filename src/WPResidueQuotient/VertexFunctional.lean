import WPResidueQuotient.PolePresentation

/-!
Extreme vertex coefficients of actual supported Laurent numerators. These
are the finite coefficient identities used to descend the six boundary
functionals through the actual localization and exact logarithmic images.
-/

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

theorem standardExponent_isCanonical (v : Fin 6) : IsCanonical (standardExponent v) := by
  obtain ⟨j, hj⟩ := exists_ne v
  exact ⟨standardExponent_nonneg v, ⟨j, by simp [standardExponent, hj]⟩⟩

theorem sixVertex_injective : Function.Injective sixVertex := by
  intro v w h
  have he : standardExponent v = standardExponent w := canonical_unique _ _
    (standardExponent_isCanonical v) (standardExponent_isCanonical w)
    (by simpa only [← sixVertex_eq_latticeQ_standardExponent] using h)
  have hv := congrFun he v
  by_contra hvw
  simp [standardExponent, hvw] at hv

theorem totalDegree_nsmul_standardExponent (k : ℕ) (v : Fin 6) :
    totalDegree (k • standardExponent v) = (k : ℤ) := by
  unfold totalDegree
  simp only [Pi.smul_apply]
  rw [Finset.sum_nsmul]
  change k • totalDegree (standardExponent v) = (k : ℤ)
  rw [totalDegree_standardExponent]
  simp

theorem nsmul_standardExponent_nonneg (k : ℕ) (v j : Fin 6) :
    0 ≤ (k • standardExponent v) j := by
  rw [Pi.smul_apply]
  exact nsmul_nonneg (standardExponent_nonneg v j) k

theorem minimumEntry_nsmul_standardExponent (k : ℕ) (v : Fin 6) :
    minimumEntry (k • standardExponent v) = 0 := by
  apply minimumEntry_eq_zero
  obtain ⟨j, hj⟩ := exists_ne v
  refine ⟨nsmul_standardExponent_nonneg k v, ⟨j, ?_⟩⟩
  rw [Pi.smul_apply]
  simp [standardExponent, hj]

theorem sixVertex_nsmul_degree (k : ℕ) (v : Fin 6) :
    canonicalDegreeNat (k • sixVertex v) = k := by
  have hq : latticeQ (k • standardExponent v) = k • sixVertex v := by
    rw [map_nsmul, sixVertex_eq_latticeQ_standardExponent]
  have hd := canonicalDegree_latticeQ (k • standardExponent v)
  rw [hq, totalDegree_nsmul_standardExponent, minimumEntry_nsmul_standardExponent] at hd
  rw [← canonicalDegreeNat_cast] at hd
  omega

theorem minimumEntry_vertex_difference (k : ℕ) (v w : Fin 6) (hvw : v ≠ w) :
    minimumEntry (k • standardExponent v - standardExponent w) = -1 := by
  apply le_antisymm
  · have h := minimumEntry_le (k • standardExponent v - standardExponent w) w
    have hw : (k • standardExponent v - standardExponent w) w = -1 := by
      rw [Pi.sub_apply, Pi.smul_apply]
      simp [standardExponent, Ne.symm hvw]
    simpa only [hw] using h
  · apply le_minimumEntry
    intro j
    change -1 ≤ (k • standardExponent v) j - standardExponent w j
    have h₁ := nsmul_standardExponent_nonneg k v j
    have h₂ := standardExponent_le_one w j
    omega

theorem sixVertex_nsmul_sub_degree (k : ℕ) (v w : Fin 6) (hvw : v ≠ w) :
    canonicalDegreeNat (k • sixVertex v - sixVertex w) = k + 5 := by
  have hq : latticeQ (k • standardExponent v - standardExponent w) =
      k • sixVertex v - sixVertex w := by
    rw [map_sub, map_nsmul, ← sixVertex_eq_latticeQ_standardExponent,
      ← sixVertex_eq_latticeQ_standardExponent]
  have ht : totalDegree (k • standardExponent v - standardExponent w) = (k : ℤ) - 1 := by
    unfold totalDegree
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
    change totalDegree (k • standardExponent v) - totalDegree (standardExponent w) = _
    rw [totalDegree_nsmul_standardExponent, totalDegree_standardExponent]
  have hd := canonicalDegree_latticeQ (k • standardExponent v - standardExponent w)
  rw [hq, ht, minimumEntry_vertex_difference k v w hvw] at hd
  rw [← canonicalDegreeNat_cast] at hd
  omega

theorem numeratorFiltration_coeff_eq_zero {R : Type*} [CommRing R] (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m)
    (x : Exponents) (hx : m < canonicalDegreeNat x) : P.coeff x = 0 := by
  classical
  apply Finsupp.notMem_support_iff.1
  intro h
  have hdeg := (mem_numeratorFiltration m P).1 hP x h
  omega

theorem coefficient_at_next_vertex_zero {R : Type*} [CommRing R] (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) (v : Fin 6) :
    P.coeff ((m + 1) • sixVertex v) = 0 := by
  apply numeratorFiltration_coeff_eq_zero m hP
  rw [sixVertex_nsmul_degree]
  omega

theorem coefficient_at_off_vertex_shift_zero {R : Type*} [CommRing R] (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m)
    (v w : Fin 6) (hvw : v ≠ w) :
    P.coeff ((m + 1) • sixVertex v - sixVertex w) = 0 := by
  apply numeratorFiltration_coeff_eq_zero m hP
  rw [sixVertex_nsmul_sub_degree (m + 1) v w hvw]
  omega

theorem nsmul_succ_sub_vertex (m : ℕ) (v : Fin 6) :
    (m + 1) • sixVertex v - sixVertex v = m • sixVertex v := by
  rw [add_nsmul, one_nsmul, add_sub_cancel_right]

theorem vertex_sum_top_coefficient {R : Type*} [CommRing R] (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) (v : Fin 6) :
    (∑ w : Fin 6, P * laurentVertex (R := R) w).coeff ((m + 1) • sixVertex v) =
      P.coeff (m • sixVertex v) := by
  classical
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    laurentVertex, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, ← sub_eq_add_neg]
  rw [← nsmul_succ_sub_vertex m v]
  apply Finset.sum_eq_single v
  · intro w _ hw
    exact coefficient_at_off_vertex_shift_zero m hP v w (Ne.symm hw)
  · simp

/-- The entire extreme-coefficient calculation, with the actual denominator. -/
theorem torusPolynomial_top_coefficient {R : Type*} [CommRing R] (u : R) (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) (v : Fin 6) :
    (P * torusPolynomial u).coeff ((m + 1) • sixVertex v) =
      -u * P.coeff (m • sixVertex v) := by
  have he : P * torusPolynomial u = P - u • ∑ w : Fin 6, P * laurentVertex w := by
    rw [torusPolynomial, mul_sub, mul_one, Algebra.smul_def]
    congr 1
    rw [← mul_assoc, mul_comm P (algebraMap R (LaurentPolynomial R) u),
      mul_assoc, Finset.mul_sum]
  rw [he]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  rw [coefficient_at_next_vertex_zero m hP v, vertex_sum_top_coefficient m hP v]
  ring

def vertexPoleValue {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (m : ℕ) (P : LaurentPolynomial R) : R :=
  (-(↑hu.unit⁻¹ : R)) ^ m * P.coeff (m • sixVertex v)

theorem vertexScale_succ_cancel {R : Type*} [CommRing R] (u : R) (hu : IsUnit u) (m : ℕ) :
    (-(↑hu.unit⁻¹ : R)) ^ (m + 1) * (-u) = (-(↑hu.unit⁻¹ : R)) ^ m := by
  rw [pow_succ, mul_assoc, neg_mul_neg, hu.val_inv_mul, mul_one]

theorem vertexPoleValue_add {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (m : ℕ) (P Q : LaurentPolynomial R) :
    vertexPoleValue u hu v m (P + Q) =
      vertexPoleValue u hu v m P + vertexPoleValue u hu v m Q := by
  simp only [vertexPoleValue, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

theorem vertexPoleValue_smul {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (m : ℕ) (c : R) (P : LaurentPolynomial R) :
    vertexPoleValue u hu v m (c • P) = c • vertexPoleValue u hu v m P := by
  simp only [vertexPoleValue, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  ring

theorem vertexPoleValue_raise_one {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (m : ℕ) {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) :
    vertexPoleValue u hu v (m + 1) (P * torusPolynomial u) = vertexPoleValue u hu v m P := by
  unfold vertexPoleValue
  rw [torusPolynomial_top_coefficient u m hP v, ← mul_assoc, vertexScale_succ_cancel]

theorem vertexPoleValue_raise {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (m k : ℕ) {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) :
    vertexPoleValue u hu v (m + k) (P * torusPolynomial u ^ k) = vertexPoleValue u hu v m P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      have hmk : m + (k + 1) = (m + k) + 1 := by omega
      rw [hmk, vertexPoleValue_raise_one u hu v (m + k)
        (numeratorFiltration_mul_f_pow u m k hP)]
      exact ih

/-- The value is independent of all actual supported common-pole presentations. -/
theorem vertexPoleValue_eq_of_fraction_eq {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (m n : ℕ)
    {P Q : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m)
    (hQ : Q ∈ numeratorFiltration R n)
    (h : poleLinearMap u m P = poleLinearMap u n Q) :
    vertexPoleValue u hu v m P = vertexPoleValue u hu v n Q := by
  have hc := (poleLinearMap_eq_iff_cross_multiply u m n P Q).1 h
  calc
    _ = vertexPoleValue u hu v (m + n) (P * torusPolynomial u ^ n) :=
      (vertexPoleValue_raise u hu v m n hP).symm
    _ = vertexPoleValue u hu v (n + m) (Q * torusPolynomial u ^ m) := by
      rw [hc, Nat.add_comm m n]
    _ = _ := vertexPoleValue_raise u hu v n m hQ

theorem FClosed_exists_supported_pole {R : Type*} [CommRing R] (u : R) (g : FClosed u) :
    ∃ mp : ℕ × LaurentPolynomial R, 0 < mp.1 ∧
      mp.2 ∈ numeratorFiltration R mp.1 ∧ (g : ActualRing u) = poleLinearMap u mp.1 mp.2 := by
  obtain ⟨m, P, hm, _, hP, hg⟩ := FClosed_common_pole u g.property
  exact ⟨⟨m, P⟩, hm, hP, hg⟩

def vertexPresentation {R : Type*} [CommRing R] (u : R) (g : FClosed u) :
    ℕ × LaurentPolynomial R := Classical.choose (FClosed_exists_supported_pole u g)

theorem vertexPresentation_spec {R : Type*} [CommRing R] (u : R) (g : FClosed u) :
    0 < (vertexPresentation u g).1 ∧
      (vertexPresentation u g).2 ∈ numeratorFiltration R (vertexPresentation u g).1 ∧
      (g : ActualRing u) = poleLinearMap u (vertexPresentation u g).1 (vertexPresentation u g).2 :=
  Classical.choose_spec (FClosed_exists_supported_pole u g)

def vertexFunctionalValue {R : Type*} [CommRing R] (u : R) (hu : IsUnit u)
    (v : Fin 6) (g : FClosed u) : R :=
  vertexPoleValue u hu v (vertexPresentation u g).1 (vertexPresentation u g).2

theorem vertexFunctionalValue_eq_presentation {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (g : FClosed u) (m : ℕ)
    (P : LaurentPolynomial R) (hP : P ∈ numeratorFiltration R m)
    (hg : (g : ActualRing u) = poleLinearMap u m P) :
    vertexFunctionalValue u hu v g = vertexPoleValue u hu v m P := by
  have hs := vertexPresentation_spec u g
  exact vertexPoleValue_eq_of_fraction_eq u hu v (vertexPresentation u g).1 m hs.2.1 hP
    (hs.2.2.symm.trans hg)

/-- A genuine linear boundary functional on the actual closed rational-function submodule. -/
def vertexFunctional {R : Type*} [CommRing R] [IsDomain R] (u : R) (hu : IsUnit u)
    (v : Fin 6) : FClosed u →ₗ[R] R where
  toFun := vertexFunctionalValue u hu v
  map_add' g h := by
    let m := (vertexPresentation u g).1
    let n := (vertexPresentation u h).1
    let P := (vertexPresentation u g).2
    let Q := (vertexPresentation u h).2
    have hg := vertexPresentation_spec u g
    have hh := vertexPresentation_spec u h
    have hP : P * torusPolynomial u ^ n ∈ numeratorFiltration R (m + n) :=
      numeratorFiltration_mul_f_pow u m n hg.2.1
    have hQ : Q * torusPolynomial u ^ m ∈ numeratorFiltration R (m + n) := by
      simpa only [Nat.add_comm n m] using numeratorFiltration_mul_f_pow u n m hh.2.1
    have hsum : ((g + h : FClosed u) : ActualRing u) =
        poleLinearMap u (m + n) (P * torusPolynomial u ^ n + Q * torusPolynomial u ^ m) := by
      rw [map_add, poleLinearMap_raise]
      have he : m + n = n + m := Nat.add_comm m n
      rw [he, poleLinearMap_raise]
      exact congrArg₂ (· + ·) hg.2.2 hh.2.2
    rw [vertexFunctionalValue_eq_presentation u hu v (g + h) (m + n) _
      ((numeratorFiltration R _).add_mem hP hQ) hsum, vertexPoleValue_add]
    have hPv := vertexPoleValue_raise u hu v m n hg.2.1
    have hQv : vertexPoleValue u hu v (m + n) (Q * torusPolynomial u ^ m) =
        vertexPoleValue u hu v n Q := by
      rw [Nat.add_comm m n]
      exact vertexPoleValue_raise u hu v n m hh.2.1
    rw [hPv, hQv]
    rfl
  map_smul' c g := by
    have hg := vertexPresentation_spec u g
    have he : ((c • g : FClosed u) : ActualRing u) =
        poleLinearMap u (vertexPresentation u g).1 (c • (vertexPresentation u g).2) := by
      rw [map_smul, ← hg.2.2]
      rfl
    rw [vertexFunctionalValue_eq_presentation u hu v (c • g) _ _
      ((numeratorFiltration R _).smul_mem c hg.2.1) he, vertexPoleValue_smul]
    rfl

theorem vertexFunctional_eq_presentation {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (g : FClosed u) (m : ℕ)
    (P : LaurentPolynomial R) (hP : P ∈ numeratorFiltration R m)
    (hg : (g : ActualRing u) = poleLinearMap u m P) :
    vertexFunctional u hu v g = (-(↑hu.unit⁻¹ : R)) ^ m * P.coeff (m • sixVertex v) :=
  vertexFunctionalValue_eq_presentation u hu v g m P hP hg

theorem vertexFunctional_interior_zero {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (g : FClosed u)
    (hg : (g : ActualRing u) ∈ FInterior u) : vertexFunctional u hu v g = 0 := by
  obtain ⟨m, P, hm, _, hP, he⟩ := FInterior_common_pole u hg
  have hP' : P ∈ numeratorFiltration R m :=
    numeratorFiltration_mono (Nat.sub_le m 1) hP
  rw [vertexFunctional_eq_presentation u hu v g m P hP' he]
  have hc : P.coeff (m • sixVertex v) = 0 := by
    apply numeratorFiltration_coeff_eq_zero (m - 1) hP
    rw [sixVertex_nsmul_degree]
    omega
  rw [hc, mul_zero]

theorem vertexFunctional_factorialPole_zero {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (hu : IsUnit u) (v : Fin 6) (n : ℕ) :
    vertexFunctional u hu v ⟨factorialPole u n,
      FInterior_le_FClosed u (factorialPole_mem_interior u n)⟩ = 0 :=
  vertexFunctional_interior_zero u hu v _ (factorialPole_mem_interior u n)

end

end WPResidueQuotient
