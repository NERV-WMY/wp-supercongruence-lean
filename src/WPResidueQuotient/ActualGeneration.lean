import WPResidueQuotient.ActualReduction

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

@[simp] theorem actualMonomial_zero {R : Type*} [CommRing R] (u : R) :
    actualMonomial u 0 = 1 := by
  change algebraMap (LaurentPolynomial R) (ActualRing u) (AddMonoidAlgebra.single 0 1) = 1
  simp [← AddMonoidAlgebra.one_def]

def exactAmbient {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  (exactSubmodule u).map (FClosed u).subtype

def allPoleSpan {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  Submodule.span R (Set.range (factorialPole u))

def allPoleBoundarySpan {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  Submodule.span R (Set.range (factorialPole u) ∪ Set.range (b u))

def reductionCoefficient {R : Type*} [CommRing R] (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) : R :=
  (n + 1 : R) + 6 * (a i : R) - ∑ k : Fin 6, (a k : R)

theorem reductionCoefficient_image {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) :
    algebraMap R (ActualRing u) (reductionCoefficient (R := R) a i n) =
      (n + 1 : ActualRing u) + 6 * (a i : ActualRing u) - ∑ k : Fin 6, (a k : ActualRing u) := by
  simp [reductionCoefficient, map_sum, map_ofNat]

theorem sum_Dik_mem_exactAmbient {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) (ha : (∑ k, a k) ≤ n + 1) :
    (∑ k : Fin 6, Dik u i k (numeratorGenerator u a n)) ∈ exactAmbient u := by
  let g : FClosed u := ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha⟩
  refine ⟨∑ k : Fin 6, DikClosed u i k g, ?_, ?_⟩
  · exact (exactSubmodule u).sum_mem (fun k _ => DikClosed_mem_exact u i k g)
  · simp only [Submodule.subtype_apply, Submodule.coe_sum, DikClosed_coe]
    rfl

theorem numeratorGenerator_zero {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    numeratorGenerator u 0 n = factorialPole u n := by
  change algebraMap (LaurentPolynomial R) (ActualRing u)
    (AddMonoidAlgebra.single 0 1) * factorialPole u n = factorialPole u n
  simp [← AddMonoidAlgebra.one_def]

theorem numeratorGenerator_single_zeroPole {R : Type*} [CommRing R] (u : R) (i : Fin 6) :
    numeratorGenerator u (Pi.single i 1) 0 = b u i := by
  have h := numeratorGenerator_add u 0 i 0
  have hz : actualMonomial u (fun k => ((0 : Fin 6 → ℕ) k : ℤ)) = 1 := actualMonomial_zero u
  rw [hz, one_mul] at h
  simpa [addNumeratorExponent, numeratorGenerator, b, factorialPole] using h

theorem removeNumeratorExponent (a : Fin 6 → ℕ) (h : 0 < ∑ k, a k) :
    ∃ (i : Fin 6) (c : Fin 6 → ℕ), a = addNumeratorExponent c i ∧
      (∑ k, a k) = (∑ k, c k) + 1 := by
  classical
  have hi : ∃ i, 0 < a i := by
    by_contra! hn
    have hz : a = 0 := by ext i; exact Nat.eq_zero_of_le_zero (hn i)
    simp [hz] at h
  obtain ⟨i, hi⟩ := hi
  let c : Fin 6 → ℕ := Function.update a i (a i - 1)
  have he : a = addNumeratorExponent c i := by
    ext k
    by_cases hk : k = i
    · subst k
      simp only [addNumeratorExponent, Pi.add_apply, c, Function.update_self,
        Pi.single_eq_same]
      omega
    · simp [addNumeratorExponent, c, hk]
  refine ⟨i, c, he, ?_⟩
  rw [he, addNumeratorExponent_sum]

theorem naturalExponents_eq_zero_of_sum_zero (a : Fin 6 → ℕ) (h : (∑ k, a k) = 0) : a = 0 := by
  ext i
  have hi : a i ≤ ∑ k, a k := Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ i)
  simp only [h] at hi
  exact Nat.eq_zero_of_le_zero hi

/-- Integral generation by every constant pole and the six boundary fractions.
    This precedes, and does not replace, the six-vertex pole reduction. -/
theorem numeratorGeneration_closed {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ k, a k) ≤ n + 1) :
    numeratorGenerator u a n ∈ exactAmbient u ⊔ allPoleBoundarySpan u := by
  classical
  generalize hd : (∑ k, a k) = d
  induction d using Nat.strong_induction_on generalizing a n with
  | h d ih =>
    by_cases hz : d = 0
    · have ha0 : a = 0 := naturalExponents_eq_zero_of_sum_zero a (hd.trans hz)
      rw [ha0, numeratorGenerator_zero]
      exact (le_sup_right : allPoleBoundarySpan u ≤ exactAmbient u ⊔ allPoleBoundarySpan u)
        (Submodule.subset_span (Or.inl ⟨n, rfl⟩))
    · obtain ⟨i, c, he, hs⟩ := removeNumeratorExponent a (by omega)
      have hc : (∑ k, c k) < d := by omega
      cases n with
      | zero =>
          have hc0 : c = 0 := naturalExponents_eq_zero_of_sum_zero c (by omega)
          rw [he, hc0]
          simp only [addNumeratorExponent, zero_add, numeratorGenerator_single_zeroPole]
          exact (le_sup_right : allPoleBoundarySpan u ≤ exactAmbient u ⊔ allPoleBoundarySpan u)
            (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
      | succ n =>
          have hcBound : (∑ k, c k) ≤ n + 1 := by omega
          have hsame := ih (∑ k, c k) hc c (n + 1) (by omega) rfl
          have hlower := ih (∑ k, c k) hc c n hcBound rfl
          rw [he, numeratorReduction_normalized u v huv c i n,
            ← reductionCoefficient_image u c i n]
          simp only [← Algebra.smul_def]
          apply (exactAmbient u ⊔ allPoleBoundarySpan u).add_mem
          · exact (exactAmbient u ⊔ allPoleBoundarySpan u).smul_mem v
              ((exactAmbient u ⊔ allPoleBoundarySpan u).sub_mem hsame
                ((exactAmbient u ⊔ allPoleBoundarySpan u).smul_mem
                  (reductionCoefficient (R := R) c i n) hlower))
          · exact (exactAmbient u ⊔ allPoleBoundarySpan u).smul_mem v
              ((le_sup_left : exactAmbient u ≤ exactAmbient u ⊔ allPoleBoundarySpan u)
                (sum_Dik_mem_exactAmbient u c i n hcBound))

theorem numeratorGeneration_interior {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ k, a k) ≤ n) :
    numeratorGenerator u a n ∈ exactAmbient u ⊔ allPoleSpan u := by
  classical
  generalize hd : (∑ k, a k) = d
  induction d using Nat.strong_induction_on generalizing a n with
  | h d ih =>
    by_cases hz : d = 0
    · have ha0 : a = 0 := naturalExponents_eq_zero_of_sum_zero a (hd.trans hz)
      rw [ha0, numeratorGenerator_zero]
      exact (le_sup_right : allPoleSpan u ≤ exactAmbient u ⊔ allPoleSpan u)
        (Submodule.subset_span ⟨n, rfl⟩)
    · obtain ⟨i, c, he, hs⟩ := removeNumeratorExponent a (by omega)
      have hc : (∑ k, c k) < d := by omega
      cases n with
      | zero => omega
      | succ n =>
          have hcBound : (∑ k, c k) ≤ n := by omega
          have hsame := ih (∑ k, c k) hc c (n + 1) (by omega) rfl
          have hlower := ih (∑ k, c k) hc c n hcBound rfl
          rw [he, numeratorReduction_normalized u v huv c i n,
            ← reductionCoefficient_image u c i n]
          simp only [← Algebra.smul_def]
          apply (exactAmbient u ⊔ allPoleSpan u).add_mem
          · exact (exactAmbient u ⊔ allPoleSpan u).smul_mem v
              ((exactAmbient u ⊔ allPoleSpan u).sub_mem hsame
                ((exactAmbient u ⊔ allPoleSpan u).smul_mem
                  (reductionCoefficient (R := R) c i n) hlower))
          · exact (exactAmbient u ⊔ allPoleSpan u).smul_mem v
              ((le_sup_left : exactAmbient u ≤ exactAmbient u ⊔ allPoleSpan u)
                (sum_Dik_mem_exactAmbient u c i n (by omega)))

theorem FClosed_numerator_generation {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) : FClosed u ≤ exactAmbient u ⊔ allPoleBoundarySpan u := by
  apply Submodule.span_le.mpr
  rintro g ⟨a, n, ha, rfl⟩
  exact numeratorGeneration_closed u v huv a n ha

theorem FInterior_numerator_generation {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) : FInterior u ≤ exactAmbient u ⊔ allPoleSpan u := by
  apply Submodule.span_le.mpr
  rintro g ⟨a, n, ha, rfl⟩
  exact numeratorGeneration_interior u v huv a n ha

/-- A bounded form of the same integral induction: no pole above the input
    pole occurs, and the exact primitives are the original allowed ones. -/
theorem numeratorGeneration_interior_of_poles {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (P : Submodule R (ActualRing u))
    (hN : exactAmbient u ≤ P) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ k, a k) ≤ n)
    (hG : ∀ k ≤ n, factorialPole u k ∈ P) : numeratorGenerator u a n ∈ P := by
  classical
  generalize hd : (∑ k, a k) = d
  induction d using Nat.strong_induction_on generalizing a n with
  | h d ih =>
    by_cases hz : d = 0
    · have ha0 : a = 0 := naturalExponents_eq_zero_of_sum_zero a (hd.trans hz)
      rw [ha0, numeratorGenerator_zero]
      exact hG n le_rfl
    · obtain ⟨i, c, he, hs⟩ := removeNumeratorExponent a (by omega)
      have hc : (∑ k, c k) < d := by omega
      cases n with
      | zero => omega
      | succ n =>
          have hcBound : (∑ k, c k) ≤ n := by omega
          have hsame := ih (∑ k, c k) hc c (n + 1) (by omega) hG rfl
          have hlower := ih (∑ k, c k) hc c n hcBound
            (fun k hk => hG k (by omega)) rfl
          rw [he, numeratorReduction_normalized u v huv c i n,
            ← reductionCoefficient_image u c i n]
          simp only [← Algebra.smul_def]
          exact P.add_mem
            (P.smul_mem v (P.sub_mem hsame
              (P.smul_mem (reductionCoefficient (R := R) c i n) hlower)))
            (P.smul_mem v (hN (sum_Dik_mem_exactAmbient u c i n (by omega))))

end

end WPResidueQuotient
