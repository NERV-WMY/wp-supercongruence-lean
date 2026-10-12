import WPGammaClosedNumeratorBounds.Gathering

noncomputable section

namespace WPGammaClosedNumeratorBounds

open scoped BigOperators
open WPIntegralBlocks WPResidueQuotient
open WPReview.ResidueNumeratorOperators WPReview.ResidueClosedConnection

theorem wordExponent_count (w : List (Fin 6)) (i : Fin 6) : wordExponent w i = w.count i := by
  induction w with
  | nil => simp [wordExponent]
  | cons j w ih =>
    by_cases hji : j=i
    · subst j
      simp [wordExponent, addNumeratorExponent, ih, add_comm]
    · simp [wordExponent, addNumeratorExponent, ih, hji, Ne.symm hji]

theorem wordExponent_perm {v w : List (Fin 6)} (h : v.Perm w) : wordExponent v = wordExponent w := by
  funext i
  rw [wordExponent_count, wordExponent_count]
  exact h.count_eq i

theorem word_perm_canonical (w : List (Fin 6)) : w.Perm (canonicalWord (wordExponent w)) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [← wordExponent_count, ← wordExponent_count, canonicalWord_exponent]

variable (p : ℕ) [Fact p.Prime]

theorem progression_apply (b j : ℕ) (v : Space p) :
    progression p (-6*(b : ℤ)) (-6) j v =
      gammaNabla p v - (6*((b+j : ℕ) : S p)) • v := by
  change gammaNabla p v + (((-6*(b : ℤ) : ℤ) : S p)+(-6 : S p)*j) • v = _
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1
  congr 1
  push_cast
  ring

theorem started_cons_factor (base : Fin 6 → ℕ) (x : Space p) (i : Fin 6) (w : List (Fin 6)) :
    startedCoordinateOperators ℤ_[p] base x (i::w) =
      progression p (-6*(base i : ℤ)) (-6) (wordExponent w i)
        (startedCoordinateOperators ℤ_[p] base x w) :=
  (progression_apply p (base i) (wordExponent w i) _).symm

set_option maxHeartbeats 1000000 in
theorem started_word_perm (base : Fin 6 → ℕ) (x : Space p)
    {v w : List (Fin 6)} (h : v.Perm w) :
    startedCoordinateOperators ℤ_[p] base x v = startedCoordinateOperators ℤ_[p] base x w := by
  induction h with
  | nil => rfl
  | cons i h ih =>
    simp only [startedCoordinateOperators]
    rw [wordExponent_perm h, ih]
  | swap i j w =>
    by_cases hij : i=j
    · subst j; rfl
    · simp only [started_cons_factor, wordExponent, addNumeratorExponent, Pi.add_apply]
      simp only [Pi.single_apply, if_neg hij, if_neg (Ne.symm hij), add_zero]
      simpa only [Module.End.mul_apply] using DFunLike.congr_fun
        (progression_commute p (-6*(base j : ℤ)) (-6) (-6*(base i : ℤ)) (-6)
          (wordExponent w j) (wordExponent w i)).eq
        (startedCoordinateOperators ℤ_[p] base x w)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem ordered_succ_reverse (b d : ℤ) (s n : ℕ) :
    ordered (progression p b d) s (n+1) =
      progression p b d (s+n) * ordered (progression p b d) s n := by
  rw [ordered_add _ _ n 1]
  simp only [ordered, mul_one]
  have hc := progression_ordered_commute p b d b d s n (s+n) 1
  simpa only [ordered, mul_one] using hc.eq

theorem replicate_word_factorization (base : Fin 6 → ℕ) (i : Fin 6) (m : ℕ)
    (w : List (Fin 6)) (v : Space p) :
    startedCoordinateOperators ℤ_[p] base v (List.replicate m i ++ w) =
      ordered (progression p (-6*(base i : ℤ)) (-6)) (wordExponent w i) m
        (startedCoordinateOperators ℤ_[p] base v w) := by
  induction m with
  | zero => simp [ordered]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, startedCoordinateOperators, ih,
      ordered_succ_reverse]
    simp only [wordExponent_append, wordExponent_replicate, Pi.add_apply, Pi.single_eq_same]
    rw [Module.End.mul_apply, progression_apply]
    rw [Nat.add_comm m (wordExponent w i)]
    rfl

theorem replicate_word (base : Fin 6 → ℕ) (i : Fin 6) (m : ℕ) (v : Space p) :
    startedCoordinateOperators ℤ_[p] base v (List.replicate m i) =
      ordered (progression p (-6*(base i : ℤ)) (-6)) 0 m v := by
  simpa [wordExponent, startedCoordinateOperators] using
    replicate_word_factorization p base i m [] v

def boundaryProgressions (base b : Fin 6 → ℕ) : List Progression :=
  [⟨-6*(base 0 : ℤ),-6,0,b 0⟩, ⟨-6*(base 1 : ℤ),-6,0,b 1⟩,
   ⟨-6*(base 2 : ℤ),-6,0,b 2⟩, ⟨-6*(base 3 : ℤ),-6,0,b 3⟩,
   ⟨-6*(base 4 : ℤ),-6,0,b 4⟩, ⟨-6*(base 5 : ℤ),-6,0,b 5⟩]

def boundaryProduct (base b : Fin 6 → ℕ) : End p :=
  ((boundaryProgressions base b).map (product p)).prod

theorem canonical_factorization (base b : Fin 6 → ℕ) (v : Space p) :
    startedCoordinateOperators ℤ_[p] base v (canonicalWord b) = boundaryProduct p base b v := by
  simp only [canonicalWord, List.append_assoc, replicate_word_factorization,
    wordExponent_append, wordExponent_replicate, Pi.add_apply]
  simp only [Pi.single_apply, ite_false, Fin.isValue, Fin.reduceEq, add_zero, replicate_word]
  simp [boundaryProduct, boundaryProgressions, product, Module.End.mul_apply]

theorem arbitrary_word_factorization (base : Fin 6 → ℕ) (v : Space p) (w : List (Fin 6)) :
    startedCoordinateOperators ℤ_[p] base v w = boundaryProduct p base (wordExponent w) v := by
  rw [started_word_perm p base v (word_perm_canonical w), canonical_factorization]

def blockCount (p : ℕ) (b : Fin 6 → ℕ) : ℕ := ∑ i, b i / p

theorem boundaryProduct_divisible (hp7 : 7 ≤ p) (base b : Fin 6 → ℕ) :
    Divisible p (blockCount p b/5) (boundaryProduct p base b) := by
  have he := progressions_divisible p hp7 (boundaryProgressions base b) (by
    intro r hr
    simp only [boundaryProgressions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact WPGammaIntegralLift.negative_six_residue_ne_zero p hp7)
  simpa [boundaryProduct, boundaryProgressions, blockCount, Fin.sum_univ_succ,
    Nat.add_assoc] using he

theorem boundary_word_coordinates_exact (hp7 : 7 ≤ p) (i : Fin 6) (w : List (Fin 6)) :
    ∃ v : Space p, boundaryWordCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) i w =
      (p : ℤ)^(blockCount p (wordExponent w)/5) • v := by
  obtain ⟨v, hv⟩ := boundaryProduct_divisible p hp7 (Pi.single i 1) (wordExponent w)
    ((6*ActualConnection.parameter ℤ_[p]) • boundaryStart ℤ_[p] (Parameter.padic_six_unit p hp7) i)
  refine ⟨(ActualConnection.boundaryScalar ℤ_[p] (Parameter.padic_six_unit p hp7)) ^
    (w.length+1) • v, ?_⟩
  rw [boundaryWordCoordinates, arbitrary_word_factorization, hv]
  exact smul_comm _ _ _

theorem boundary_word_classes_exact (hp7 : 7 ≤ p) (i : Fin 6) (w : List (Fin 6)) :
    ∃ v : Space p, qNumerator ℤ_[p] (Pi.single i 1+wordExponent w) w.length
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) =
      (p : ℤ)^(blockCount p (wordExponent w)/5) • fullSection p hp7 v := by
  obtain ⟨v, hv⟩ := boundary_word_coordinates_exact p hp7 i w
  rw [← actual_unscaled_boundary_word_coordinates ℤ_[p] (Parameter.padic_six_unit p hp7), hv]
  exact ⟨v, map_zsmul (fullSection p hp7) _ _⟩

end WPGammaClosedNumeratorBounds
