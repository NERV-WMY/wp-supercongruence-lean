import WPGammaNumeratorBounds.Gathering

noncomputable section

namespace WPGammaNumeratorBounds

open scoped BigOperators
open WPGammaIntegralLift WPIntegralBlocks WPResidueQuotient
open WPReview.ResidueNumeratorOperators

variable (p : ℕ) [Fact p.Prime]

theorem ordered_succ_reverse (b d : ℤ) (s n : ℕ) :
    ordered (progression p b d) s (n+1) =
      progression p b d (s+n) * ordered (progression p b d) s n := by
  rw [ordered_add _ _ n 1]
  simp only [ordered, mul_one]
  have hc := progression_ordered_commute p b d b d s n (s+n) 1
  simpa only [ordered, mul_one] using hc.eq

theorem replicate_word_factorization (i : Fin 6) (m : ℕ) (w : List (Fin 6)) (v : Space p) :
    coordinateOperators ℤ_[p] v (List.replicate m i ++ w) =
      ordered (progression p 0 (-6)) (wordExponent w i) m (coordinateOperators ℤ_[p] v w) := by
  induction m with
  | zero => simp [ordered]
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, coordinateOperators, ih,
      ordered_succ_reverse]
    simp only [wordExponent_append, wordExponent_replicate, Pi.add_apply, Pi.single_eq_same]
    change gammaNabla p _ - (6 * ((m + wordExponent w i : ℕ) : S p)) • _ =
      gammaNabla p _ + (0 + (-6 : S p) * (wordExponent w i + m : ℕ)) • _
    rw [sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    push_cast
    ring

theorem pole_factorization (m : ℕ) :
    coordinatePoleOperators ℤ_[p] m =
      ordered (progression p 1 1) 0 m (Pi.single 0 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [coordinatePoleOperators, ih, ordered_succ_reverse]
    simp [progression, factor, scalarAction, gammaNabla, Module.End.mul_apply, add_comm, add_smul]

theorem replicate_word (i : Fin 6) (m : ℕ) (v : Space p) :
    coordinateOperators ℤ_[p] v (List.replicate m i) =
      ordered (progression p 0 (-6)) 0 m v := by
  simpa [wordExponent, coordinateOperators] using replicate_word_factorization p i m [] v

def numeratorProgressions (a : Fin 6 → ℕ) (n : ℕ) : List Progression :=
  [⟨0,-6,0,a 0⟩, ⟨0,-6,0,a 1⟩, ⟨0,-6,0,a 2⟩,
   ⟨0,-6,0,a 3⟩, ⟨0,-6,0,a 4⟩, ⟨0,-6,0,a 5⟩,
   ⟨1,1,0,n-∑ i, a i⟩]

def numeratorProduct (a : Fin 6 → ℕ) (n : ℕ) : End p :=
  ((numeratorProgressions a n).map (product p)).prod

/-- All six vertex lists and the pole list, with the literal word order. -/
theorem canonical_factorization (a : Fin 6 → ℕ) (n : ℕ) :
    coordinateOperators ℤ_[p] (coordinatePoleOperators ℤ_[p] (n-∑ i, a i))
      (canonicalWord a) = numeratorProduct p a n (Pi.single 0 1) := by
  simp only [canonicalWord, List.append_assoc, replicate_word_factorization,
    wordExponent_append, wordExponent_replicate, Pi.add_apply]
  simp only [Pi.single_apply, ite_false, Fin.isValue, Fin.reduceEq,
    add_zero, pole_factorization, replicate_word]
  simp [numeratorProduct, numeratorProgressions, product, Module.End.mul_apply]

def blockCount (a : Fin 6 → ℕ) (n : ℕ) : ℕ :=
  (∑ i, a i / p) + (n-∑ i, a i)/p

theorem numeratorProduct_divisible (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ) :
    Divisible p (blockCount p a n / 5) (numeratorProduct p a n) := by
  have he := progressions_divisible p hp7 (numeratorProgressions a n) (by
    intro r hr
    simp only [numeratorProgressions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    all_goals first | exact negative_six_residue_ne_zero p hp7 | simp)
  simpa [numeratorProduct, numeratorProgressions, blockCount, Fin.sum_univ_succ,
    Nat.add_assoc] using he

/-- The stronger exact sum-of-floor-lengths bound for actual unscaled coordinates. -/
theorem strict_coordinates_exact (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ) :
    ∃ w : Space p, strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) a n =
      (p : ℤ)^(blockCount p a n / 5) • w := by
  obtain ⟨w, hw⟩ := numeratorProduct_divisible p hp7 a n (Pi.single 0 1)
  refine ⟨(ActualConnection.boundaryScalar ℤ_[p] (Parameter.padic_six_unit p hp7)) ^
    (∑ i, a i) • w, ?_⟩
  rw [strictNumeratorCoordinates, canonical_factorization, hw]
  exact smul_comm _ _ _

theorem strict_classes_exact (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) : ∃ w : Space p,
    qNumerator ℤ_[p] a n (by omega) =
      (p : ℤ)^(blockCount p a n / 5) • gammaSection p w := by
  obtain ⟨w, hw⟩ := strict_coordinates_exact p hp7 a n
  rw [← actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp7) a n ha, hw]
  exact ⟨w, map_zsmul (gammaSection p) _ _⟩

end WPGammaNumeratorBounds
