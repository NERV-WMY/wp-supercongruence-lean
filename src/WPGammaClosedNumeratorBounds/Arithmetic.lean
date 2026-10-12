import WPGammaClosedNumeratorBounds.Words

noncomputable section

namespace WPGammaClosedNumeratorBounds

open scoped BigOperators
open WPResidueQuotient
open WPReview.ResidueNumeratorOperators WPReview.ResidueClosedConnection

def lengths (b : Fin 6 → ℕ) : List ℕ := [b 0,b 1,b 2,b 3,b 4,b 5]

theorem lengths_sum (b : Fin 6 → ℕ) : (lengths b).sum = ∑ i, b i := by
  simp [lengths, Fin.sum_univ_succ]

theorem lengths_floor_sum (p : ℕ) (b : Fin 6 → ℕ) :
    ((lengths b).map (fun n => n/p)).sum = blockCount p b := by
  simp [lengths, blockCount, Fin.sum_univ_succ]

theorem six_list_count (p : ℕ) (b : Fin 6 → ℕ) :
    (((∑ i, b i)/p)-5)/5 ≤ blockCount p b/5 := by
  have he := WPGammaNumeratorBounds.floor_list_bound p (lengths b)
  rw [lengths_sum, lengths_floor_sum] at he
  have hl : (lengths b).length = 6 := by simp [lengths]
  rw [hl] at he
  apply Nat.div_le_div_right
  omega

theorem five_list_count (p : ℕ) (b : Fin 6 → ℕ) (hz : ∃ i, b i=0) :
    (((∑ i, b i)/p)-4)/5 ≤ blockCount p b/5 := by
  have hm : 0 ∈ lengths b := by
    obtain ⟨i, hi⟩ := hz
    fin_cases i <;> dsimp at hi <;> simp_all [lengths]
  have he := WPGammaNumeratorBounds.floor_list_bound p ((lengths b).erase 0)
  have hs : ((lengths b).erase 0).sum = ∑ i, b i := by
    simpa only [zero_add, lengths_sum] using List.sum_erase hm
  have hfs : (((lengths b).erase 0).map (fun n => n/p)).sum = blockCount p b := by
    simpa only [Nat.zero_div, zero_add, lengths_floor_sum] using List.sum_map_erase (fun n => n/p) hm
  have hl : ((lengths b).erase 0).length = 5 := by
    rw [List.length_erase_of_mem hm]
    simp [lengths]
  rw [hs, hfs, hl] at he
  apply Nat.div_le_div_right
  omega

variable (p : ℕ) [Fact p.Prime]

theorem coordinate_divisibility_mono (m k : ℕ) (v : Space p) (hmk : m ≤ k)
    (hv : ∃ w : Space p, v = (p : ℤ)^k • w) : ∃ w : Space p, v = (p : ℤ)^m • w := by
  obtain ⟨w, hw⟩ := hv
  refine ⟨(p : ℤ)^(k-m) • w, ?_⟩
  rw [hw, smul_smul, ← pow_add, Nat.add_sub_of_le hmk]

theorem boundary_word_coordinates_bound (hp7 : 7 ≤ p) (i : Fin 6) (w : List (Fin 6)) :
    ∃ v : Space p, boundaryWordCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) i w =
      (p : ℤ)^((w.length/p-5)/5) • v := by
  apply coordinate_divisibility_mono p _ _ _ _ (boundary_word_coordinates_exact p hp7 i w)
  simpa only [wordExponent_sum] using six_list_count p (wordExponent w)

theorem boundary_word_coordinates_zero_bound (hp7 : 7 ≤ p) (i : Fin 6)
    (w : List (Fin 6)) (hz : ∃ j, wordExponent w j=0) :
    ∃ v : Space p, boundaryWordCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) i w =
      (p : ℤ)^((w.length/p-4)/5) • v := by
  apply coordinate_divisibility_mono p _ _ _ _ (boundary_word_coordinates_exact p hp7 i w)
  simpa only [wordExponent_sum] using five_list_count p (wordExponent w) hz

theorem boundary_word_classes_bound (hp7 : 7 ≤ p) (i : Fin 6) (w : List (Fin 6)) :
    ∃ v : Space p, qNumerator ℤ_[p] (Pi.single i 1+wordExponent w) w.length
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) =
      (p : ℤ)^((w.length/p-5)/5) • fullSection p hp7 v := by
  obtain ⟨v, hv⟩ := boundary_word_coordinates_bound p hp7 i w
  rw [← actual_unscaled_boundary_word_coordinates ℤ_[p] (Parameter.padic_six_unit p hp7), hv]
  exact ⟨v, map_zsmul (fullSection p hp7) _ _⟩

theorem boundary_word_classes_zero_bound (hp7 : 7 ≤ p) (i : Fin 6)
    (w : List (Fin 6)) (hz : ∃ j, wordExponent w j=0) :
    ∃ v : Space p, qNumerator ℤ_[p] (Pi.single i 1+wordExponent w) w.length
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, wordExponent_sum]; simp; omega) =
      (p : ℤ)^((w.length/p-4)/5) • fullSection p hp7 v := by
  obtain ⟨v, hv⟩ := boundary_word_coordinates_zero_bound p hp7 i w hz
  rw [← actual_unscaled_boundary_word_coordinates ℤ_[p] (Parameter.padic_six_unit p hp7), hv]
  exact ⟨v, map_zsmul (fullSection p hp7) _ _⟩

def predecessor (a : Fin 6 → ℕ) (i : Fin 6) : Fin 6 → ℕ := a-Pi.single i 1

theorem single_predecessor (a : Fin 6 → ℕ) (i : Fin 6) (hi : 0<a i) :
    Pi.single i 1+predecessor a i = a := by
  funext j
  by_cases hji : j=i
  · subst j
    simp only [predecessor, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
    omega
  · simp [predecessor, hji]

theorem predecessor_sum (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ j, a j)=n+1)
    (i : Fin 6) (hi : 0<a i) : (∑ j, predecessor a i j)=n := by
  have he := congrArg (fun b : Fin 6 → ℕ => ∑ j, b j) (single_predecessor a i hi)
  simp [Pi.add_apply, Finset.sum_add_distrib, ha] at he
  omega

theorem positive_exists (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ j, a j)=n+1) : ∃ i, 0<a i := by
  by_contra! hn
  have hz : ∀ i, a i=0 := by intro i; have := hn i; omega
  have he : (∑ i, a i)=0 := by simp [hz]
  omega

theorem predecessor_zero (a : Fin 6 → ℕ) (i : Fin 6) (hz : ∃ j, a j=0) :
    ∃ j, predecessor a i j=0 := by
  obtain ⟨j, hj⟩ := hz
  exact ⟨j, by simp [predecessor, hj]⟩

theorem closed_classes_exact (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ j, a j)=n+1) (i : Fin 6) (hi : 0<a i) : ∃ v : Space p,
    qNumerator ℤ_[p] a n (by omega) =
      (p : ℤ)^(blockCount p (predecessor a i)/5) • fullSection p hp7 v := by
  have he := boundary_word_classes_exact p hp7 i (canonicalWord (predecessor a i))
  simpa only [canonicalWord_exponent, single_predecessor a i hi,
    canonicalWord_length, predecessor_sum a n ha i hi] using he

theorem closed_classes_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ j, a j)=n+1) : ∃ v : Space p,
    qNumerator ℤ_[p] a n (by omega) = (p : ℤ)^((n/p-5)/5) • fullSection p hp7 v := by
  obtain ⟨i, hi⟩ := positive_exists a n ha
  have he := boundary_word_classes_bound p hp7 i (canonicalWord (predecessor a i))
  simpa only [canonicalWord_exponent, single_predecessor a i hi,
    canonicalWord_length, predecessor_sum a n ha i hi] using he

theorem closed_classes_zero_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ j, a j)=n+1) (hz : ∃ j, a j=0) : ∃ v : Space p,
    qNumerator ℤ_[p] a n (by omega) = (p : ℤ)^((n/p-4)/5) • fullSection p hp7 v := by
  obtain ⟨i, hi⟩ := positive_exists a n ha
  have he := boundary_word_classes_zero_bound p hp7 i (canonicalWord (predecessor a i))
    (by simpa only [canonicalWord_exponent] using predecessor_zero a i hz)
  simpa only [canonicalWord_exponent, single_predecessor a i hi,
    canonicalWord_length, predecessor_sum a n ha i hi] using he

end WPGammaClosedNumeratorBounds
