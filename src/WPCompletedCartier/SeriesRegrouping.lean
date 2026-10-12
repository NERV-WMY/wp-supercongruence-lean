import WPCompletedCartier.AdicSeries

namespace WPCompletedCartier.SeriesRegrouping

noncomputable section
open scoped BigOperators
open WPResidueQuotient.Adic
open WPCompletedCartier.AdicSeries

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def shift (d : ℕ) (a : ℕ → M) (j : ℕ) : M :=
  if d ≤ j then a (j - d) else 0

theorem shift_eventual (p : R) (d : ℕ) (a : ℕ → M)
    (ha : EventuallyDivisible p a) : EventuallyDivisible p (shift d a) := by
  intro n
  obtain ⟨K, hK⟩ := ha n
  refine ⟨d + K, ?_⟩
  intro j hj
  rw [shift, if_pos (by omega)]
  exact hK _ (by omega)

theorem sum_shift (p : R) (d : ℕ) (a : ℕ → M)
    (ha : EventuallyDivisible p a) :
    sum p (shift d a) (shift_eventual p d a ha) = sum p a ha := by
  rw [sum_eq_partialSum_add_tail p (shift d a) (shift_eventual p d a ha) d]
  have hzero : partialSum (shift d a) d = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact if_neg (by have := Finset.mem_range.mp hj; omega)
  rw [hzero, map_zero, zero_add]
  congr 1
  funext j
  simp only [shift, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem finset_eventual {I : Type*} (p : R) (s : Finset I) (a : I → ℕ → M)
    (ha : ∀ i, EventuallyDivisible p (a i)) :
    EventuallyDivisible p (fun j => ∑ i ∈ s, a i j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      exact ⟨0, fun j _ => by simp⟩
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact eventuallyDivisible_add p _ _ (ha i) ih

theorem sum_finset {I : Type*} (p : R) (s : Finset I) (a : I → ℕ → M)
    (ha : ∀ i, EventuallyDivisible p (a i)) :
    sum p (fun j => ∑ i ∈ s, a i j) (finset_eventual p s a ha) =
      ∑ i ∈ s, sum p (a i) (ha i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply sum_unique
      simpa only [Finset.sum_empty, partialSum, Finset.sum_const_zero, map_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : Completion p M))
          Filter.atTop (nhds 0))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [sum_add p (a i) (fun j => ∑ k ∈ s, a k j) (ha i)
        (finset_eventual p s a ha)]
      rw [ih]

end

end WPCompletedCartier.SeriesRegrouping
