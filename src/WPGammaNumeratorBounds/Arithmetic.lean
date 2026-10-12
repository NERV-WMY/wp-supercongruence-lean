import WPGammaNumeratorBounds.Words
import Mathlib.Data.Nat.ModEq

noncomputable section

namespace WPGammaNumeratorBounds

open scoped BigOperators
open WPGammaIntegralLift WPIntegralBlocks WPResidueQuotient
open WPReview.ResidueNumeratorOperators

theorem floor_list_bound (p : ℕ) (l : List ℕ) :
    l.sum / p ≤ (l.map (fun m => m/p)).sum + (l.length-1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      have he := Nat.add_div_le_div_add_div_add_one a (b+l.sum) p
      simp only [List.sum_cons, List.map_cons, List.length_cons] at ih ⊢
      omega

def lengths (a : Fin 6 → ℕ) (n : ℕ) : List ℕ :=
  [a 0,a 1,a 2,a 3,a 4,a 5,n-∑ i, a i]

theorem lengths_sum (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n) :
    (lengths a n).sum = n := by
  have hs : (∑ i, a i) = a 0+a 1+a 2+a 3+a 4+a 5 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc]
  simp only [lengths, List.sum_cons, List.sum_nil, add_zero]
  omega

variable (p : ℕ)

theorem lengths_floor_sum (a : Fin 6 → ℕ) (n : ℕ) :
    ((lengths a n).map (fun m => m/p)).sum = blockCount p a n := by
  simp [lengths, blockCount, Fin.sum_univ_succ, Nat.add_assoc]

theorem seven_list_count (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n) :
    ((n/p)-6)/5 ≤ blockCount p a n / 5 := by
  have he := floor_list_bound p (lengths a n)
  rw [lengths_sum a n ha, lengths_floor_sum] at he
  have hl : (lengths a n).length = 7 := by simp [lengths]
  rw [hl] at he
  apply Nat.div_le_div_right
  omega

theorem six_list_count (a : Fin 6 → ℕ) (n : ℕ) (ha : (∑ i, a i) ≤ n)
    (hz : ∃ i, a i = 0) : ((n/p)-5)/5 ≤ blockCount p a n / 5 := by
  have hm : 0 ∈ lengths a n := by
    obtain ⟨i, hi⟩ := hz
    fin_cases i <;> dsimp at hi <;> simp_all [lengths]
  have he := floor_list_bound p ((lengths a n).erase 0)
  have hs : ((lengths a n).erase 0).sum = n := by
    have ht := List.sum_erase hm
    simpa only [zero_add, lengths_sum a n ha] using ht
  have hfs : (((lengths a n).erase 0).map (fun m => m/p)).sum = blockCount p a n := by
    have ht := List.sum_map_erase (fun m => m/p) hm
    simpa only [Nat.zero_div, zero_add, lengths_floor_sum] using ht
  have hl : ((lengths a n).erase 0).length = 6 := by
    rw [List.length_erase_of_mem hm]
    simp [lengths]
  rw [hs, hfs, hl] at he
  apply Nat.div_le_div_right
  omega

variable [Fact p.Prime]

theorem coordinate_divisibility_mono (m k : ℕ) (v : Space p) (hmk : m ≤ k)
    (hv : ∃ w : Space p, v = (p : ℤ)^k • w) :
    ∃ w : Space p, v = (p : ℤ)^m • w := by
  obtain ⟨w, hw⟩ := hv
  refine ⟨(p : ℤ)^(k-m) • w, ?_⟩
  rw [hw, smul_smul, ← pow_add, Nat.add_sub_of_le hmk]

theorem strict_coordinates_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) : ∃ w : Space p,
    strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) a n =
      (p : ℤ)^(((n/p)-6)/5) • w :=
  coordinate_divisibility_mono p _ _ _ (seven_list_count p a n ha)
    (strict_coordinates_exact p hp7 a n)

theorem strict_coordinates_zero_exponent_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) (hz : ∃ i, a i = 0) : ∃ w : Space p,
    strictNumeratorCoordinates ℤ_[p] (Parameter.padic_six_unit p hp7) a n =
      (p : ℤ)^(((n/p)-5)/5) • w :=
  coordinate_divisibility_mono p _ _ _ (six_list_count p a n ha hz)
    (strict_coordinates_exact p hp7 a n)

theorem strict_classes_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) : ∃ w : Space p,
    qNumerator ℤ_[p] a n (by omega) =
      (p : ℤ)^(((n/p)-6)/5) • gammaSection p w := by
  obtain ⟨w, hw⟩ := strict_coordinates_bound p hp7 a n ha
  rw [← actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp7) a n ha, hw]
  exact ⟨w, map_zsmul (gammaSection p) _ _⟩

theorem strict_classes_zero_exponent_bound (hp7 : 7 ≤ p) (a : Fin 6 → ℕ) (n : ℕ)
    (ha : (∑ i, a i) ≤ n) (hz : ∃ i, a i = 0) : ∃ w : Space p,
    qNumerator ℤ_[p] a n (by omega) =
      (p : ℤ)^(((n/p)-5)/5) • gammaSection p w := by
  obtain ⟨w, hw⟩ := strict_coordinates_zero_exponent_bound p hp7 a n ha hz
  rw [← actual_unscaled_strict_numerator_coordinates ℤ_[p]
    (Parameter.padic_six_unit p hp7) a n ha, hw]
  exact ⟨w, map_zsmul (gammaSection p) _ _⟩

end WPGammaNumeratorBounds
