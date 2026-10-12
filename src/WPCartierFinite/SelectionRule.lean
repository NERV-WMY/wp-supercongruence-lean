import WPCartierFinite.Support
import Mathlib.Data.Int.ModEq

namespace WPCartierFinite
noncomputable section

theorem exponentScale_range_six_iff (p : ℕ) (b : Fin 6 → ℤ) :
    qSix b ∈ Set.range (exponentScale p) ↔
      ∀ i, (p : ℤ) ∣ b i - b (Fin.last 5) := by
  constructor
  · rintro ⟨x, hx⟩ i
    refine Fin.lastCases (by simp) (fun j => ?_) i
    refine ⟨x j, ?_⟩
    exact (congrFun hx j).symm
  · intro h
    let x : Exponents := fun i => (b i.castSucc - b (Fin.last 5)) / (p : ℤ)
    refine ⟨x, ?_⟩
    ext i
    exact Int.mul_ediv_cancel_of_dvd (h i.castSucc)

theorem exponentScale_range_six_congruent (p : ℕ) (b : Fin 6 → ℤ) :
    qSix b ∈ Set.range (exponentScale p) ↔
      ∀ i, Int.ModEq (p : ℤ) (b (Fin.last 5)) (b i) := by
  simp only [exponentScale_range_six_iff, Int.modEq_iff_dvd]

def dividedCanonicalSix (p : ℕ) (b : Fin 6 → ℤ) : Fin 6 → ℤ :=
  fun i => normalizeSix b i / (p : ℤ)

@[simp] theorem kappa_one (p : ℕ) (hp : 0 < p) : kappa p hp (1 : LaurentPolynomial) = 1 := by
  simpa [AddMonoidAlgebra.one_def] using kappa_scaled_single p hp 0 1

@[simp] theorem kappa_phi (p : ℕ) (hp : 0 < p) (H : LaurentPolynomial) :
    kappa p hp (phi p H) = H := by
  simpa using kappa_mul_phi p hp 1 H

theorem dividedCanonicalSix_selected (p : ℕ) (hp : 0 < p) (b : Fin 6 → ℤ)
    (x : Exponents) (hx : exponentScale p x = qSix b) :
    dividedCanonicalSix p b = canonicalSix x := by
  have hn : normalizeSix b = fun i => (p : ℤ) * canonicalSix x i := by
    rw [← canonicalSix_qSix, ← hx, canonicalSix_scale p hp]
  ext i
  simp only [dividedCanonicalSix, hn]
  exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (Nat.ne_of_gt hp))

theorem kappa_six_monomial (p : ℕ) (hp : 0 < p) (b : Fin 6 → ℤ) (c : ℚ) :
    kappa p hp (AddMonoidAlgebra.single (qSix b) c) =
      if ∀ i, Int.ModEq (p : ℤ) (b (Fin.last 5)) (b i) then
        AddMonoidAlgebra.single (qSix (dividedCanonicalSix p b)) c else 0 := by
  classical
  by_cases h : ∀ i, Int.ModEq (p : ℤ) (b (Fin.last 5)) (b i)
  · rw [if_pos h]
    obtain ⟨x, hx⟩ := (exponentScale_range_six_congruent p b).mpr h
    rw [← hx, kappa_scaled_single]
    rw [dividedCanonicalSix_selected p hp b x hx, qSix_canonicalSix]
  · rw [if_neg h]
    exact kappa_single_not_selected p hp (qSix b) c
      (fun hr => h ((exponentScale_range_six_congruent p b).mp hr))

theorem kappa_support_from_ordinary (p : ℕ) (hp : 0 < p) (P : LaurentPolynomial) (d : ℕ)
    (hP : ∀ x ∈ P.coeff.support, ∃ b : Fin 6 → ℕ,
      qSix (fun i => (b i : ℤ)) = x ∧ ∑ i, b i ≤ p * d) :
    SupportBound (kappa p hp P) d := by
  apply kappa_support_closed
  intro x hx
  obtain ⟨b, hb, hd⟩ := hP x hx
  rw [← hb]
  exact (canonicalDegree_le_ordinary b).trans hd

theorem kappa_support_from_ordinary_strict (p : ℕ) (hp : 0 < p)
    (P : LaurentPolynomial) (d : ℕ)
    (hP : ∀ x ∈ P.coeff.support, ∃ b : Fin 6 → ℕ,
      qSix (fun i => (b i : ℤ)) = x ∧ ∑ i, b i < p * d) :
    ∀ x ∈ (kappa p hp P).coeff.support, canonicalDegree x < d := by
  apply kappa_support_strict
  intro x hx
  obtain ⟨b, hb, hd⟩ := hP x hx
  rw [← hb]
  exact lt_of_le_of_lt (canonicalDegree_le_ordinary b) hd

end
end WPCartierFinite
