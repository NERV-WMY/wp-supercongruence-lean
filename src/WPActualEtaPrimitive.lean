import WPActualEtaSupport

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualEtaPole WPActualEtaSupport

namespace WPActualEtaPrimitive

/-- The coefficient-defined nonresonant primitive; every resonant slot is fixed to zero. -/
noncomputable def canonicalPrimitive (p : ℕ) (P : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (P.coeff.support.image (fun j => j + 1))
    (fun k : ℤ => if (p : ℤ) ∣ k then 0 else P.coeff (k - 1) / (k : ℚ)) (by
      intro k hk
      have hP : P.coeff (k - 1) ≠ 0 := by
        intro h
        simp [h] at hk
      exact Finset.mem_image.mpr ⟨k - 1, Finsupp.mem_support_iff.mpr hP, by omega⟩))

noncomputable def resonantSource (p : ℕ) (P : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (P.coeff.filter (fun j => (p : ℤ) ∣ j + 1))

theorem canonicalPrimitive_coeff (p : ℕ) (P : ℚ[T;T⁻¹]) (k : ℤ) :
    (canonicalPrimitive p P).coeff k =
      if (p : ℤ) ∣ k then 0 else P.coeff (k - 1) / (k : ℚ) := by
  simp only [canonicalPrimitive, Finsupp.onFinset_apply]

theorem resonantSource_coeff (p : ℕ) (P : ℚ[T;T⁻¹]) (j : ℤ) :
    (resonantSource p P).coeff j = if (p : ℤ) ∣ j + 1 then P.coeff j else 0 := by
  exact Finsupp.filter_apply _ _ _

theorem finite_monomial_coeff (c : ℚ) (n j : ℤ) :
    (C c * T n).coeff j = if n = j then c else 0 := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_apply

theorem finite_derivative_coeff (P : ℚ[T;T⁻¹]) (j : ℤ) :
    (derivative P).coeff j = ((j + 1 : ℤ) : ℚ) * P.coeff (j + 1) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
    ring
  | C_mul_T n a =>
    rw [derivative_monomial, finite_monomial_coeff, finite_monomial_coeff]
    by_cases hn : n = j + 1
    · subst n
      simp only [add_sub_cancel_right, if_true]
      ring
    · have hnj : n - 1 ≠ j := by omega
      simp only [if_neg hn, if_neg hnj, mul_zero]

theorem canonicalPrimitive_derivative (p : ℕ) (P : ℚ[T;T⁻¹]) :
    derivative (canonicalPrimitive p P) = P - resonantSource p P := by
  ext j
  rw [finite_derivative_coeff, canonicalPrimitive_coeff, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, resonantSource_coeff]
  rw [show j + 1 - 1 = j by omega]
  by_cases h : (p : ℤ) ∣ j + 1
  · simp [h]
  · have hj : j + 1 ≠ 0 := by intro hj; simp [hj] at h
    have hjq : ((j + 1 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hj
    simp only [if_neg h, sub_zero]
    field_simp [hjq]

theorem canonicalPrimitive_resonant_zero (p : ℕ) (P : ℚ[T;T⁻¹]) (k : ℤ) :
    (canonicalPrimitive p P).coeff (k * p) = 0 := by
  rw [canonicalPrimitive_coeff, if_pos]
  exact dvd_mul_left _ _

theorem canonicalPrimitive_bounded (p : ℕ) (P : ℚ[T;T⁻¹]) (lo hi : ℤ)
    (hP : bounded P lo hi) : bounded (canonicalPrimitive p P) (lo + 1) (hi + 1) := by
  intro j hj
  rw [canonicalPrimitive_coeff] at hj
  have hcoeff : P.coeff (j - 1) ≠ 0 := by
    intro h
    simp [h] at hj
  have hb := hP (j - 1) hcoeff
  omega

/-- The canonical primitive of the actual complete pole-subtracted source. -/
noncomputable def Aeta (p N e : ℕ) : ℚ[T;T⁻¹] := canonicalPrimitive p (Peta p N e)

noncomputable def actualResonantSource (p N e : ℕ) : ℚ[T;T⁻¹] :=
  resonantSource p (Peta p N e)

theorem actual_Aeta_coeff (p N e : ℕ) (k : ℤ) :
    (Aeta p N e).coeff k = if (p : ℤ) ∣ k then 0 else
      (Peta p N e).coeff (k - 1) / (k : ℚ) := canonicalPrimitive_coeff p _ k

theorem actual_Aeta_derivative (p N e : ℕ) :
    derivative (Aeta p N e) = Peta p N e - actualResonantSource p N e :=
  canonicalPrimitive_derivative p _

theorem actual_Aeta_resonant_zero (p N e : ℕ) (k : ℤ) :
    (Aeta p N e).coeff (k * p) = 0 := canonicalPrimitive_resonant_zero p _ k

theorem actual_Aeta_full_support (p N e : ℕ) (he : N ≤ e) (hepos : 1 ≤ e) :
    bounded (Aeta p N e) ((N : ℤ) - 3 * (e : ℤ) + 1) (3 * (e : ℤ)) := by
  have h := canonicalPrimitive_bounded p _ _ _ (actual_Peta_full_support p N e he hepos)
  simpa only [Aeta, sub_add_cancel] using h

theorem actual_cutoff_resonance_indices (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : (Peta p ((p - 1) / 2) (p - 1 - p / 6)).coeff j ≠ 0)
    (hres : (p : ℤ) ∣ j + 1) :
    ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) ∧ j = k * p - 1 := by
  have hbound := actual_Peta_cutoff_support p hp j hj
  have hl : -2 * (p : ℤ) < j + 1 := by omega
  have hu : j + 1 < 3 * (p : ℤ) := by omega
  obtain ⟨k, hk⟩ := hres
  have hpz : 0 < (p : ℤ) := by omega
  have hkl : -1 ≤ k := by
    by_contra h
    have : k ≤ -2 := by omega
    nlinarith
  have hku : k ≤ 2 := by
    by_contra h
    have : 3 ≤ k := by omega
    nlinarith
  refine ⟨k, by omega, ?_⟩
  nlinarith

noncomputable def actualResidue (p N e : ℕ) (k : ℤ) : ℚ :=
  (Peta p N e).coeff (k * p - 1)

theorem actual_cutoff_resonant_decomposition (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualResonantSource p ((p - 1) / 2) (p - 1 - p / 6) =
      C (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) (-1)) * T (-(p : ℤ) - 1) +
      C (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 0) * T (-1) +
      C (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 1) * T ((p : ℤ) - 1) +
      C (actualResidue p ((p - 1) / 2) (p - 1 - p / 6) 2) * T (2 * (p : ℤ) - 1) := by
  ext j
  rw [actualResonantSource, resonantSource_coeff]
  by_cases hres : (p : ℤ) ∣ j + 1
  · rw [if_pos hres]
    by_cases hcoeff : (Peta p ((p - 1) / 2) (p - 1 - p / 6)).coeff j = 0
    · simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, finite_monomial_coeff,
        actualResidue, neg_one_mul, zero_mul, one_mul]
      split_ifs <;> simp_all
    · obtain ⟨k, hk, hj⟩ := actual_cutoff_resonance_indices p hp j hcoeff hres
      rcases hk with hk | hk | hk | hk <;> subst k <;> subst j <;>
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, finite_monomial_coeff,
          actualResidue, neg_one_mul, zero_mul, one_mul]
      all_goals split_ifs <;> first | omega | simp only [add_zero, zero_add]
  · rw [if_neg hres]
    have hj1 : -(p : ℤ) - 1 ≠ j := by intro h; subst j; simp at hres
    have hj0 : (-1 : ℤ) ≠ j := by intro h; subst j; simp at hres
    have hjp : (p : ℤ) - 1 ≠ j := by intro h; subst j; simp at hres
    have hj2 : 2 * (p : ℤ) - 1 ≠ j := by intro h; subst j; simp at hres
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, finite_monomial_coeff,
      if_neg hj1, if_neg hj0, if_neg hjp, if_neg hj2, add_zero]

end WPActualEtaPrimitive
