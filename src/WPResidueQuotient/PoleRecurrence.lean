import WPResidueQuotient.ActualGeneration
import Mathlib.Tactic

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

/-- The first `L` of the six genuine torus vertices. -/
def prefixExponent (L : ℕ) : Fin 6 → ℕ := fun i => if i.val < L then 1 else 0

@[simp] theorem prefixExponent_zero : prefixExponent 0 = 0 := by
  ext i
  simp [prefixExponent]

theorem prefixExponent_sum (L : ℕ) (hL : L ≤ 6) :
    (∑ i, prefixExponent L i) = L := by
  interval_cases L <;> decide

theorem prefixExponent_at_next (L : ℕ) (hL : L < 6) :
    prefixExponent L ⟨L, hL⟩ = 0 := by simp [prefixExponent]

theorem prefixExponent_succ (L : ℕ) (hL : L < 6) :
    prefixExponent (L + 1) = addNumeratorExponent (prefixExponent L) ⟨L, hL⟩ := by
  ext i
  simp only [prefixExponent, addNumeratorExponent, Pi.add_apply, Pi.single_apply]
  by_cases hi : i = ⟨L, hL⟩
  · subst i
    simp
  · have hv : i.val ≠ L := by
      intro he
      apply hi
      exact Fin.ext he
    split_ifs <;> omega

theorem prefixExponent_six_monomial {R : Type*} [CommRing R] (u : R) :
    actualMonomial u (fun i => (prefixExponent 6 i : ℤ)) = 1 := by
  have he : sixToFive (fun i => (prefixExponent 6 i : ℤ)) = 0 := by
    ext i
    have hi : i.val < 6 := by omega
    simp [sixToFive, prefixExponent, hi]
  change algebraMap (LaurentPolynomial R) (ActualRing u)
    (AddMonoidAlgebra.single (sixToFive (fun i => (prefixExponent 6 i : ℤ))) 1) = 1
  rw [he]
  simp [← AddMonoidAlgebra.one_def]

@[simp] theorem numeratorGenerator_prefix_six {R : Type*} [CommRing R]
    (u : R) (n : ℕ) : numeratorGenerator u (prefixExponent 6) n = factorialPole u n := by
  rw [numeratorGenerator, prefixExponent_six_monomial, one_mul]

def poleClass {R : Type*} [CommRing R] (u : R) :
    ActualRing u →ₗ[R] (ActualRing u ⧸ exactAmbient u) := (exactAmbient u).mkQ

theorem poleClass_exact_zero {R : Type*} [CommRing R] (u : R)
    {g : ActualRing u} (hg : g ∈ exactAmbient u) : poleClass u g = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (exactAmbient u)).mpr hg

theorem poleClass_numerator_reduction {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ)
    (ha : (∑ k, a k) ≤ n + 1) :
    poleClass u (numeratorGenerator u (addNumeratorExponent a i) (n + 1)) =
      v • (poleClass u (numeratorGenerator u a (n + 1)) -
        reductionCoefficient (R := R) a i n • poleClass u (numeratorGenerator u a n)) := by
  rw [numeratorReduction_normalized u v huv, ← reductionCoefficient_image]
  simp only [← Algebra.smul_def, map_add, map_smul, map_sub]
  rw [poleClass_exact_zero u (sum_Dik_mem_exactAmbient u a i n ha), smul_zero, add_zero]

/-- This shifted indexing never introduces Gamma zero. -/
def poleExpression {R : Type*} [CommRing R] (u v : R) : ℕ → ℕ → ActualRing u
  | s, 0 => factorialPole u s
  | s, L + 1 => v • (poleExpression u v (s + 1) L -
      (s + 1 : R) • poleExpression u v s L)

theorem prefixClass_recurrence {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (s L : ℕ) (hL : L < 6) :
    poleClass u (numeratorGenerator u (prefixExponent (L + 1)) (s + L + 1)) =
      v • (poleClass u (numeratorGenerator u (prefixExponent L) (s + 1 + L)) -
        (s + 1 : R) • poleClass u (numeratorGenerator u (prefixExponent L) (s + L))) := by
  rw [prefixExponent_succ L hL]
  have h := poleClass_numerator_reduction u v huv (prefixExponent L) ⟨L, hL⟩ (s + L)
    (by rw [prefixExponent_sum L (by omega)]; omega)
  have hc : reductionCoefficient (R := R) (prefixExponent L) ⟨L, hL⟩ (s + L) = s + 1 := by
    simp only [reductionCoefficient, prefixExponent_at_next, Nat.cast_zero, mul_zero,
      add_zero, ← Nat.cast_sum, prefixExponent_sum L (by omega), Nat.cast_add]
    ring
  rw [hc] at h
  simpa only [Nat.add_assoc, Nat.add_comm L 1, Nat.add_left_comm L 1] using h

theorem prefixClass_expression {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (s L : ℕ) (hL : L ≤ 6) :
    poleClass u (numeratorGenerator u (prefixExponent L) (s + L)) =
      poleClass u (poleExpression u v s L) := by
  induction L generalizing s with
  | zero => simp [poleExpression, numeratorGenerator_zero]
  | succ L ih =>
      rw [show s + (L + 1) = s + L + 1 by omega,
        prefixClass_recurrence u v huv s L (by omega),
        ih (s + 1) (by omega), ih s (by omega)]
      simp only [poleExpression, map_smul, map_sub]

theorem poleExpression_five {R : Type*} [CommRing R] (u v : R) :
    poleExpression u v 0 5 = v ^ 5 •
      (factorialPole u 5 - 15 • factorialPole u 4 + 65 • factorialPole u 3 -
        90 • factorialPole u 2 + 31 • factorialPole u 1 - factorialPole u 0) := by
  simp only [poleExpression, Nat.reduceAdd]
  module

/-- The last vertex at pole six has coefficient zero on the lower pole.
    Thus there is no Gamma-zero endpoint. -/
theorem prefixSix_at_six {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) :
    poleClass u (factorialPole u 5) =
      v • poleClass u (numeratorGenerator u (prefixExponent 5) 5) := by
  have h := poleClass_numerator_reduction u v huv (prefixExponent 5) ⟨5, by decide⟩ 4
    (by rw [prefixExponent_sum 5 (by decide)])
  have hc : reductionCoefficient (R := R) (prefixExponent 5) ⟨5, by decide⟩ 4 = 0 := by
    simp only [reductionCoefficient, prefixExponent_at_next, Nat.cast_zero, mul_zero,
      add_zero, ← Nat.cast_sum, prefixExponent_sum 5 (by decide)]
    norm_num
  rw [hc, zero_smul, sub_zero, ← prefixExponent_succ 5 (by decide),
    numeratorGenerator_prefix_six] at h
  exact h

theorem sixthPole_relation {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) :
    poleClass u (factorialPole u 5) = v ^ 6 •
      poleClass u (factorialPole u 5 - 15 • factorialPole u 4 + 65 • factorialPole u 3 -
        90 • factorialPole u 2 + 31 • factorialPole u 1 - factorialPole u 0) := by
  rw [prefixSix_at_six u v huv]
  have h := prefixClass_expression u v huv 0 5 (by decide)
  simp only [zero_add] at h
  rw [h, poleExpression_five, map_smul, smul_smul]
  congr 1
  ring

theorem inverseSix_power {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) : (6 * u) ^ 6 * v ^ 6 = 1 := by
  rw [← mul_pow, mul_comm (6 * u) v, huv, one_pow]

theorem sixthPole_discriminant_relation {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) :
    (1 - (6 * u) ^ 6) • poleClass u (factorialPole u 5) =
      poleClass u (factorialPole u 0 - 31 • factorialPole u 1 + 90 • factorialPole u 2 -
        65 • factorialPole u 3 + 15 • factorialPole u 4) := by
  have h := congrArg (fun z : ActualRing u ⧸ exactAmbient u => (6 * u) ^ 6 • z)
    (sixthPole_relation u v huv)
  rw [smul_smul, inverseSix_power u v huv, one_smul] at h
  rw [sub_smul, one_smul, h]
  simp only [map_sub, map_add, map_nsmul]
  abel

theorem sixthPole_formula {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    poleClass u (factorialPole u 5) = d •
      poleClass u (factorialPole u 0 - 31 • factorialPole u 1 + 90 • factorialPole u 2 -
        65 • factorialPole u 3 + 15 • factorialPole u 4) := by
  have h := congrArg (fun z : ActualRing u ⧸ exactAmbient u => d • z)
    (sixthPole_discriminant_relation u v huv)
  simpa only [smul_smul, hd, one_smul] using h

theorem prefixExpression_difference_exact {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (s L : ℕ) (hL : L ≤ 6) :
    numeratorGenerator u (prefixExponent L) (s + L) - poleExpression u v s L ∈
      exactAmbient u := by
  apply (Submodule.Quotient.mk_eq_zero (exactAmbient u)).mp
  change poleClass u (numeratorGenerator u (prefixExponent L) (s + L) -
    poleExpression u v s L) = 0
  rw [map_sub, prefixClass_expression u v huv s L hL, sub_self]

theorem poleExpression_mem_of_poles {R : Type*} [CommRing R] (u v : R)
    (P : Submodule R (ActualRing u)) (s L : ℕ)
    (hG : ∀ k ≤ s + L, factorialPole u k ∈ P) : poleExpression u v s L ∈ P := by
  induction L generalizing s with
  | zero => exact hG s (by omega)
  | succ L ih =>
      exact P.smul_mem v (P.sub_mem
        (ih (s + 1) (fun k hk => hG k (by omega)))
        (P.smul_mem (s + 1 : R) (ih s (fun k hk => hG k (by omega)))))

/-- In any genuine submodule quotient the only top pole of this expression
    is its leading coefficient; all remaining poles are strictly lower. -/
theorem poleExpression_top_class {R : Type*} [CommRing R] (u v : R)
    (P : Submodule R (ActualRing u)) (s L : ℕ)
    (hG : ∀ k < s + L, factorialPole u k ∈ P) :
    P.mkQ (poleExpression u v s L) = v ^ L • P.mkQ (factorialPole u (s + L)) := by
  induction L generalizing s with
  | zero => simp [poleExpression]
  | succ L ih =>
      have hlow : P.mkQ (poleExpression u v s L) = 0 :=
        (Submodule.Quotient.mk_eq_zero P).mpr
          (poleExpression_mem_of_poles u v P s L (fun k hk => hG k (by omega)))
      rw [poleExpression, map_smul, map_sub, map_smul, hlow, smul_zero, sub_zero,
        ih (s + 1) (fun k hk => hG k (by omega)), smul_smul]
      rw [show s + 1 + L = s + (L + 1) by omega]
      congr 1
      ring

theorem inversePoleDiscriminant {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    (-(d * (6 * u) ^ 6)) * (1 - v ^ 6) = 1 := by
  calc
    _ = d * ((6 * u) ^ 6 * v ^ 6 - (6 * u) ^ 6) := by ring
    _ = d * (1 - (6 * u) ^ 6) := by rw [inverseSix_power u v huv]
    _ = 1 := hd

theorem higherPole_mem_of_lower {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1)
    (P : Submodule R (ActualRing u)) (hN : exactAmbient u ≤ P) (s : ℕ)
    (hG : ∀ k < s + 6, factorialPole u k ∈ P) : factorialPole u (s + 6) ∈ P := by
  have he := hN (prefixExpression_difference_exact u v huv s 6 (by decide))
  have hz : P.mkQ (factorialPole u (s + 6)) = P.mkQ (poleExpression u v s 6) := by
    have hez := (Submodule.Quotient.mk_eq_zero P).mpr he
    change P.mkQ (numeratorGenerator u (prefixExponent 6) (s + 6) -
      poleExpression u v s 6) = 0 at hez
    rw [numeratorGenerator_prefix_six, map_sub] at hez
    exact sub_eq_zero.mp hez
  rw [poleExpression_top_class u v P s 6 hG] at hz
  have hc : (1 - v ^ 6) • P.mkQ (factorialPole u (s + 6)) = 0 := by
    rw [sub_smul, one_smul, ← hz, sub_self]
  have hcz := congrArg (fun z : ActualRing u ⧸ P => (-(d * (6 * u) ^ 6)) • z) hc
  rw [smul_zero, smul_smul, inversePoleDiscriminant u v d huv hd, one_smul] at hcz
  exact (Submodule.Quotient.mk_eq_zero P).mp hcz

def finitePoleSpan {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  Submodule.span R (Set.range (fun i : Fin 5 => factorialPole u i.val))

def finitePoleBoundarySpan {R : Type*} [CommRing R] (u : R) :
    Submodule R (ActualRing u) := finitePoleSpan u ⊔ Submodule.span R (Set.range (b u))

theorem finitePole_mem {R : Type*} [CommRing R] (u : R) (n : ℕ) (hn : n < 5) :
    factorialPole u n ∈ finitePoleSpan u := Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩

theorem sixthPole_difference_exact {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    factorialPole u 5 - d •
      (factorialPole u 0 - 31 • factorialPole u 1 + 90 • factorialPole u 2 -
        65 • factorialPole u 3 + 15 • factorialPole u 4) ∈ exactAmbient u := by
  apply (Submodule.Quotient.mk_eq_zero (exactAmbient u)).mp
  change poleClass u (factorialPole u 5 - d •
    (factorialPole u 0 - 31 • factorialPole u 1 + 90 • factorialPole u 2 -
      65 • factorialPole u 3 + 15 • factorialPole u 4)) = 0
  rw [map_sub, map_smul, sixthPole_formula u v d huv hd, sub_self]

theorem ambientExact_quotient_eq {R : Type*} [CommRing R] (u : R)
    (g h : FClosed u) (he : (g : ActualRing u) - (h : ActualRing u) ∈ exactAmbient u) :
    (exactSubmodule u).mkQ g = (exactSubmodule u).mkQ h := by
  obtain ⟨n, hn, hne⟩ := he
  have hclosed : n = g - h := by
    apply Subtype.ext
    exact hne
  rw [hclosed] at hn
  have hz := (Submodule.Quotient.mk_eq_zero (exactSubmodule u)).mpr hn
  change (exactSubmodule u).mkQ (g - h) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem sixthPoleCombination_mem {R : Type*} [CommRing R] (u : R) :
    factorialPole u 0 - 31 • factorialPole u 1 + 90 • factorialPole u 2 -
      65 • factorialPole u 3 + 15 • factorialPole u 4 ∈ finitePoleSpan u := by
  have h0 := finitePole_mem u 0 (by decide)
  have h1 := finitePole_mem u 1 (by decide)
  have h2 := finitePole_mem u 2 (by decide)
  have h3 := finitePole_mem u 3 (by decide)
  have h4 := finitePole_mem u 4 (by decide)
  exact (finitePoleSpan u).add_mem
    ((finitePoleSpan u).sub_mem
      ((finitePoleSpan u).add_mem
        ((finitePoleSpan u).sub_mem h0 (nsmul_mem h1 31))
        (nsmul_mem h2 90))
      (nsmul_mem h3 65))
    (nsmul_mem h4 15)

theorem everyPole_finite_generation {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) (n : ℕ) :
    factorialPole u n ∈ exactAmbient u ⊔ finitePoleSpan u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 5
      · exact (le_sup_right : finitePoleSpan u ≤ exactAmbient u ⊔ finitePoleSpan u)
          (finitePole_mem u n hn)
      · by_cases hn5 : n = 5
        · subst n
          have he := (le_sup_left : exactAmbient u ≤ exactAmbient u ⊔ finitePoleSpan u)
            (sixthPole_difference_exact u v d huv hd)
          have hc := (exactAmbient u ⊔ finitePoleSpan u).smul_mem d
            ((le_sup_right : finitePoleSpan u ≤ exactAmbient u ⊔ finitePoleSpan u)
              (sixthPoleCombination_mem u))
          have hs := (exactAmbient u ⊔ finitePoleSpan u).add_mem he hc
          simpa only [sub_add_cancel] using hs
        · obtain ⟨s, rfl⟩ : ∃ s, n = s + 6 := ⟨n - 6, by omega⟩
          exact higherPole_mem_of_lower u v d huv hd (exactAmbient u ⊔ finitePoleSpan u)
            le_sup_left s (fun k hk => ih k hk)

theorem allPoleSpan_finite_generation {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    allPoleSpan u ≤ exactAmbient u ⊔ finitePoleSpan u := by
  apply Submodule.span_le.mpr
  rintro g ⟨n, rfl⟩
  exact everyPole_finite_generation u v d huv hd n

theorem FInterior_finite_generation {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    FInterior u ≤ exactAmbient u ⊔ finitePoleSpan u := by
  apply (FInterior_numerator_generation u v huv).trans
  exact sup_le le_sup_left (allPoleSpan_finite_generation u v d huv hd)

theorem FClosed_finite_generation {R : Type*} [CommRing R] (u v d : R)
    (huv : v * (6 * u) = 1) (hd : d * (1 - (6 * u) ^ 6) = 1) :
    FClosed u ≤ exactAmbient u ⊔ finitePoleBoundarySpan u := by
  apply (FClosed_numerator_generation u v huv).trans
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  rintro g (⟨n, rfl⟩ | ⟨i, rfl⟩)
  · exact (sup_le_sup_left
      (show finitePoleSpan u ≤ finitePoleBoundarySpan u from le_sup_left)
      (exactAmbient u)) (everyPole_finite_generation u v d huv hd n)
  · exact (le_sup_right : finitePoleBoundarySpan u ≤ exactAmbient u ⊔ finitePoleBoundarySpan u)
      ((le_sup_right : Submodule.span R (Set.range (b u)) ≤ finitePoleBoundarySpan u)
        (Submodule.subset_span ⟨i, rfl⟩))

end

end WPResidueQuotient
