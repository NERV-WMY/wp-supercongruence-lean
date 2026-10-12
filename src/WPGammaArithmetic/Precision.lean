import WPGammaArithmetic.Valuation

open scoped BigOperators

namespace WPGammaArithmetic

theorem rationalCongruent_iff_sub_zero (p m : ℕ) (a b : ℚ) :
    RationalCongruent p m a b ↔ RationalCongruent p m (a - b) 0 := by
  simp only [RationalCongruent, sub_zero, sub_eq_zero]

theorem rationalCongruent_zero_add (p m : ℕ) (hp : p.Prime) (a b : ℚ)
    (ha : RationalCongruent p m a 0) (hb : RationalCongruent p m b 0) :
    RationalCongruent p m (a + b) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rcases ha with ha | ha
  · rw [ha, zero_add]
    exact hb
  rcases hb with hb | hb
  · rw [hb, add_zero]
    exact Or.inr ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  · apply Or.inr
    rw [sub_zero] at ha hb ⊢
    exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add hab)

theorem rationalCongruent_zero_sum (p m : ℕ) (hp : p.Prime)
    (s : Finset ℕ) (a : ℕ → ℚ) :
    (∀ k ∈ s, RationalCongruent p m (a k) 0) →
      RationalCongruent p m (∑ k ∈ s, a k) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _h
      exact Or.inl (by simp)
  | @insert k s hk ih =>
      intro h
      rw [Finset.sum_insert hk]
      exact rationalCongruent_zero_add p m hp (a k) (∑ j ∈ s, a j)
        (h k (Finset.mem_insert_self k s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A literal finite weight loses at most one digit on a coefficient difference. -/
theorem gamma_mul_precision_loss (p m k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hk : k ≤ 3 * p - 1) (a b : ℚ)
    (hab : RationalCongruent p (m + 1) a b) :
    RationalCongruent p m (gamma k * a) (gamma k * b) := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hab with hab | hab
  · exact Or.inl (congrArg (fun q : ℚ => gamma k * q) hab)
  by_cases heq : a = b
  · exact Or.inl (congrArg (fun q : ℚ => gamma k * q) heq)
  · apply Or.inr
    rw [← mul_sub, padicValRat.mul (gamma_ne_zero k) (sub_ne_zero.mpr heq)]
    have hgamma := gamma_valuation_ge_neg_one p k hp hp7 hk
    simp only [Nat.cast_add, Nat.cast_one] at hab
    omega

/-- Coefficient precision survives the finite outer moment with one digit loss. -/
theorem gammaMoment_precision_loss (p L m : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f g : ℕ → ℚ)
    (hfg : ∀ k ≤ L, RationalCongruent p (m + 1) (f k) (g k)) :
    RationalCongruent p m (gammaMoment L f) (gammaMoment L g) := by
  apply (rationalCongruent_iff_sub_zero p m _ _).mpr
  have hsub : gammaMoment L f - gammaMoment L g =
      ∑ k ∈ Finset.range (L + 1), gamma k * (f k - g k) := by
    unfold gammaMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hsub]
  apply rationalCongruent_zero_sum p m hp
  intro k hk
  have hkL : k ≤ L := by
    have := Finset.mem_range.mp hk
    omega
  have hterm := gamma_mul_precision_loss p m k hp hp7 (hkL.trans hL)
    (f k) (g k) (hfg k hkL)
  simpa only [mul_sub] using
    (rationalCongruent_iff_sub_zero p m _ _).mp hterm

/-- The coefficientwise sixth digit gives the scalar fifth digit. -/
theorem gammaMoment_p6_to_p5 (p L : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f g : ℕ → ℚ)
    (hfg : ∀ k ≤ L, RationalCongruent p 6 (f k) (g k)) :
    RationalCongruent p 5 (gammaMoment L f) (gammaMoment L g) :=
  gammaMoment_precision_loss p L 5 hp hp7 hL f g hfg

/-- Multiplying the finite moment by the prime restores integrality. -/
theorem p_mul_gammaMoment_integral (p L : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hL : L ≤ 3 * p - 1) (f : ℕ → ℚ)
    (hf : ∀ k ≤ L, RationalCongruent p 0 (f k) 0) :
    RationalCongruent p 0 ((p : ℚ) * gammaMoment L f) 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hdist : (p : ℚ) * gammaMoment L f =
      ∑ k ∈ Finset.range (L + 1), ((p : ℚ) * gamma k) * f k := by
    unfold gammaMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [hdist]
  apply rationalCongruent_zero_sum p 0 hp
  intro k hk
  have hkL : k ≤ L := by
    have := Finset.mem_range.mp hk
    omega
  rcases hf k hkL with hfk | hfk
  · exact Or.inl (by rw [hfk, mul_zero])
  by_cases hzero : f k = 0
  · exact Or.inl (by rw [hzero, mul_zero])
  · apply Or.inr
    rw [sub_zero, padicValRat.mul (mul_ne_zero hpq (gamma_ne_zero k)) hzero,
      padicValRat.mul hpq (gamma_ne_zero k), padicValRat.self hp.one_lt]
    have hgamma := gamma_valuation_ge_neg_one p k hp hp7 (hkL.trans hL)
    simp only [sub_zero, Nat.cast_zero] at hfk ⊢
    omega

end WPGammaArithmetic
