import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace WPNativeMomentIntegrality

/-- The literal odd denominator in the finite native primitive. -/
def primitiveDenominator (n a : ℕ) : ℤ := 2 * (a : ℤ) - 6 * (n : ℤ) + 1

/-- The endpoint difference retains both original endpoints. -/
def primitiveWeight (p : ℕ) (m : ℤ) : ℚ :=
  (p : ℚ) * ((2 : ℚ) ^ m - (2 : ℚ) ^ (-m)) / (m : ℚ)

/-- The D1 finite primitive, with its entire polynomial coefficient range. -/
def monomialMoment (p n : ℕ) (L : ℕ → ℤ) : ℚ :=
  2 / (3 * (125 : ℚ) ^ (p + n)) *
    ∑ a ∈ Finset.range (3 * (p + n)),
      (L a : ℚ) * primitiveWeight p (primitiveDenominator n a)

theorem small_integer_valuation_le_one (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) (hbound : m.natAbs < p ^ 2) :
    padicValRat p (m : ℚ) ≤ 1 := by
  have habs : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hv : padicValNat p m.natAbs ≤ 1 := by
    by_contra h
    have hv2 : 2 ≤ padicValNat p m.natAbs := by omega
    have hd : p ^ 2 ∣ m.natAbs := (padicValNat_dvd_iff_le habs).mpr hv2
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero habs) hd
    omega
  rw [padicValRat.of_int]
  change (padicValNat p m.natAbs : ℤ) ≤ 1
  exact_mod_cast hv

theorem prime_over_small_integer_integral (p : ℕ) [Fact p.Prime]
    (m : ℤ) (hm : m ≠ 0) (hbound : m.natAbs < p ^ 2) :
    0 ≤ padicValRat p ((p : ℚ) / (m : ℚ)) := by
  have hp : p.Prime := Fact.out
  rw [padicValRat.div (Nat.cast_ne_zero.mpr hp.ne_zero) (Int.cast_ne_zero.mpr hm),
    padicValRat.self hp.one_lt]
  have hv := small_integer_valuation_le_one p m hm hbound
  omega

theorem primitive_denominator_bounds (p n a : ℕ) (hp : 7 ≤ p)
    (hn : n < p) (ha : a < 3 * (p + n)) :
    primitiveDenominator n a ≠ 0 ∧
      (primitiveDenominator n a).natAbs < p ^ 2 := by
  have hm : primitiveDenominator n a ≠ 0 := by
    unfold primitiveDenominator
    omega
  have hlower : -(6 * (p : ℤ)) < primitiveDenominator n a := by
    unfold primitiveDenominator
    omega
  have hupper : primitiveDenominator n a < 6 * (p : ℤ) := by
    unfold primitiveDenominator
    omega
  have hsmall : (primitiveDenominator n a).natAbs < 6 * p := by
    omega
  have hpoly : 6 * p < p ^ 2 := by nlinarith
  exact ⟨hm, hsmall.trans hpoly⟩

private theorem small_nat_unit (p n : ℕ) (hn : 0 < n) (hnp : n < p) :
    padicValRat p (n : ℚ) = 0 := by
  have hnd : ¬p ∣ n := by
    intro hd
    have hle := Nat.le_of_dvd hn hd
    omega
  simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd, Int.natCast_zero]

private theorem integral_mul (p : ℕ) [Fact p.Prime] (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  rw [padicValRat.mul hx0 hy0]
  omega

private theorem integral_sub (p : ℕ) [Fact p.Prime] (x y : ℚ)
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x - y) := by
  by_cases hxy : x - y = 0
  · simp [hxy]
  have h := padicValRat.min_le_padicValRat_add (p := p)
    (show x + -y ≠ 0 by simpa only [sub_eq_add_neg] using hxy)
  have hyneg : 0 ≤ padicValRat p (-y) := by simpa using hy
  simpa only [sub_eq_add_neg] using (le_min hx hyneg).trans h

private theorem integral_sum (p : ℕ) [Fact p.Prime]
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ a ∈ s, 0 ≤ padicValRat p (f a)) :
    0 ≤ padicValRat p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have h := integral_sub p (f a) (-(∑ b ∈ s, f b)) h1 (by simpa using h2)
    simpa using h

theorem primitive_weight_integral (p n a : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (ha : a < 3 * (p + n)) :
    0 ≤ padicValRat p (primitiveWeight p (primitiveDenominator n a)) := by
  obtain ⟨hm, hb⟩ := primitive_denominator_bounds p n a hp hn ha
  have hdiv := prime_over_small_integer_integral p (primitiveDenominator n a) hm hb
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    simpa using small_nat_unit p 2 (by norm_num) (by omega)
  have hpos : padicValRat p ((2 : ℚ) ^ primitiveDenominator n a) = 0 := by
    rw [padicValRat.zpow, htwo, mul_zero]
  have hneg : padicValRat p ((2 : ℚ) ^ (-primitiveDenominator n a)) = 0 := by
    rw [padicValRat.zpow, htwo, mul_zero]
  have hdiff := integral_sub p ((2 : ℚ) ^ primitiveDenominator n a)
    ((2 : ℚ) ^ (-primitiveDenominator n a)) (by omega) (by omega)
  have h := integral_mul p ((p : ℚ) / (primitiveDenominator n a : ℚ))
    ((2 : ℚ) ^ primitiveDenominator n a - (2 : ℚ) ^ (-primitiveDenominator n a)) hdiv hdiff
  simpa only [primitiveWeight, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem monomial_moment_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (L : ℕ → ℤ) :
    0 ≤ padicValRat p (monomialMoment p n L) := by
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    simpa using small_nat_unit p 2 (by norm_num) (by omega)
  have hthree : padicValRat p (3 : ℚ) = 0 := by
    simpa using small_nat_unit p 3 (by norm_num) (by omega)
  have hfive : padicValRat p (5 : ℚ) = 0 := by
    simpa using small_nat_unit p 5 (by norm_num) (by omega)
  have h125 : padicValRat p (125 : ℚ) = 0 := by
    rw [show (125 : ℚ) = 5 ^ 3 by norm_num, padicValRat.pow, hfive]
    ring
  have hden : padicValRat p (3 * (125 : ℚ) ^ (p + n)) = 0 := by
    rw [padicValRat.mul (by norm_num) (by positivity), padicValRat.pow, hthree, h125]
    ring
  have hfactor : 0 ≤ padicValRat p (2 / (3 * (125 : ℚ) ^ (p + n))) := by
    rw [padicValRat.div (by norm_num) (by positivity), htwo, hden]
    norm_num
  unfold monomialMoment
  apply integral_mul p _ _ hfactor
  apply integral_sum
  intro a ha
  apply integral_mul
  · rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  · exact primitive_weight_integral p n a hp hn (Finset.mem_range.mp ha)

/-- No digit is lost when multiplying a coefficient difference by a D1 moment. -/
theorem monomial_moment_preserves_precision (p n k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (L : ℕ → ℤ) (a b : ℚ)
    (hab : a = b ∨ (k : ℤ) ≤ padicValRat p (a - b)) :
    a * monomialMoment p n L = b * monomialMoment p n L ∨
      (k : ℤ) ≤ padicValRat p (a * monomialMoment p n L - b * monomialMoment p n L) := by
  rcases hab with hab | hab
  · exact Or.inl (congrArg (fun z : ℚ => z * monomialMoment p n L) hab)
  by_cases heq : a = b
  · exact Or.inl (congrArg (fun z : ℚ => z * monomialMoment p n L) heq)
  by_cases hzero : monomialMoment p n L = 0
  · exact Or.inl (by simp [hzero])
  apply Or.inr
  rw [← sub_mul, padicValRat.mul (sub_ne_zero.mpr heq) hzero]
  have hint := monomial_moment_integral p n hp hn L
  omega

private theorem precision_zero_add (p k : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : a = 0 ∨ (k : ℤ) ≤ padicValRat p a)
    (hb : b = 0 ∨ (k : ℤ) ≤ padicValRat p b) :
    a + b = 0 ∨ (k : ℤ) ≤ padicValRat p (a + b) := by
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · simpa using Or.inr ha
  by_cases hab : a + b = 0
  · exact Or.inl hab
  exact Or.inr ((le_min ha hb).trans (padicValRat.min_le_padicValRat_add hab))

private theorem precision_zero_sum (p k : ℕ) [Fact p.Prime]
    (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ n ∈ s, f n = 0 ∨ (k : ℤ) ≤ padicValRat p (f n)) :
    (∑ n ∈ s, f n) = 0 ∨ (k : ℤ) ≤ padicValRat p (∑ n ∈ s, f n) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn]
    exact precision_zero_add p k (f n) (∑ j ∈ s, f j)
      (hf n (Finset.mem_insert_self n s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The complete native coefficient range preserves any finite precision. -/
theorem finite_native_moment_preserves_precision (p k : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (L : ℕ → ℕ → ℤ) (f g : ℕ → ℚ)
    (hfg : ∀ n < p, f n = g n ∨ (k : ℤ) ≤ padicValRat p (f n - g n)) :
    (∑ n ∈ Finset.range p, f n * monomialMoment p n (L n)) =
      (∑ n ∈ Finset.range p, g n * monomialMoment p n (L n)) ∨
    (k : ℤ) ≤ padicValRat p
      ((∑ n ∈ Finset.range p, f n * monomialMoment p n (L n)) -
        (∑ n ∈ Finset.range p, g n * monomialMoment p n (L n))) := by
  have hsum :
      ((∑ n ∈ Finset.range p, f n * monomialMoment p n (L n)) -
        (∑ n ∈ Finset.range p, g n * monomialMoment p n (L n))) =
        ∑ n ∈ Finset.range p, (f n - g n) * monomialMoment p n (L n) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have h := precision_zero_sum p k (Finset.range p)
    (fun n => (f n - g n) * monomialMoment p n (L n)) (by
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have ht := monomial_moment_preserves_precision p n k hp hn' (L n)
        (f n) (g n) (hfg n hn')
      rcases ht with heq | hval
      · exact Or.inl (by rw [sub_mul, heq, sub_self])
      · exact Or.inr (by simpa only [← sub_mul] using hval))
  rw [← hsum] at h
  simpa only [sub_eq_zero] using h

end WPNativeMomentIntegrality
