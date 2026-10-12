import WPFiniteInversion

open scoped BigOperators

namespace WPFiniteInversion

private theorem sum_full_pairs {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (n : ℕ) :
    (∑ j ∈ Finset.Ico 1 (2 * n + 1), f j) =
      (∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j)) +
        ∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
      rw [Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1 + 1) (by omega)]
      rw [Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1) (by omega)]
      rw [ih]
      simp only [Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega)]
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
        show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      ac_rfl

private theorem sum_full_even_odd {A : Type*} [AddCommMonoid A]
    (p n : ℕ) (hp : p = 2 * n + 1) (f : ℕ → A) :
    (∑ j ∈ Finset.Ico 1 p, f j) =
      (∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j)) +
        ∑ j ∈ Finset.Ico 1 (n + 1), f (p - 2 * j) := by
  have hodd : (∑ j ∈ Finset.Ico 1 (n + 1), f (p - 2 * j)) =
      ∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j - 1) := by
    calc
      _ = ∑ j ∈ Finset.Ico 1 (n + 1), f (2 * (n + 1 - j) - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        congr 1
        omega
      _ = _ := full_cutoff_reflection (n + 1) (fun j => f (2 * j - 1))
  rw [hodd, hp]
  exact sum_full_pairs f n

private theorem sum_full_halves {A : Type*} [AddCommMonoid A]
    (p n : ℕ) (hp : p = 2 * n + 1) (f : ℕ → A) :
    (∑ j ∈ Finset.Ico 1 p, f j) =
      (∑ j ∈ Finset.Ico 1 (n + 1), f j) +
        ∑ j ∈ Finset.Ico 1 (n + 1), f (p - j) := by
  have href : (∑ j ∈ Finset.Ico 1 (n + 1), f (p - j)) =
      ∑ j ∈ Finset.Ico (n + 1) p, f j := by
    have htop : p + 1 - (n + 1) = n + 1 := by omega
    simpa only [htop, Nat.add_sub_cancel] using
      (Finset.sum_Ico_reflect f 1 (m := n + 1) (n := p) (by omega))
  rw [href]
  exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm

private theorem neg_pow_even (p j : ℕ) [Fact p.Prime] (x : ZMod p) :
    (-x) ^ (2 * j) = x ^ (2 * j) := by
  rw [pow_mul, neg_sq, ← pow_mul]

private theorem neg_pow_odd_cutoff (p n j : ℕ) [Fact p.Prime]
    (hp : p = 2 * n + 1) (hj : j ∈ Finset.Ico 1 (n + 1)) (x : ZMod p) :
    (-x) ^ (p - 2 * j) = -(x ^ (p - 2 * j)) := by
  have hj' := Finset.mem_Ico.mp hj
  have he : p - 2 * j = 2 * (n - j) + 1 := by omega
  simp only [he, pow_add, pow_mul, neg_sq, pow_one, mul_neg]

private theorem quadratic_lower_term (p n j : ℕ) [Fact p.Prime]
    (hp : p = 2 * n + 1) (hn : 0 < n)
    (hj : j ∈ Finset.Ico 1 (n + 1)) (x : ZMod p) :
    (x ^ 2) ^ j / (j : ZMod p) ^ 2 =
      4 * (x ^ (2 * j) / ((2 * j : ℕ) : ZMod p) ^ 2) := by
  have hj' := Finset.mem_Ico.mp hj
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : ZMod p) ≠ 0 :=
    denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
  rw [← pow_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]
  ring

private theorem quadratic_upper_term (p n j : ℕ) [Fact p.Prime]
    (hp : p = 2 * n + 1) (hn : 0 < n)
    (hj : j ∈ Finset.Ico 1 (n + 1)) (x : ZMod p) :
    (x ^ 2) ^ (p - j) / ((p - j : ℕ) : ZMod p) ^ 2 =
      (4 * x ^ p) *
        (x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : ZMod p) ^ 2) := by
  have hj' := Finset.mem_Ico.mp hj
  have hjfull : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hjdouble : 2 * j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : ZMod p) ≠ 0 := denominator_ne_zero p j hjfull
  have he : 2 * (p - j) = p + (p - 2 * j) := by omega
  rw [← pow_mul, he, pow_add, reflected_denominator p j hjfull,
    reflected_denominator p (2 * j) hjdouble, neg_sq, neg_sq,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]
  ring

theorem R_quadratic_distribution_of_half (p n : ℕ) [Fact p.Prime]
    (hp : p = 2 * n + 1) (hn : 0 < n) (x : ZMod p) :
    R p (x ^ 2) =
      2 * (1 + x ^ p) * R p x + 2 * (1 - x ^ p) * R p (-x) := by
  let E : ZMod p := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (2 * j) / ((2 * j : ℕ) : ZMod p) ^ 2
  let O : ZMod p := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : ZMod p) ^ 2
  have hR : R p x = E + O := sum_full_even_odd p n hp _
  have hneg : R p (-x) = E - O := by
    unfold R
    rw [sum_full_even_odd p n hp]
    change _ + _ = E - O
    have heven : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (2 * j) / ((2 * j : ℕ) : ZMod p) ^ 2) = E := by
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_pow_even]
    have hodd : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (p - 2 * j) / ((p - 2 * j : ℕ) : ZMod p) ^ 2) = -O := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [neg_pow_odd_cutoff p n j hp hj, neg_div]
    rw [heven, hodd, sub_eq_add_neg]
  have hsquare : R p (x ^ 2) = 4 * E + (4 * x ^ p) * O := by
    unfold R
    rw [sum_full_halves p n hp]
    change _ + _ = 4 * E + (4 * x ^ p) * O
    have hlo : (∑ j ∈ Finset.Ico 1 (n + 1),
        (x ^ 2) ^ j / (j : ZMod p) ^ 2) = 4 * E := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_lower_term p n j hp hn hj x
    have hhi : (∑ j ∈ Finset.Ico 1 (n + 1),
        (x ^ 2) ^ (p - j) / ((p - j : ℕ) : ZMod p) ^ 2) = (4 * x ^ p) * O := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_upper_term p n j hp hn hj x
    rw [hlo, hhi]
  rw [hR, hneg, hsquare]
  ring

theorem R_quadratic_distribution (p : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (x : ZMod p) :
    R p (x ^ 2) =
      2 * (1 + x ^ p) * R p x + 2 * (1 - x ^ p) * R p (-x) := by
  obtain ⟨n, hn⟩ := hpodd
  have hprime : p.Prime := Fact.out
  have hp : p = 2 * n + 1 := by omega
  have hnpos : 0 < n := by have := hprime.two_le; omega
  exact R_quadratic_distribution_of_half p n hp hnpos x

end WPFiniteInversion
