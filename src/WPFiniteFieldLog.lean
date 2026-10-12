import WPFiniteField
import WPFiniteEntropy

open scoped BigOperators
open Polynomial

namespace WPFiniteField

variable {K : Type*} [Field K]

private theorem eval₂_log_polynomial (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (WPFiniteInversion.ellPolynomial p).eval₂ (ZMod.castHom (dvd_refl p) K) x =
      ell p x := by
  simp only [WPFiniteInversion.ellPolynomial, ell, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, map_inv₀, map_natCast, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ell_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 ≤ p) (x : K) :
    ell p (1 - x) = ell p x := by
  have he := congrArg (fun T : Polynomial (ZMod p) =>
    T.eval₂ (ZMod.castHom (dvd_refl p) K) x)
    (WPFiniteInversion.ellPolynomial_reflection_eq p hp)
  simpa only [eval₂_comp, eval₂_sub, eval₂_one, eval₂_X, eval₂_log_polynomial] using he

theorem ell_inversion (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) (hx : x ≠ 0) :
    ell p x⁻¹ = -(x ^ p)⁻¹ * ell p x := by
  unfold ell
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => x⁻¹ ^ j / (j : K))]
  calc
    (∑ j ∈ Finset.Ico 1 p, x⁻¹ ^ (p - j) / ((p - j : ℕ) : K)) =
        ∑ j ∈ Finset.Ico 1 p, -(x ^ p)⁻¹ * (x ^ j / (j : K)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inv_pow_sub₀ hx (Nat.le_of_lt (Finset.mem_Ico.mp hj).2),
        reflected_denominator p j hj]
      simp only [div_eq_mul_inv, inv_neg]
      ring
    _ = -(x ^ p)⁻¹ * ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : K) := by rw [Finset.mul_sum]

theorem ell_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (x : ZMod p) :
    ell p (ZMod.castHom (dvd_refl p) K x) =
      ZMod.castHom (dvd_refl p) K (WPFiniteInversion.ell p x) := by
  simp only [ell, WPFiniteInversion.ell, map_sum, map_div₀, map_pow, map_natCast]

theorem natCast_pow_char (p a : ℕ) [Fact p.Prime] [CharP K p] :
    (a : K) ^ p = a := by
  have he := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (a : ZMod p))
  simpa only [map_pow, map_natCast] using he

theorem ell_neg_four_eq_fermat (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ell p (-4) = 8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
      5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) := by
  have he := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.ell_neg_four_eq_fermat p (by omega : 7 ≤ p))
  simpa only [← ell_castHom, map_neg, map_ofNat, map_sub, map_mul, map_intCast] using he

theorem ell_one_fifth_eq_fermat (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    ell p (1 / 5) = (WPFiniteInversion.integerFermatQuotient p 5 : K) -
      8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5 := by
  have hfive : (5 : K) ≠ 0 :=
    denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have href := ell_reflection p (by omega : 3 ≤ p) (5 : K)
  rw [show (1 - 5 : K) = -4 by ring, ell_neg_four_eq_fermat p hp] at href
  have h5pow : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
  rw [one_div, ell_inversion p (5 : K) hfive, h5pow, ← href]
  field_simp [hfive]
  ring

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
      _ = _ := WPFiniteInversion.full_cutoff_reflection (n + 1) (fun j => f (2 * j - 1))
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

private theorem neg_pow_even (p j : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (-x) ^ (2 * j) = x ^ (2 * j) := by
  rw [pow_mul, neg_sq, ← pow_mul]

private theorem neg_pow_odd_cutoff (p n j : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hj : j ∈ Finset.Ico 1 (n + 1)) (x : K) :
    (-x) ^ (p - 2 * j) = -(x ^ (p - 2 * j)) := by
  have hj' := Finset.mem_Ico.mp hj
  have he : p - 2 * j = 2 * (n - j) + 1 := by omega
  simp only [he, pow_add, pow_mul, neg_sq, pow_one, mul_neg]

private theorem quadratic_lower_term (p n j : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hn : 0 < n)
    (hj : j ∈ Finset.Ico 1 (n + 1)) (x : K) :
    (x ^ 2) ^ j / (j : K) =
      2 * (x ^ (2 * j) / ((2 * j : ℕ) : K)) := by
  have hj' := Finset.mem_Ico.mp hj
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : K) ≠ 0 :=
    denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
  rw [← pow_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]

private theorem quadratic_upper_term (p n j : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hn : 0 < n)
    (hj : j ∈ Finset.Ico 1 (n + 1)) (x : K) :
    (x ^ 2) ^ (p - j) / ((p - j : ℕ) : K) =
      (2 * x ^ p) *
        (x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K)) := by
  have hj' := Finset.mem_Ico.mp hj
  have hjfull : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hjdouble : 2 * j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : K) ≠ 0 := denominator_ne_zero p j hjfull
  have he : 2 * (p - j) = p + (p - 2 * j) := by omega
  rw [← pow_mul, he, pow_add, reflected_denominator p j hjfull,
    reflected_denominator p (2 * j) hjdouble,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]

theorem ell_quadratic_distribution_of_half (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hn : 0 < n) (x : K) :
    ell p (x ^ 2) =
      (1 + x ^ p) * ell p x + (1 - x ^ p) * ell p (-x) := by
  let E : K := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (2 * j) / ((2 * j : ℕ) : K)
  let O : K := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K)
  have hR : ell p x = E + O := sum_full_even_odd p n hp _
  have hneg : ell p (-x) = E - O := by
    unfold ell
    rw [sum_full_even_odd p n hp]
    change _ + _ = E - O
    have heven : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (2 * j) / ((2 * j : ℕ) : K)) = E := by
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_pow_even p j]
    have hodd : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K)) = -O := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [neg_pow_odd_cutoff p n j hp hj, neg_div]
    rw [heven, hodd, sub_eq_add_neg]
  have hsquare : ell p (x ^ 2) = 2 * E + (2 * x ^ p) * O := by
    unfold ell
    rw [sum_full_halves p n hp]
    change _ + _ = 2 * E + (2 * x ^ p) * O
    have hlo : (∑ j ∈ Finset.Ico 1 (n + 1),
        (x ^ 2) ^ j / (j : K)) = 2 * E := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_lower_term p n j hp hn hj x
    have hhi : (∑ j ∈ Finset.Ico 1 (n + 1),
        (x ^ 2) ^ (p - j) / ((p - j : ℕ) : K)) = (2 * x ^ p) * O := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_upper_term p n j hp hn hj x
    rw [hlo, hhi]
  rw [hR, hneg, hsquare]
  ring

theorem ell_quadratic_distribution (p : ℕ) [Fact p.Prime] [CharP K p]
    (hpodd : Odd p) (x : K) :
    ell p (x ^ 2) =
      (1 + x ^ p) * ell p x + (1 - x ^ p) * ell p (-x) := by
  obtain ⟨n, hn⟩ := hpodd
  have hprime : p.Prime := Fact.out
  have hp : p = 2 * n + 1 := by omega
  have hnpos : 0 < n := by have := hprime.two_le; omega
  exact ell_quadratic_distribution_of_half p n hp hnpos x



end WPFiniteField

