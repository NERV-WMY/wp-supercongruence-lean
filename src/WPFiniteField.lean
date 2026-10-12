import WPFiniteReflection

open scoped BigOperators
open Polynomial

namespace WPFiniteField

variable {K : Type*} [Field K]

/-- The literal full-cutoff finite logarithm over a field. -/
def ell (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) : K :=
  ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : K)

/-- The literal full-cutoff finite dilogarithm over a field. -/
def R (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) : K :=
  ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : K) ^ 2

theorem denominator_ne_zero (p j : ℕ) [CharP K p]
    (hj : j ∈ Finset.Ico 1 p) : (j : K) ≠ 0 := by
  intro hzero
  have hdvd := (CharP.cast_eq_zero_iff K p j).mp hzero
  have hj' := Finset.mem_Ico.mp hj
  exact Nat.not_dvd_of_pos_of_lt (by omega) hj'.2 hdvd

theorem reflected_denominator (p j : ℕ) [CharP K p]
    (hj : j ∈ Finset.Ico 1 p) : ((p - j : ℕ) : K) = -(j : K) := by
  rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_Ico.mp hj).2), CharP.cast_eq_zero K p]
  simp

private theorem eval₂_ellPolynomial (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (WPFiniteInversion.ellPolynomial p).eval₂ (ZMod.castHom (dvd_refl p) K) x =
      ell p x := by
  simp only [WPFiniteInversion.ellPolynomial, ell, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, map_inv₀, map_natCast, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem eval₂_RPolynomial (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) :
    (WPFiniteInversion.RPolynomial p).eval₂ (ZMod.castHom (dvd_refl p) K) x =
      R p x := by
  simp only [WPFiniteInversion.RPolynomial, R, eval₂_finsetSum, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, map_inv₀, map_pow, map_natCast, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full finite reflection law is evaluated from the zero polynomial, not from point data. -/
theorem R_weight_two_reflection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 5 ≤ p) (x : K) :
    x ^ p * R p x + (1 - x) ^ p * R p (1 - x) = -(ell p x) ^ 2 / 2 := by
  have he := congrArg (fun T : Polynomial (ZMod p) =>
    T.eval₂ (ZMod.castHom (dvd_refl p) K) x)
    (WPFiniteInversion.reflectionDefect_eq_zero p hp)
  simp only [WPFiniteInversion.reflectionDefect, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, eval₂_comp, eval₂_sub, eval₂_one, eval₂_RPolynomial,
    eval₂_ellPolynomial, eval₂_zero, map_inv₀, map_ofNat] at he
  rw [div_eq_mul_inv]
  linear_combination he

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
    (x ^ 2) ^ j / (j : K) ^ 2 =
      4 * (x ^ (2 * j) / ((2 * j : ℕ) : K) ^ 2) := by
  have hj' := Finset.mem_Ico.mp hj
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : K) ≠ 0 :=
    denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
  rw [← pow_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]
  ring

private theorem quadratic_upper_term (p n j : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hn : 0 < n)
    (hj : j ∈ Finset.Ico 1 (n + 1)) (x : K) :
    (x ^ 2) ^ (p - j) / ((p - j : ℕ) : K) ^ 2 =
      (4 * x ^ p) *
        (x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K) ^ 2) := by
  have hj' := Finset.mem_Ico.mp hj
  have hjfull : j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hjdouble : 2 * j ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hden : (j : K) ≠ 0 := denominator_ne_zero p j hjfull
  have he : 2 * (p - j) = p + (p - 2 * j) := by omega
  rw [← pow_mul, he, pow_add, reflected_denominator p j hjfull,
    reflected_denominator p (2 * j) hjdouble, neg_sq, neg_sq,
    Nat.cast_mul, Nat.cast_ofNat]
  field_simp [htwo, hden]
  ring

theorem R_quadratic_distribution_of_half (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p = 2 * n + 1) (hn : 0 < n) (x : K) :
    R p (x ^ 2) =
      2 * (1 + x ^ p) * R p x + 2 * (1 - x ^ p) * R p (-x) := by
  let E : K := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (2 * j) / ((2 * j : ℕ) : K) ^ 2
  let O : K := ∑ j ∈ Finset.Ico 1 (n + 1),
    x ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K) ^ 2
  have hR : R p x = E + O := sum_full_even_odd p n hp _
  have hneg : R p (-x) = E - O := by
    unfold R
    rw [sum_full_even_odd p n hp]
    change _ + _ = E - O
    have heven : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (2 * j) / ((2 * j : ℕ) : K) ^ 2) = E := by
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_pow_even p j]
    have hodd : (∑ j ∈ Finset.Ico 1 (n + 1),
        (-x) ^ (p - 2 * j) / ((p - 2 * j : ℕ) : K) ^ 2) = -O := by
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
        (x ^ 2) ^ j / (j : K) ^ 2) = 4 * E := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_lower_term p n j hp hn hj x
    have hhi : (∑ j ∈ Finset.Ico 1 (n + 1),
        (x ^ 2) ^ (p - j) / ((p - j : ℕ) : K) ^ 2) = (4 * x ^ p) * O := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact quadratic_upper_term p n j hp hn hj x
    rw [hlo, hhi]
  rw [hR, hneg, hsquare]
  ring

theorem R_quadratic_distribution (p : ℕ) [Fact p.Prime] [CharP K p]
    (hpodd : Odd p) (x : K) :
    R p (x ^ 2) =
      2 * (1 + x ^ p) * R p x + 2 * (1 - x ^ p) * R p (-x) := by
  obtain ⟨n, hn⟩ := hpodd
  have hprime : p.Prime := Fact.out
  have hp : p = 2 * n + 1 := by omega
  have hnpos : 0 < n := by have := hprime.two_le; omega
  exact R_quadratic_distribution_of_half p n hp hnpos x


/-- The literal even part of the full finite logarithm. -/
def E (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (ell p t + ell p (-t)) / 2

/-- The literal odd part of the full finite logarithm. -/
def O (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (ell p t - ell p (-t)) / 2

/-- The literal even weight-two endpoint combination. -/
def Ke (p : ℕ) [Fact p.Prime] [CharP K p] (t : K) : K :=
  (R p t + R p (-t) - R p (1 - t) - R p (1 + t)) / 2

/-- Reflection at `t` and `-t`, together with full distribution, without divisions. -/
theorem Ke_cleared_numerator (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    4 * (1 - t ^ (2 * p)) *
        (R p t + R p (-t) - R p (1 - t) - R p (1 + t)) =
      2 * R p (t ^ 2) + 2 * t ^ p * ((ell p t) ^ 2 - (ell p (-t)) ^ 2) +
        2 * ((ell p t) ^ 2 + (ell p (-t)) ^ 2) := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hplus := R_weight_two_reflection p (by omega : 5 ≤ p) t
  rw [sub_pow_char (p := p), one_pow] at hplus
  have hminus := R_weight_two_reflection p (by omega : 5 ≤ p) (-t)
  rw [hodd.neg_pow, sub_neg_eq_add, add_pow_char (p := p), one_pow] at hminus
  have hplus2 := (eq_div_iff htwo).mp hplus
  have hminus2 := (eq_div_iff htwo).mp hminus
  have hpow : t ^ (2 * p) = (t ^ p) ^ 2 := by
    rw [Nat.mul_comm 2 p, pow_mul]
  rw [hpow, R_quadratic_distribution p hodd t]
  linear_combination -2 * (1 + t ^ p) * hplus2 - 2 * (1 - t ^ p) * hminus2

/-- The full finite cleared `K_e` law, including `t = 0, 1, -1`. -/
theorem Ke_cleared_identity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    (1 - t ^ (2 * p)) * Ke p t =
      R p (t ^ 2) / 4 + t ^ p * E p t * O p t +
        ((E p t) ^ 2 + (O p t) ^ 2) / 2 := by
  have htwo : (2 : K) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : K) ≠ 0 :=
    denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have height : (8 : K) ≠ 0 :=
    denominator_ne_zero p 8 (Finset.mem_Ico.mpr (by omega))
  have hE : E p t * 2 = ell p t + ell p (-t) := by
    exact div_mul_cancel₀ _ htwo
  have hO : O p t * 2 = ell p t - ell p (-t) := by
    exact div_mul_cancel₀ _ htwo
  have hK : Ke p t * 2 = R p t + R p (-t) - R p (1 - t) - R p (1 + t) := by
    exact div_mul_cancel₀ _ htwo
  have hlt : ell p t = E p t + O p t := by
    apply mul_right_cancel₀ htwo
    linear_combination -hE - hO
  have hlm : ell p (-t) = E p t - O p t := by
    apply mul_right_cancel₀ htwo
    linear_combination -hE + hO
  have hR4 : R p (t ^ 2) / 4 * 8 = 2 * R p (t ^ 2) := by
    rw [show (8 : K) = 4 * 2 by ring, ← mul_assoc, div_mul_cancel₀ _ hfour]
    ring
  have hlogs : ((E p t) ^ 2 + (O p t) ^ 2) / 2 * 8 =
      4 * ((E p t) ^ 2 + (O p t) ^ 2) := by
    rw [show (8 : K) = 2 * 4 by ring, ← mul_assoc, div_mul_cancel₀ _ htwo]
    ring
  apply mul_right_cancel₀ height
  calc
    ((1 - t ^ (2 * p)) * Ke p t) * 8 =
        4 * (1 - t ^ (2 * p)) * (Ke p t * 2) := by ring
    _ = 4 * (1 - t ^ (2 * p)) *
        (R p t + R p (-t) - R p (1 - t) - R p (1 + t)) := by rw [hK]
    _ = 2 * R p (t ^ 2) + 2 * t ^ p * ((ell p t) ^ 2 - (ell p (-t)) ^ 2) +
        2 * ((ell p t) ^ 2 + (ell p (-t)) ^ 2) := Ke_cleared_numerator p hp t
    _ = (R p (t ^ 2) / 4 + t ^ p * E p t * O p t +
        ((E p t) ^ 2 + (O p t) ^ 2) / 2) * 8 := by
      rw [hlt, hlm, add_mul, add_mul, hR4, hlogs]
      ring


end WPFiniteField

