import WPFifthEntropy
import WPRationalWeightTwo
import WPFinalEndpointAlgebra

open scoped BigOperators

namespace WPFiniteField

variable {K : Type*} [Field K]

theorem R_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (x : ZMod p) :
    R p (ZMod.castHom (dvd_refl p) K x) =
      ZMod.castHom (dvd_refl p) K (WPFiniteInversion.R p x) := by
  simp only [R, WPFiniteInversion.R, map_sum, map_div₀, map_pow, map_natCast]

theorem R_inversion (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) (hx : x ≠ 0) :
    R p x⁻¹ = (x ^ p)⁻¹ * R p x := by
  unfold R
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => x⁻¹ ^ j / (j : K) ^ 2)]
  calc
    (∑ j ∈ Finset.Ico 1 p, x⁻¹ ^ (p - j) / ((p - j : ℕ) : K) ^ 2) =
        ∑ j ∈ Finset.Ico 1 p, (x ^ p)⁻¹ * (x ^ j / (j : K) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inv_pow_sub₀ hx (Nat.le_of_lt (Finset.mem_Ico.mp hj).2),
        reflected_denominator p j hj, neg_sq]
      simp only [div_eq_mul_inv]
      ring
    _ = (x ^ p)⁻¹ * ∑ j ∈ Finset.Ico 1 p, x ^ j / (j : K) ^ 2 := by
      rw [Finset.mul_sum]

theorem R_one_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    R p (1 / 5 : K) = R p 5 / 5 := by
  have hfive : (5 : K) ≠ 0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h5pow : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
  rw [one_div, R_inversion p (5 : K) hfive, h5pow]
  ring

theorem R_fifth_reflection (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    R p (1 / 5) / 5 + 4 * R p (4 / 5) / 5 =
      -((WPFiniteInversion.integerFermatQuotient p 5 : K) -
        8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5) ^ 2 / 2 := by
  have hfive : (5 : K) ≠ 0 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h5pow : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
  have hphase : (1 / 5 : K) ^ p = 1 / 5 := by rw [div_pow, one_pow, h5pow]
  have harg : (1 - 1 / 5 : K) = 4 / 5 := by field_simp [hfive]; ring
  have he := R_weight_two_reflection p (by omega : 5 ≤ p) (1 / 5 : K)
  rw [sub_pow_char (p := p), one_pow, hphase, harg, ell_one_fifth_eq_fermat p hp] at he
  linear_combination he

end WPFiniteField

namespace WPKFifthEndpoint

open WPFiniteField WPFifthEntropy

variable {K : Type*} [Field K]

private theorem fixed_ne_zero (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (hn : n ∣ 2 ^ 8 * 3 ^ 3 * 5 ^ 5) : (n : K) ≠ 0 := by
  intro hz
  have hprime : p.Prime := Fact.out
  have hnzero := (CharP.cast_eq_zero_iff K p n).mp hz
  have hproduct := dvd_trans hnzero hn
  rcases hprime.dvd_mul.mp hproduct with h23 | h5
  · rcases hprime.dvd_mul.mp h23 with h2 | h3
    · have hp2 := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2)
      omega
    · have hp3 := Nat.le_of_dvd (by decide : 0 < 3) (hprime.dvd_of_dvd_pow h3)
      omega
  · have hp5 := Nat.le_of_dvd (by decide : 0 < 5) (hprime.dvd_of_dvd_pow h5)
    omega

private theorem fifth_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) (hu : u ^ 2 = 1 / 5) : (u ^ p) ^ 2 = 1 / 5 := by
  have h5 : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
  calc
    _ = (u ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2]
    _ = (1 / 5 : K) ^ p := by rw [hu]
    _ = 1 / 5 := by rw [div_pow, one_pow, h5]

theorem Ke_at_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Ke p u = 5 * R p (1 / 5) / 16 +
      E p u * (2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) - C p u) / 4 +
        5 * (E p u) ^ 2 / 8 +
          (2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) - C p u) ^ 2 / 8 := by
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  have h2 : (2 : K) ≠ 0 := fixed_ne_zero p 2 hp (by norm_num)
  have h4 : (4 : K) ≠ 0 := fixed_ne_zero p 4 hp (by norm_num)
  have h5 : (5 : K) ≠ 0 := fixed_ne_zero p 5 hp (by norm_num)
  have h8 : (8 : K) ≠ 0 := fixed_ne_zero p 8 hp (by norm_num)
  have h16 : (16 : K) ≠ 0 := fixed_ne_zero p 16 hp (by norm_num)
  have hphase := fifth_phase p u hu
  have hpow : u ^ (2 * p) = 1 / 5 := by rw [Nat.mul_comm 2 p, pow_mul, hphase]
  have he := Ke_cleared_identity p hp u
  rw [hpow, hu, O_at_fifth p hp u hu] at he
  have hcross : u ^ p * E p u * (u ^ p * (2 * q - C p u)) =
      (1 / 5 : K) * E p u * (2 * q - C p u) := by
    calc
      _ = (u ^ p) ^ 2 * E p u * (2 * q - C p u) := by ring
      _ = _ := by rw [hphase]
  have hsquare : (u ^ p * (2 * q - C p u)) ^ 2 =
      (1 / 5 : K) * (2 * q - C p u) ^ 2 := by rw [mul_pow, hphase]
  change (1 - 1 / 5 : K) * Ke p u =
    R p (1 / 5) / 4 + u ^ p * E p u * (u ^ p * (2 * q - C p u)) +
      ((E p u) ^ 2 + (u ^ p * (2 * q - C p u)) ^ 2) / 2 at he
  rw [hcross, hsquare] at he
  have hcoeff : (1 - 1 / 5 : K) = 4 / 5 := by field_simp [h5]; ring
  rw [hcoeff] at he
  have hsolve : Ke p u =
      (R p (1 / 5) / 4 + (1 / 5 : K) * E p u * (2 * q - C p u) +
        ((E p u) ^ 2 + (1 / 5 : K) * (2 * q - C p u) ^ 2) / 2) / (4 / 5) := by
    apply (eq_div_iff (div_ne_zero h4 h5)).mpr
    linear_combination he
  rw [hsolve]
  change _ = 5 * R p (1 / 5) / 16 + E p u * (2 * q - C p u) / 4 +
    5 * (E p u) ^ 2 / 8 + (2 * q - C p u) ^ 2 / 8
  field_simp [h2, h4, h5, h8, h16]
  ring

theorem Ke_at_double_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Ke p (2 * u) = 5 * R p (4 / 5) / 4 +
      2 * (E p u + C p u) * ((WPFiniteInversion.integerFermatQuotient p 2 : K) - 3 * C p u) +
        5 * (E p u + C p u) ^ 2 / 2 +
          ((WPFiniteInversion.integerFermatQuotient p 2 : K) - 3 * C p u) ^ 2 / 2 := by
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  have h2 : (2 : K) ≠ 0 := fixed_ne_zero p 2 hp (by norm_num)
  have h4 : (4 : K) ≠ 0 := fixed_ne_zero p 4 hp (by norm_num)
  have h5 : (5 : K) ≠ 0 := fixed_ne_zero p 5 hp (by norm_num)
  have hphase := fifth_phase p u hu
  have h2pow : (2 * u) ^ p = 2 * u ^ p := by
    have h : (2 : K) ^ p = 2 := by
      simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 2)
    rw [mul_pow, h]
  have hpow : (2 * u) ^ (2 * p) = (4 : K) / 5 := by
    rw [Nat.mul_comm 2 p, pow_mul, h2pow, mul_pow, hphase]
    ring
  have harg : (2 * u) ^ 2 = (4 : K) / 5 := by rw [mul_pow, hu]; ring
  have he := Ke_cleared_identity p hp (2 * u)
  rw [hpow, harg, h2pow, O_at_double_fifth p hp u hu, E_at_double_fifth] at he
  change (1 - 4 / 5 : K) * Ke p (2 * u) =
    R p (4 / 5) / 4 + (2 * u ^ p) * (E p u + C p u) * (u ^ p * (q - 3 * C p u)) +
      ((E p u + C p u) ^ 2 + (u ^ p * (q - 3 * C p u)) ^ 2) / 2 at he
  have hcross : (2 * u ^ p) * (E p u + C p u) * (u ^ p * (q - 3 * C p u)) =
      (2 / 5 : K) * (E p u + C p u) * (q - 3 * C p u) := by
    calc
      _ = 2 * (u ^ p) ^ 2 * (E p u + C p u) * (q - 3 * C p u) := by ring
      _ = _ := by rw [hphase]; ring
  have hsquare : (u ^ p * (q - 3 * C p u)) ^ 2 =
      (1 / 5 : K) * (q - 3 * C p u) ^ 2 := by rw [mul_pow, hphase]
  rw [hcross, hsquare] at he
  have hcoeff : (1 - 4 / 5 : K) = 1 / 5 := by field_simp [h5]; ring
  rw [hcoeff] at he
  have hsolve : Ke p (2 * u) =
      (R p (4 / 5) / 4 + (2 / 5 : K) * (E p u + C p u) * (q - 3 * C p u) +
        ((E p u + C p u) ^ 2 + (1 / 5 : K) * (q - 3 * C p u) ^ 2) / 2) / (1 / 5) := by
    apply (eq_div_iff (div_ne_zero one_ne_zero h5)).mpr
    linear_combination he
  rw [hsolve]
  change _ = 5 * R p (4 / 5) / 4 + 2 * (E p u + C p u) * (q - 3 * C p u) +
    5 * (E p u + C p u) ^ 2 / 2 + (q - 3 * C p u) ^ 2 / 2
  field_simp [h2, h4, h5]
  ring

theorem R_fifth_contribution (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    5 * R p (4 / 5 : K) / 4 - 5 * R p (1 / 5 : K) / 16 =
      -R p (5 : K) / 8 - 25 *
        ((WPFiniteInversion.integerFermatQuotient p 5 : K) -
          8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5) ^ 2 / 32 := by
  have h2 : (2 : K) ≠ 0 := fixed_ne_zero p 2 hp (by norm_num)
  have h4 : (4 : K) ≠ 0 := fixed_ne_zero p 4 hp (by norm_num)
  have h5 : (5 : K) ≠ 0 := fixed_ne_zero p 5 hp (by norm_num)
  have h8 : (8 : K) ≠ 0 := fixed_ne_zero p 8 hp (by norm_num)
  have h16 : (16 : K) ≠ 0 := fixed_ne_zero p 16 hp (by norm_num)
  have h32 : (32 : K) ≠ 0 := fixed_ne_zero p 32 hp (by norm_num)
  have he := R_fifth_reflection (K := K) p hp
  have hr4 : R p (4 / 5 : K) =
      (-((WPFiniteInversion.integerFermatQuotient p 5 : K) -
        8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) / 5) ^ 2 / 2 -
          R p (1 / 5 : K) / 5) / (4 / 5) := by
    apply (eq_div_iff (div_ne_zero h4 h5)).mpr
    linear_combination he
  rw [hr4, R_one_fifth p hp]
  field_simp [h2, h4, h5, h8, h16, h32]
  ring

theorem Ke_difference_retained (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Ke p (2 * u) - Ke p u =
      -R p (5 : K) / 8 - 5 * (WPFiniteInversion.integerFermatQuotient p 5 : K) ^ 2 / 16 +
        (WPFiniteInversion.integerFermatQuotient p 2 : K) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) -
        11 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 / 10 -
        (WPFiniteInversion.integerFermatQuotient p 2 : K) * C p u / 5 +
        4 * (C p u) ^ 2 / 5 := by
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  have h2 : (2 : K) ≠ 0 := fixed_ne_zero p 2 hp (by norm_num)
  have h4 : (4 : K) ≠ 0 := fixed_ne_zero p 4 hp (by norm_num)
  have h5 : (5 : K) ≠ 0 := fixed_ne_zero p 5 hp (by norm_num)
  have h8 : (8 : K) ≠ 0 := fixed_ne_zero p 8 hp (by norm_num)
  have h10 : (10 : K) ≠ 0 := fixed_ne_zero p 10 hp (by norm_num)
  have h16 : (16 : K) ≠ 0 := fixed_ne_zero p 16 hp (by norm_num)
  have h32 : (32 : K) ≠ 0 := fixed_ne_zero p 32 hp (by norm_num)
  change _ = -R p (5 : K) / 8 - 5 * k ^ 2 / 16 + q * k - 11 * q ^ 2 / 10 -
    q * C p u / 5 + 4 * (C p u) ^ 2 / 5
  calc
    _ = (5 * R p (4 / 5) / 4 - 5 * R p (1 / 5) / 16) +
        15 * (E p u) ^ 2 / 8 + 3 * q * E p u / 2 - 3 * C p u * E p u / 4 -
          q * C p u / 2 + 7 * (C p u) ^ 2 / 8 := by
      rw [Ke_at_double_fifth p hp u hu, Ke_at_fifth p hp u hu]
      field_simp [h2, h4, h8, h16]
      dsimp only [q]
      ring
    _ = _ := by
      rw [R_fifth_contribution p hp, E_at_fifth p hp u hu]
      dsimp only [q, k]
      field_simp [h2, h4, h5, h8, h10, h16, h32]
      ring

theorem C_castHom (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    C p u = ZMod.castHom (dvd_refl p) K
      (((B p 2 - B p 1 : ℤ) : ZMod p) / 5) := by
  have h5 : (5 : K) ≠ 0 := fixed_ne_zero p 5 hp (by norm_num)
  have h5pow : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using (natCast_pow_char (K := K) p 5)
  have hb1 := B_evaluation p hp 1 u hu
  have hb2 := B_evaluation p hp 2 u hu
  rw [h5pow] at hb1 hb2
  norm_num only [Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat, one_mul] at hb1 hb2
  simp only [map_div₀, map_sub, map_intCast, map_ofNat, Int.cast_sub]
  apply mul_right_cancel₀ h5
  rw [div_mul_cancel₀ _ h5]
  unfold C
  linear_combination -hb2 + hb1

theorem Ke_difference (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Ke p (2 * u) - Ke p u =
      7 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 / 10 -
        (WPFiniteInversion.integerFermatQuotient p 2 : K) * C p u / 5 +
        4 * (C p u) ^ 2 / 5 + R p (-2 : K) / 3 + R p (16 : K) / 60 := by
  let q : ZMod p := WPFiniteInversion.integerFermatQuotient p 2
  let k : ZMod p := WPFiniteInversion.integerFermatQuotient p 5
  let c : ZMod p := ((B p 2 - B p 1 : ℤ) : ZMod p) / 5
  have hrel : WPFiniteInversion.R p 16 + 20 * WPFiniteInversion.R p (-2) +
      15 * WPFiniteInversion.R p 5 / 2 = -108 * q ^ 2 + 60 * q * k - 75 * k ^ 2 / 4 := by
    have he := WPFiniteInversion.rational_weight_two_aggregate p hp
    dsimp only [q, k]
    linear_combination he
  have he := WPFinalEndpointAlgebra.real_endpoint_elimination p hp q k c
    (WPFiniteInversion.R p (-2)) (WPFiniteInversion.R p 5) (WPFiniteInversion.R p 16) hrel
  have hm := congrArg (ZMod.castHom (dvd_refl p) K) he
  dsimp only [q, k, c] at hm
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_div₀, map_intCast,
    map_ofNat, ← R_castHom, ← C_castHom p hp u hu] at hm
  rw [Ke_difference_retained p hp u hu]
  exact hm

end WPKFifthEndpoint
