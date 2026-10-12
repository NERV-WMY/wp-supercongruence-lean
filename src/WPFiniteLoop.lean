import WPKFifthEndpoint
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators

namespace WPFiniteLoop

variable {K : Type*} [Field K]

def L (n : ℕ) (x : K) : K := ∑ j ∈ Finset.Ico 1 (n + 1), x ^ j / (j : K)

def D (n : ℕ) (x y : K) : K :=
  ∑ j ∈ Finset.Ico 1 (n + 1),
    ∑ k ∈ Finset.Ico 1 (j + 1), x ^ k * y ^ (j - k) / ((k : K) * (j : K))

def S (p : ℕ) (x y : K) : K := D ((p - 1) / 2) (x ^ 2) (y ^ 2)

def A (p : ℕ) (t : K) : K := S p (2 * t) 1 - S p t (1 / 2)

def B (p : ℕ) (t : K) : K := S p (2 * t) 2 - S p t 1

def Chi (p : ℕ) (t : K) : K :=
  S p t t + S p (2 * t) (2 * t) - S p (2 * t) t - S p t (2 * t)

theorem D_denominator_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (j k : ℕ) (hj : j ∈ Finset.Ico 1 ((p - 1) / 2 + 1))
    (hk : k ∈ Finset.Ico 1 (j + 1)) : (k : K) * (j : K) ≠ 0 := by
  have hj' := Finset.mem_Ico.mp hj
  have hk' := Finset.mem_Ico.mp hk
  exact mul_ne_zero
    (WPFiniteField.denominator_ne_zero p k (Finset.mem_Ico.mpr (by omega)))
    (WPFiniteField.denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega)))

theorem D_zero_left (n : ℕ) (y : K) : D n (0 : K) y = 0 := by
  unfold D
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  have hkpos := (Finset.mem_Ico.mp hk).1
  simp only [zero_pow (by omega : k ≠ 0), zero_mul, zero_div]

theorem loop_origin (p : ℕ) : A p (0 : K) - B p (0 : K) + Chi p (0 : K) = 0 := by
  unfold A B Chi S
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), D_zero_left,
    sub_self, add_zero]

private def row (a : K) (m j : ℕ) : K :=
  (1 + a ^ m - a ^ j - a ^ m * (a⁻¹) ^ j) / ((m : K) * (j : K))

private theorem loop_tail (n : ℕ) (a s : K) (ha : a ≠ 0) :
    D n (a * s) 1 - D n s a⁻¹ - D n (a * s) a + D n s 1 =
      ∑ m ∈ Finset.Ico 1 (n + 1), ∑ j ∈ Finset.Ico m (n + 1),
        s ^ m * row a m j := by
  rw [Finset.sum_Ico_Ico_comm]
  unfold D
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro m hm
  have hmj : m ≤ j := by have := Finset.mem_Ico.mp hm; omega
  have hp : (a * s) ^ m * a ^ (j - m) = a ^ j * s ^ m := by
    rw [mul_pow]
    calc
      _ = (a ^ m * a ^ (j - m)) * s ^ m := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hmj]
  simp only [one_pow, mul_one]
  rw [hp, inv_pow_sub₀ ha hmj]
  simp only [row, mul_pow, inv_pow, div_eq_mul_inv]
  ring

private theorem loop_head (n : ℕ) (a s : K) (ha : a ≠ 0) :
    D n s s + D n (a * s) (a * s) - D n (a * s) s - D n s (a * s) =
      ∑ m ∈ Finset.Ico 1 (n + 1), ∑ j ∈ Finset.Ico 1 (m + 1),
        s ^ m * row a m j := by
  unfold D
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_Ico.mp hj; omega
  have hs : s ^ j * s ^ (m - j) = s ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hjm]
  have ha' : a ^ j * a ^ (m - j) = a ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hjm]
  have hsub : a ^ (m - j) = a ^ m * (a⁻¹) ^ j := by
    rw [pow_sub₀ a ha hjm, inv_pow]
  simp only [mul_pow]
  calc
    _ = s ^ m * (1 + a ^ m - a ^ j - a ^ (m - j)) /
        ((j : K) * (m : K)) := by
      simp only [div_eq_mul_inv]
      linear_combination (1 + a ^ m - a ^ j - a ^ (m - j)) *
        (((j : K) * (m : K))⁻¹) * hs +
        (s ^ j * s ^ (m - j)) * (((j : K) * (m : K))⁻¹) * ha'
    _ = _ := by rw [hsub]; simp only [row, div_eq_mul_inv, mul_inv_rev]; ring

private theorem row_diagonal (a : K) (ha : a ≠ 0) (m : ℕ) : row a m m = 0 := by
  simp only [row, ← mul_pow, mul_inv_cancel₀ ha, one_pow]
  ring

private theorem row_full (n m : ℕ) (a : K) :
    (∑ j ∈ Finset.Ico 1 (n + 1), row a m j) =
      ((1 + a ^ m) * L n 1 - L n a - a ^ m * L n a⁻¹) / (m : K) := by
  unfold row L
  simp only [one_pow, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem loop_finite_primitive (n : ℕ) (a s : K) (ha : a ≠ 0) :
    D n (a * s) 1 - D n s a⁻¹ - D n (a * s) a + D n s 1 +
      (D n s s + D n (a * s) (a * s) - D n (a * s) s - D n s (a * s)) =
        (L n 1 - L n a) * L n s + (L n 1 - L n a⁻¹) * L n (a * s) := by
  rw [loop_tail n a s ha, loop_head n a s ha, ← Finset.sum_add_distrib]
  have hjoin (m : ℕ) (hm : m ∈ Finset.Ico 1 (n + 1)) :
      (∑ j ∈ Finset.Ico m (n + 1), s ^ m * row a m j) +
        (∑ j ∈ Finset.Ico 1 (m + 1), s ^ m * row a m j) =
          s ^ m * ((1 + a ^ m) * L n 1 - L n a - a ^ m * L n a⁻¹) / (m : K) := by
    have hm' := Finset.mem_Ico.mp hm
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m), row_diagonal a ha,
      mul_zero, add_zero, add_comm]
    rw [Finset.sum_Ico_consecutive (fun j => s ^ m * row a m j)
      (by omega : 1 ≤ m) (by omega : m ≤ n + 1),
      ← Finset.mul_sum, row_full]
    ring
  calc
    _ = ∑ m ∈ Finset.Ico 1 (n + 1),
        s ^ m * ((1 + a ^ m) * L n 1 - L n a - a ^ m * L n a⁻¹) / (m : K) :=
      Finset.sum_congr rfl hjoin
    _ = _ := by
      change _ = (L n 1 - L n a) * (∑ m ∈ Finset.Ico 1 (n + 1), s ^ m / (m : K)) +
        (L n 1 - L n a⁻¹) * (∑ m ∈ Finset.Ico 1 (n + 1), (a * s) ^ m / (m : K))
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [mul_pow, div_eq_mul_inv]
      ring

private theorem sum_full_pairs {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
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

theorem L_square_eq_twice_E (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (x : K) :
    L ((p - 1) / 2) (x ^ 2) = 2 * WPFiniteField.E p x := by
  let n := (p - 1) / 2
  have hprime : p.Prime := Fact.out
  have hodd := hprime.odd_of_ne_two (by omega)
  have hpn : p = 2 * n + 1 := by
    rcases hodd with ⟨a, ha⟩
    dsimp only [n]
    omega
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he : WPFiniteField.ell p x + WPFiniteField.ell p (-x) = L n (x ^ 2) := by
    unfold WPFiniteField.ell
    rw [← Finset.sum_add_distrib, hpn, sum_full_pairs, ← Finset.sum_add_distrib]
    unfold L
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hden : (j : K) ≠ 0 :=
      WPFiniteField.denominator_ne_zero p j (Finset.mem_Ico.mpr (by omega))
    have heven : (-x) ^ (2 * j) = x ^ (2 * j) := by rw [pow_mul, neg_sq, ← pow_mul]
    have hoddj : (-x) ^ (2 * j - 1) = -(x ^ (2 * j - 1)) := by
      rw [show 2 * j - 1 = 2 * (j - 1) + 1 by omega]
      simp only [pow_add, pow_mul, neg_sq, pow_one, mul_neg]
    rw [heven, hoddj, neg_div]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [← pow_mul, Nat.mul_comm 2 j]
    field_simp [htwo, hden]
    ring
  rw [WPFiniteField.E, mul_div_cancel₀ _ htwo, he]

theorem ell_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.ell p (2 : K) = -2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
  have he := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.ell_two_eq_fermat p (by omega : 3 ≤ p))
  simpa only [← WPFiniteField.ell_castHom, map_neg, map_ofNat, map_mul, map_intCast] using he

private theorem pred_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : Even (p - 1) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hodd with ⟨n, hn⟩
  exact ⟨n, by omega⟩

theorem ell_neg_two (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.ell p (-2 : K) =
      2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hthree : (3 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hnegative : WPFiniteInversion.integerFermatQuotient p (-2) =
      WPFiniteInversion.integerFermatQuotient p 2 := by
    unfold WPFiniteInversion.integerFermatQuotient
    rw [(pred_even p hp).neg_pow]
  have he := WPFiniteInversion.entropyQuotient_eq_fermat p (-2)
    (by simpa using htwo) (by simpa using hthree)
  have hel := WPFiniteInversion.ell_eq_entropyQuotient p (by omega) (-2)
  rw [he, hnegative] at hel
  norm_num only [show (1 - -2 : ℤ) = 3 by norm_num] at hel
  have hm := congrArg (ZMod.castHom (dvd_refl p) K) hel
  simpa only [← WPFiniteField.ell_castHom, map_intCast, Int.cast_neg, Int.cast_ofNat,
    Nat.cast_ofNat, map_sub, map_neg, map_mul, Int.cast_sub, Int.cast_mul,
    map_ofNat, neg_neg] using hm

theorem L_rational_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    L ((p - 1) / 2) (1 : K) = -2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ∧
      L ((p - 1) / 2) (4 : K) = -3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) ∧
      L ((p - 1) / 2) (1 / 4 : K) =
        2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
          3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 2 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hone : WPFiniteField.ell p (1 : K) = 0 := by
    have he := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [← WPFiniteField.ell_castHom, map_one, map_zero] using he
  have hmone : WPFiniteField.ell p (-1 : K) =
      -2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
    have he := WPFiniteField.ell_reflection p (by omega) (-1 : K)
    rw [show (1 - -1 : K) = 2 by ring, ell_two p hp] at he
    exact he.symm
  have h2pow : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using (WPFiniteField.natCast_pow_char (K := K) p 2)
  have hnegpow : (-2 : K) ^ p = -2 := by
    rw [(Fact.out : p.Prime).odd_of_ne_two (by omega) |>.neg_pow, h2pow]
  have hhalf := WPFiniteField.ell_inversion p (2 : K) htwo
  have hmhalf := WPFiniteField.ell_inversion p (-2 : K) (neg_ne_zero.mpr htwo)
  rw [h2pow, ell_two p hp] at hhalf
  rw [hnegpow, ell_neg_two p hp] at hmhalf
  constructor
  · have he := L_square_eq_twice_E p hp (1 : K)
    rw [one_pow, WPFiniteField.E, hone, hmone] at he
    rw [he]
    field_simp [htwo]
    ring
  constructor
  · have he := L_square_eq_twice_E p hp (2 : K)
    rw [show (2 : K) ^ 2 = 4 by ring, WPFiniteField.E, ell_two p hp, ell_neg_two p hp] at he
    rw [he]
    field_simp [htwo]
    ring
  · have he := L_square_eq_twice_E p hp ((2 : K)⁻¹)
    have harg : ((2 : K)⁻¹) ^ 2 = 1 / 4 := by rw [inv_pow]; norm_num
    rw [harg, WPFiniteField.E, hhalf, show -(2 : K)⁻¹ = (-2 : K)⁻¹ by rw [inv_neg],
      hmhalf] at he
    rw [he]
    field_simp [htwo]
    ring

theorem loop_primitive (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    A p t - B p t + Chi p t =
      -(4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        6 * (WPFiniteInversion.integerFermatQuotient p 3 : K)) * WPFiniteField.E p t -
      (8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : K)) * WPFiniteField.E p (2 * t) := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have harg : (1 / 2 : K) ^ 2 = (4 : K)⁻¹ := by
    rw [div_pow, one_pow]; norm_num
  have he := loop_finite_primitive ((p - 1) / 2) (4 : K) (t ^ 2) hfour
  have hends := L_rational_ends (K := K) p hp
  rw [hends.1, hends.2.1, show (4 : K)⁻¹ = 1 / 4 by rw [one_div], hends.2.2,
    L_square_eq_twice_E p hp t,
    show 4 * t ^ 2 = (2 * t) ^ 2 by ring, L_square_eq_twice_E p hp (2 * t)] at he
  unfold A B Chi S
  simp only [mul_pow, one_pow, show (2 : K) ^ 2 = 4 by ring, harg]
  simp only [mul_pow, show (2 : K) ^ 2 = 4 by ring,
    show (1 / 4 : K) = (4 : K)⁻¹ by rw [one_div]] at he
  linear_combination he + 3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
    WPFiniteField.E p (2 * t) * (inv_mul_cancel₀ htwo)

theorem loop_at_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    A p u - B p u + Chi p u =
      -6 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) +
        9 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 +
        72 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 / 5 -
        54 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
          (WPFiniteInversion.integerFermatQuotient p 3 : K) / 5 -
        52 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * WPFifthEntropy.C p u / 5 +
        24 * (WPFiniteInversion.integerFermatQuotient p 3 : K) * WPFifthEntropy.C p u / 5 := by
  have htwo : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfive : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  rw [loop_primitive p hp u, WPFifthEntropy.E_at_double_fifth,
    WPFifthEntropy.E_at_fifth p hp u hu]
  field_simp [htwo, hfive]
  ring

end WPFiniteLoop
