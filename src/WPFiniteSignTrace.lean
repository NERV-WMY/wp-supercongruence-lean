import WPFiniteNC122Residue

open scoped BigOperators

namespace WPFiniteSignTrace

variable {K : Type*} [Field K]

noncomputable def fullTraceS (p : ℕ) (x y : K) : K :=
  WPFiniteLoop.D (p - 1) x y + WPFiniteLoop.D (p - 1) (-x) y +
    WPFiniteLoop.D (p - 1) x (-y) + WPFiniteLoop.D (p - 1) (-x) (-y)

private def signTerm (j k : ℕ) (x y : K) : K :=
  (x ^ k + (-x) ^ k) * (y ^ (j - k) + (-y) ^ (j - k)) / ((k : K) * (j : K))

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

private theorem odd_row (j : ℕ) (hj : 1 ≤ j) (x y : K) :
    (∑ k ∈ Finset.Ico 1 (2 * j - 1 + 1), signTerm (2 * j - 1) k x y) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_Ico.mp hk
  by_cases hkeven : Even k
  · obtain ⟨a, ha⟩ := hkeven
    have hyodd : Odd (2 * j - 1 - k) := ⟨j - a - 1, by omega⟩
    unfold signTerm
    rw [hyodd.neg_pow]
    simp
  · have hkodd := (Nat.even_or_odd k).resolve_left hkeven
    unfold signTerm
    rw [hkodd.neg_pow]
    simp

private theorem even_row (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (j : ℕ) (hj : j ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) (x y : K) :
    (∑ k ∈ Finset.Ico 1 (2 * j + 1), signTerm (2 * j) k x y) =
      ∑ i ∈ Finset.Ico 1 (j + 1), (x ^ 2) ^ i * (y ^ 2) ^ (j - i) / ((i : K) * (j : K)) := by
  rw [sum_full_pairs]
  have ho : (∑ i ∈ Finset.Ico 1 (j + 1), signTerm (2 * j) (2 * i - 1) x y) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := (Finset.mem_Ico.mp hi).1
    have hodd : Odd (2 * i - 1) := ⟨i - 1, by omega⟩
    unfold signTerm
    rw [hodd.neg_pow]
    simp
  rw [ho, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  have hj' := Finset.mem_Ico.mp hj
  have htwo : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hid : (i : K) ≠ 0 := WPFiniteField.denominator_ne_zero p i
    (Finset.mem_Ico.mpr (by omega))
  have hjd : (j : K) ≠ 0 := WPFiniteField.denominator_ne_zero p j
    (Finset.mem_Ico.mpr (by omega))
  have hnx : (-x) ^ (2 * i) = x ^ (2 * i) := by rw [pow_mul, neg_sq, ← pow_mul]
  have hny : (-y) ^ (2 * j - 2 * i) = y ^ (2 * j - 2 * i) := by
    rw [show 2 * j - 2 * i = 2 * (j - i) by omega, pow_mul, neg_sq, ← pow_mul]
  unfold signTerm
  rw [hnx, hny, show 2 * j - 2 * i = 2 * (j - i) by omega]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [pow_mul x 2 i, pow_mul y 2 (j - i)]
  field_simp [htwo, hid, hjd]
  ring

theorem full_trace_eq_half_cutoff (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (x y : K) :
    fullTraceS p x y = WPFiniteLoop.S p x y := by
  let n := (p - 1) / 2
  have hpn : p = 2 * n + 1 := by
    obtain ⟨a, ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    dsimp only [n]
    omega
  have he : fullTraceS p x y =
      ∑ j ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 (j + 1), signTerm j k x y := by
    unfold fullTraceS WPFiniteLoop.D
    rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold signTerm
    simp only [div_eq_mul_inv]
    ring
  rw [he, hpn, sum_full_pairs]
  have ho : (∑ j ∈ Finset.Ico 1 (n + 1),
      ∑ k ∈ Finset.Ico 1 (2 * j - 1 + 1), signTerm (2 * j - 1) k x y) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact odd_row j (Finset.mem_Ico.mp hj).1 x y
  rw [ho, add_zero]
  unfold WPFiniteLoop.S WPFiniteLoop.D
  rw [show (2 * n + 1 - 1) / 2 = n by omega]
  apply Finset.sum_congr rfl
  intro j hj
  exact even_row p hp j hj x y

noncomputable def Afull (p : ℕ) (t : K) : K := fullTraceS p (2 * t) 1 - fullTraceS p t (1 / 2)

noncomputable def Bfull (p : ℕ) (t : K) : K := fullTraceS p (2 * t) 2 - fullTraceS p t 1

noncomputable def Chifull (p : ℕ) (t : K) : K :=
  fullTraceS p t t + fullTraceS p (2 * t) (2 * t) -
    fullTraceS p (2 * t) t - fullTraceS p t (2 * t)

theorem original_loop_eq (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    Afull p t - Bfull p t + Chifull p t =
      WPFiniteLoop.A p t - WPFiniteLoop.B p t + WPFiniteLoop.Chi p t := by
  unfold Afull Bfull Chifull WPFiniteLoop.A WPFiniteLoop.B WPFiniteLoop.Chi
  simp only [full_trace_eq_half_cutoff p hp]

theorem original_sign_loop_primitive (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (t : K) :
    Afull p t - Bfull p t + Chifull p t =
      -(4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
          6 * (WPFiniteInversion.integerFermatQuotient p 3 : K)) * WPFiniteField.E p t -
        (8 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
          3 * (WPFiniteInversion.integerFermatQuotient p 3 : K)) * WPFiniteField.E p (2 * t) := by
  rw [original_loop_eq p hp]
  exact WPFiniteLoop.loop_primitive p hp t

theorem original_sign_corrected_consumer (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    77 * (Afull p u - Bfull p u + Chifull p u) / 75 +
      22 * (WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u) / 5 -
      2233 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 / 125 +
      1386 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
        (WPFiniteInversion.integerFermatQuotient p 3 : K) / 125 +
      154 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 25 -
      231 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 50 +
      4334 * (WPFiniteInversion.integerFermatQuotient p 2 : K) * WPFifthEntropy.C p u / 375 -
      616 * (WPFiniteInversion.integerFermatQuotient p 3 : K) * WPFifthEntropy.C p u / 125 -
      88 * (WPFifthEntropy.C p u) ^ 2 / 25 - 22 * WPFiniteField.R p (-2 : K) / 15 -
      11 * WPFiniteField.R p (16 : K) / 150 = 0 := by
  rw [original_loop_eq p hp]
  exact WPActualFinalConsumer.actual_corrected_consumer p hp u hu

end WPFiniteSignTrace
