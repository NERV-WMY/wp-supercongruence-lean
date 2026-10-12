import WPFiniteInversion
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

namespace WPFiniteInversion

/-- The quotient is formed in the integers before reduction. -/
def entropyQuotient (p : ℕ) (a : ℤ) : ℤ :=
  (1 - a ^ p - (1 - a) ^ p) / (p : ℤ)

/-- Literal integer Fermat quotient. -/
def integerFermatQuotient (p : ℕ) (a : ℤ) : ℤ :=
  (a ^ (p - 1) - 1) / (p : ℤ)

theorem entropy_numerator_dvd (p : ℕ) [Fact p.Prime] (a : ℤ) :
    (p : ℤ) ∣ 1 - a ^ p - (1 - a) ^ p := by
  have ha := Int.prime_dvd_pow_self_sub (Fact.out : p.Prime) a
  have hb := Int.prime_dvd_pow_self_sub (Fact.out : p.Prime) (1 - a)
  have h := dvd_neg.mpr (dvd_add ha hb)
  have he : 1 - a ^ p - (1 - a) ^ p =
      -(a ^ p - a + ((1 - a) ^ p - (1 - a))) := by ring
  rw [he]
  exact h

theorem integerFermatQuotient_dvd (p : ℕ) [Fact p.Prime]
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    (p : ℤ) ∣ a ^ (p - 1) - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_one, sub_eq_zero] using
    ZMod.pow_card_sub_one_eq_one ha

private theorem choose_pred_cast (p j : ℕ) [Fact p.Prime] (hj : j < p) :
    (Nat.choose (p - 1) j : ZMod p) = (-1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hprime : p.Prime := Fact.out
      have hdiv := hprime.dvd_choose_self (by omega : j + 1 ≠ 0) hj
      have hz : (Nat.choose p (j + 1) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
      have hpas := Nat.choose_succ_right p j hprime.pos
      have he : (Nat.choose (p - 1) j : ZMod p) +
          (Nat.choose (p - 1) (j + 1) : ZMod p) = 0 := by
        exact_mod_cast (show (Nat.choose p (j + 1) : ZMod p) = 0 from hz) ▸
          (congrArg (fun n : ℕ => (n : ZMod p)) hpas).symm
      rw [ih (by omega)] at he
      rw [pow_succ]
      linear_combination he

theorem divided_choose_cast (p j : ℕ) [Fact p.Prime]
    (hj : j ∈ Finset.Ico 1 p) :
    (((Nat.choose p j : ℤ) / (p : ℤ) : ℤ) : ZMod p) =
      (-1) ^ (j - 1) / (j : ZMod p) := by
  have hprime : p.Prime := Fact.out
  have hj' := Finset.mem_Ico.mp hj
  have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
    exact_mod_cast hprime.dvd_choose_self (by omega) hj'.2
  have hmul : (p : ℤ) * (Nat.choose (p - 1) (j - 1) : ℤ) =
      (Nat.choose p j : ℤ) * j := by
    have hn := Nat.add_one_mul_choose_eq (p - 1) (j - 1)
    rw [Nat.sub_add_cancel hprime.one_le, Nat.sub_add_cancel hj'.1] at hn
    exact_mod_cast hn
  have he : ((Nat.choose p j : ℤ) / p) * j =
      (Nat.choose (p - 1) (j - 1) : ℤ) := by
    apply mul_left_cancel₀ (by exact_mod_cast hprime.ne_zero : (p : ℤ) ≠ 0)
    rw [← mul_assoc, Int.mul_ediv_cancel' hd]
    exact hmul.symm
  have hez := congrArg (fun z : ℤ => (z : ZMod p)) he
  push_cast at hez
  rw [choose_pred_cast p (j - 1) (by omega)] at hez
  exact (eq_div_iff (denominator_ne_zero p j hj)).mpr hez

private theorem entropy_binomial_identity (p : ℕ) [Fact p.Prime]
    (hp3 : 3 ≤ p) (a : ℤ) :
    1 - a ^ p - (1 - a) ^ p =
      (p : ℤ) * (-(∑ j ∈ Finset.Ico 1 p,
        ((Nat.choose p j : ℤ) / (p : ℤ)) * (-a) ^ j)) := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  have hbin := add_pow (-a) (1 : ℤ) p
  simp only [one_pow, mul_one] at hbin
  rw [Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, Nat.choose_self] at hbin
  rw [show -a + 1 = 1 - a by ring, hodd.neg_pow] at hbin
  have hsum : (∑ j ∈ Finset.Ico 1 p, (-a) ^ j * (Nat.choose p j : ℤ)) =
      (p : ℤ) * (∑ j ∈ Finset.Ico 1 p,
        ((Nat.choose p j : ℤ) / (p : ℤ)) * (-a) ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hd : (p : ℤ) ∣ (Nat.choose p j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by omega) hj'.2
    rw [← mul_assoc, Int.mul_ediv_cancel' hd]
    ring
  rw [hsum] at hbin
  linear_combination -hbin

theorem entropyQuotient_eq_sum (p : ℕ) [Fact p.Prime]
    (hp3 : 3 ≤ p) (a : ℤ) :
    entropyQuotient p a = -(∑ j ∈ Finset.Ico 1 p,
      ((Nat.choose p j : ℤ) / (p : ℤ)) * (-a) ^ j) := by
  have hprime : p.Prime := Fact.out
  apply mul_right_cancel₀ (by exact_mod_cast hprime.ne_zero : (p : ℤ) ≠ 0)
  rw [entropyQuotient, Int.ediv_mul_cancel (entropy_numerator_dvd p a),
    entropy_binomial_identity p hp3 a]
  ring

theorem ell_eq_entropyQuotient (p : ℕ) [Fact p.Prime]
    (hp3 : 3 ≤ p) (a : ℤ) :
    ell p (a : ZMod p) = (entropyQuotient p a : ZMod p) := by
  rw [entropyQuotient_eq_sum p hp3 a]
  push_cast
  rw [← Finset.sum_neg_distrib]
  unfold ell
  apply Finset.sum_congr rfl
  intro j hj
  rw [divided_choose_cast p j hj]
  have hjpos : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hsign : (-1 : ZMod p) ^ (j - 1) * (-1) ^ j = -1 := by
    rw [show j = (j - 1) + 1 by omega, pow_succ]
    calc
      (-1 : ZMod p) ^ (j - 1) * ((-1) ^ (j - 1) * -1) =
          -((-1 : ZMod p) ^ (j - 1)) ^ 2 := by ring
      _ = -1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
  rw [neg_pow]
  simp only [div_eq_mul_inv]
  linear_combination (a : ZMod p) ^ j * (j : ZMod p)⁻¹ * hsign

theorem integerFermatQuotient_mul (p : ℕ) [Fact p.Prime]
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    integerFermatQuotient p a * (p : ℤ) = a ^ (p - 1) - 1 := by
  exact Int.ediv_mul_cancel (integerFermatQuotient_dvd p a ha)

theorem entropyQuotient_eq_fermat (p : ℕ) [Fact p.Prime]
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) (hb : ((1 - a : ℤ) : ZMod p) ≠ 0) :
    entropyQuotient p a =
      -a * integerFermatQuotient p a -
        (1 - a) * integerFermatQuotient p (1 - a) := by
  have hprime : p.Prime := Fact.out
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have ha' := integerFermatQuotient_mul p a ha
  have hb' := integerFermatQuotient_mul p (1 - a) hb
  have haPow : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hprime.one_le]
  have hbPow : (1 - a) ^ p = (1 - a) ^ (p - 1) * (1 - a) := by
    rw [← pow_succ, Nat.sub_add_cancel hprime.one_le]
  apply mul_right_cancel₀ hp
  rw [entropyQuotient, Int.ediv_mul_cancel (entropy_numerator_dvd p a),
    haPow, hbPow]
  linear_combination a * ha' + (1 - a) * hb'

private theorem pred_even (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) : Even (p - 1) := by
  have hpodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hpodd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

theorem integerFermatQuotient_four_cast (p : ℕ) [Fact p.Prime]
    (hp3 : 3 ≤ p) :
    (integerFermatQuotient p 4 : ZMod p) =
      2 * (integerFermatQuotient p 2 : ZMod p) := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by ring]
    exact mul_ne_zero htwo htwo
  have hq2 := integerFermatQuotient_mul p 2 (by simpa using htwo)
  have hq4 := integerFermatQuotient_mul p 4 (by simpa using hfour)
  have hpow : (4 : ℤ) ^ (p - 1) = ((2 : ℤ) ^ (p - 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hid : integerFermatQuotient p 4 =
      2 * integerFermatQuotient p 2 +
        (p : ℤ) * (integerFermatQuotient p 2) ^ 2 := by
    apply mul_right_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero :
      (p : ℤ) ≠ 0)
    rw [hq4, hpow]
    linear_combination
      -(integerFermatQuotient p 2 * (p : ℤ) + (2 : ℤ) ^ (p - 1) + 1) * hq2
  have hz := congrArg (fun z : ℤ => (z : ZMod p)) hid
  simpa using hz

theorem ell_two_eq_fermat (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ell p 2 = -2 * (integerFermatQuotient p 2 : ZMod p) := by
  have htwo : (2 : ZMod p) ≠ 0 :=
    denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hmone : (((1 - 2 : ℤ)) : ZMod p) ≠ 0 := by norm_num
  have he := entropyQuotient_eq_fermat p 2 (by simpa using htwo) hmone
  have heven : (-1 : ℤ) ^ (p - 1) = 1 := (pred_even p hp3).neg_one_pow
  have hzero : integerFermatQuotient p (1 - 2) = 0 := by
    norm_num only [show (1 - 2 : ℤ) = -1 by norm_num, integerFermatQuotient,
      heven, sub_self, Int.zero_ediv]
  rw [hzero] at he
  have hel := ell_eq_entropyQuotient p hp3 2
  rw [he] at hel
  simpa using hel

theorem ell_neg_four_eq_fermat (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    ell p (-4) = 8 * (integerFermatQuotient p 2 : ZMod p) -
      5 * (integerFermatQuotient p 5 : ZMod p) := by
  have hfour : ((-4 : ℤ) : ZMod p) ≠ 0 := by
    have h4 := denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
    simpa using h4
  have hfive : ((1 - (-4) : ℤ) : ZMod p) ≠ 0 := by
    have h5 := denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
    simpa using h5
  have hnegative : integerFermatQuotient p (-4) = integerFermatQuotient p 4 := by
    unfold integerFermatQuotient
    rw [(pred_even p (by omega)).neg_pow]
  have he := entropyQuotient_eq_fermat p (-4) hfour hfive
  rw [hnegative] at he
  have hel := ell_eq_entropyQuotient p (by omega) (-4)
  rw [he] at hel
  norm_num only [Int.cast_sub, Int.cast_neg, Int.cast_ofNat,
    neg_neg, show (1 - (-4) : ℤ) = 5 by norm_num] at hel
  push_cast at hel
  rw [integerFermatQuotient_four_cast p (by omega)] at hel
  linear_combination hel

end WPFiniteInversion
