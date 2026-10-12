import WPFiniteEntropy

open scoped Polynomial BigOperators
open Polynomial

namespace WPMomentPrecision.BasePole

set_option maxHeartbeats 800000

/-- Every interior binomial coefficient is divided in Z before its cast. -/
noncomputable def binomialInterior {K : Type*} [CommRing K]
    (p : ℕ) (a b : K) : K[X] :=
  ∑ j ∈ Finset.Ico 1 p,
    C (((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) *
      (C a * X) ^ j * C b ^ (p - j)

theorem binomialInterior_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : ℕ) (a b : K) :
    (binomialInterior p a b).map f = binomialInterior p (f a) (f b) := by
  simp [binomialInterior, Polynomial.map_sum]

theorem binomialInterior_normalform {K : Type*} [CommRing K]
    (p : ℕ) (a b : K) :
    binomialInterior p a b = ∑ j ∈ Finset.Ico 1 p,
      C (((((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) * a ^ j * b ^ (p - j))) * X ^ j := by
  unfold binomialInterior
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [mul_pow, ← map_pow, map_mul]
  ring

/-- No interior coefficient outside 1,...,p-1 is discarded. -/
theorem binomialInterior_coefficient {K : Type*} [CommRing K]
    (p j : ℕ) (a b : K) :
    (binomialInterior p a b).coeff j =
      if j ∈ Finset.Ico 1 p then
        ((((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) * a ^ j * b ^ (p - j))
      else 0 := by
  classical
  rw [binomialInterior_normalform, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

theorem binomialInterior_support {K : Type*} [CommRing K]
    (p : ℕ) (a b : K) : (binomialInterior p a b).support ⊆ Finset.Ico 1 p := by
  intro j hj
  by_contra hn
  have hc := Polynomial.mem_support_iff.mp hj
  rw [binomialInterior_coefficient, if_neg hn] at hc
  exact hc rfl

theorem binomialInterior_degree {K : Type*} [CommRing K]
    (p : ℕ) (a b : K) : (binomialInterior p a b).natDegree ≤ p - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [binomialInterior_coefficient, if_neg]
  intro hn
  have hjp := (Finset.mem_Ico.mp hn).2
  omega

/-- The full row includes both degree-p and constant Frobenius slots. -/
theorem binomialInterior_source {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] (a b : K) :
    (C a * X + C b : K[X]) ^ p =
      (C a * X) ^ p + C b ^ p + C (p : K) * binomialInterior p a b := by
  have hprime : p.Prime := Fact.out
  have hbin := add_pow (C a * X : K[X]) (C b) p
  rw [Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico _ hprime.one_le] at hbin
  simp only [Finset.sum_range_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, one_mul, Nat.choose_self, Nat.sub_self] at hbin
  have hsum : (∑ j ∈ Finset.Ico 1 p,
      (C a * X : K[X]) ^ j * C b ^ (p - j) * (p.choose j : K[X])) =
      C (p : K) * binomialInterior p a b := by
    rw [binomialInterior, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp := Finset.mem_Ico.mp hj
    have hd : (p : ℤ) ∣ (p.choose j : ℤ) := by
      exact_mod_cast hprime.dvd_choose_self (by omega : j ≠ 0) hjp.2
    have he : (p : K) * (((p.choose j : ℤ) / (p : ℤ) : ℤ) : K) =
        (p.choose j : K) := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : K)) (Int.mul_ediv_cancel' hd)
    have heP := congrArg (C : K → K[X]) he
    simp only [map_mul, C_eq_natCast] at heP
    rw [C_eq_natCast]
    linear_combination -(C a * X : K[X]) ^ j * C b ^ (p - j) * heP
  rw [hsum] at hbin
  simpa only [Nat.sub_zero, add_comm, add_left_comm, add_assoc] using hbin

noncomputable def firstFCarry {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  binomialInterior p (-1) 4

noncomputable def firstGCarry {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  binomialInterior p 4 (-1)

noncomputable def frobeniusF {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  C ((4 : K) ^ p) - X ^ p

noncomputable def frobeniusG {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  C ((4 : K) ^ p) * X ^ p - 1

theorem actual_F_first_carry_source {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 - X : K[X]) ^ p = frobeniusF p + C (p : K) * firstFCarry p := by
  have hs := binomialInterior_source p (-1 : K) 4
  have harg : (C (-1 : K) * X + C 4 : K[X]) = 4 - X := by
    simp only [map_neg, map_one, C_ofNat, neg_one_mul]
    ring
  have hpower : (C (-1 : K) * X : K[X]) ^ p = -X ^ p := by
    rw [map_neg, map_one, neg_one_mul, hp.neg_pow]
  have hfour : (C (4 : K) : K[X]) ^ p = C ((4 : K) ^ p) := (map_pow C 4 p).symm
  rw [harg, hpower, hfour] at hs
  simpa only [firstFCarry, frobeniusF, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hs

theorem actual_G_first_carry_source {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 * X - 1 : K[X]) ^ p = frobeniusG p + C (p : K) * firstGCarry p := by
  have hs := binomialInterior_source p (4 : K) (-1)
  have harg : (C (4 : K) * X + C (-1) : K[X]) = 4 * X - 1 := by
    simp only [map_neg, map_one, C_ofNat, sub_eq_add_neg]
  have hpower : (C (4 : K) * X : K[X]) ^ p = C ((4 : K) ^ p) * X ^ p := by
    rw [mul_pow, ← map_pow]
  have hneg : (C (-1 : K) : K[X]) ^ p = -1 := by
    rw [map_neg, map_one, hp.neg_one_pow]
  rw [harg, hpower, hneg] at hs
  simpa only [firstGCarry, frobeniusG, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hs

theorem actual_firstFCarry_field_coefficient (p j : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hj : j ∈ Finset.Ico 1 p) :
    (firstFCarry p : (ZMod p)[X]).coeff j =
      -4 / ((4 : ZMod p) ^ j * (j : ZMod p)) := by
  have hjp := Finset.mem_Ico.mp hj
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPFiniteInversion.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have hpow : (4 : ZMod p) ^ (p - j) = 4 / (4 : ZMod p) ^ j := by
    rw [pow_sub₀ (4 : ZMod p) h4 (by omega : j ≤ p), ZMod.pow_card]
    rfl
  have hsign : (-1 : ZMod p) ^ (j - 1) * (-1) ^ j = -1 := by
    have he : (-1 : ZMod p) ^ j = (-1) ^ (j - 1) * (-1) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
    rw [he, ← mul_assoc, ← mul_pow]
    norm_num
  rw [firstFCarry, binomialInterior_coefficient, if_pos hj,
    WPFiniteInversion.divided_choose_cast p j hj, hpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = ((-1 : ZMod p) ^ (j - 1) * (-1) ^ j) *
        (j : ZMod p)⁻¹ * 4 * ((4 : ZMod p) ^ j)⁻¹ := by ring
    _ = _ := by rw [hsign]; ring

theorem actual_firstGCarry_field_coefficient (p j : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hj : j ∈ Finset.Ico 1 p) :
    (firstGCarry p : (ZMod p)[X]).coeff j =
      (4 : ZMod p) ^ j / (j : ZMod p) := by
  have hjp := Finset.mem_Ico.mp hj
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    exact ⟨k, by omega⟩
  have hsign : (-1 : ZMod p) ^ (j - 1) * (-1) ^ (p - j) = 1 := by
    rw [← pow_add, show j - 1 + (p - j) = p - 1 by omega]
    exact heven.neg_one_pow
  rw [firstGCarry, binomialInterior_coefficient, if_pos hj,
    WPFiniteInversion.divided_choose_cast p j hj]
  simp only [div_eq_mul_inv]
  calc
    _ = ((-1 : ZMod p) ^ (j - 1) * (-1) ^ (p - j)) *
        (4 : ZMod p) ^ j * (j : ZMod p)⁻¹ := by ring
    _ = _ := by rw [hsign, one_mul]

noncomputable def baseFirstCarry {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  2 * frobeniusF p * firstFCarry p * frobeniusG p +
    frobeniusF p ^ 2 * firstGCarry p

noncomputable def baseSecondCarry {K : Type*} [CommRing K] (p : ℕ) : K[X] :=
  firstFCarry p ^ 2 * frobeniusG p +
    2 * frobeniusF p * firstFCarry p * firstGCarry p

/-- SB2 is an exact polynomial identity with its entire cubic remainder. -/
theorem actual_base_three_carry_source {K : Type*} [CommRing K]
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    (4 - X : K[X]) ^ (2 * p) * (4 * X - 1) ^ p =
      frobeniusF p ^ 2 * frobeniusG p +
      C (p : K) * baseFirstCarry p +
      C ((p : K) ^ 2) * baseSecondCarry p +
      C ((p : K) ^ 3) * firstFCarry p ^ 2 * firstGCarry p := by
  rw [show 2 * p = p * 2 by omega, pow_mul,
    actual_F_first_carry_source p hp, actual_G_first_carry_source p hp]
  unfold baseFirstCarry baseSecondCarry
  simp only [map_pow]
  ring

end WPMomentPrecision.BasePole
