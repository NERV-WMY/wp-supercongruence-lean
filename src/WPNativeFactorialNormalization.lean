import WPFiniteReflection
import WPReview.NativeTruncation
import WPReview.Literal
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators

namespace WPNativeFactorialNormalization

def harmonicLift (p k : ℕ) : ZMod (p ^ 3) :=
  ∑ r ∈ Finset.Ico 1 p, ((r : ZMod (p ^ 3))⁻¹) ^ k

private theorem interval_unit (p r : ℕ) (hp : p.Prime)
    (hr : r ∈ Finset.Ico 1 p) : IsUnit (r : ZMod (p ^ 3)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).mpr
  have hr' := Finset.mem_Ico.mp hr
  exact Nat.not_dvd_of_pos_of_lt (by omega) hr'.2

private theorem cubic_nil (p : ℕ) : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private def reduction (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)

private theorem reduction_inverse (p r : ℕ) [Fact p.Prime]
    (hr : r ∈ Finset.Ico 1 p) :
    reduction p (r : ZMod (p ^ 3))⁻¹ = (r : ZMod p)⁻¹ := by
  have he := congrArg (reduction p)
    (ZMod.mul_inv_of_unit (r : ZMod (p ^ 3)) (interval_unit p r Fact.out hr))
  simp only [map_mul, map_natCast, map_one] at he
  apply mul_left_cancel₀ (WPFiniteInversion.denominator_ne_zero p r hr)
  rw [he, mul_inv_cancel₀ (WPFiniteInversion.denominator_ne_zero p r hr)]

private theorem square_annihilator_of_reduction_zero (p : ℕ) [Fact p.Prime]
    (x : ZMod (p ^ 3)) (hx : reduction p x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp⟩
  have hxcast : (x.val : ZMod (p ^ 3)) = x := ZMod.natCast_zmod_val x
  have hf : (x.val : ZMod p) = 0 := by
    have he := congrArg (reduction p) hxcast
    simpa only [map_natCast, hx] using he
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hf
  rw [← hxcast, hk, Nat.cast_mul]
  calc
    (p : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) * k) =
      (p : ZMod (p ^ 3)) ^ 3 * k := by ring
    _ = 0 := by rw [cubic_nil, zero_mul]

theorem harmonic_two_annihilator (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 3)) ^ 2 * harmonicLift p 2 = 0 := by
  apply square_annihilator_of_reduction_zero
  simp only [harmonicLift, map_sum, map_pow]
  have he := WPFiniteInversion.R_one_eq_zero p (by omega : 5 ≤ p)
  simp only [WPFiniteInversion.R, one_pow, one_div, ← inv_pow] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [reduction_inverse p r hr]

private theorem pair_inverse (p r : ℕ) [Fact p.Prime]
    (hr : r ∈ Finset.Ico 1 p) :
    (r : ZMod (p ^ 3))⁻¹ + ((p - r : ℕ) : ZMod (p ^ 3))⁻¹ =
      (p : ZMod (p ^ 3)) * (r : ZMod (p ^ 3))⁻¹ *
        ((p - r : ℕ) : ZMod (p ^ 3))⁻¹ := by
  have hr' := Finset.mem_Ico.mp hr
  have hrr : p - r ∈ Finset.Ico 1 p := Finset.mem_Ico.mpr (by omega)
  have hu := ZMod.mul_inv_of_unit (r : ZMod (p ^ 3))
    (interval_unit p r Fact.out hr)
  have hv := ZMod.mul_inv_of_unit ((p - r : ℕ) : ZMod (p ^ 3))
    (interval_unit p (p - r) Fact.out hrr)
  have hb : ((p - r : ℕ) : ZMod (p ^ 3)) = p - r :=
    Nat.cast_sub (Nat.le_of_lt hr'.2)
  rw [hb] at hv ⊢
  linear_combination -((r : ZMod (p ^ 3))⁻¹) * hv -
    ((p : ZMod (p ^ 3)) - r)⁻¹ * hu

private theorem pair_cubic_identity (p r : ℕ) [Fact p.Prime]
    (hr : r ∈ Finset.Ico 1 p) :
    (p : ZMod (p ^ 3)) * ((r : ZMod (p ^ 3))⁻¹ +
        ((p - r : ℕ) : ZMod (p ^ 3))⁻¹) =
      -(p : ZMod (p ^ 3)) ^ 2 * ((r : ZMod (p ^ 3))⁻¹) ^ 2 := by
  have he := pair_inverse p r hr
  have hn := cubic_nil p
  linear_combination
    ((p : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 *
      (r : ZMod (p ^ 3))⁻¹) * he +
    (r : ZMod (p ^ 3))⁻¹ ^ 2 * ((p - r : ℕ) : ZMod (p ^ 3))⁻¹ * hn

theorem harmonic_one_annihilator (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 3)) * harmonicLift p 1 = 0 := by
  have href := WPFiniteInversion.full_cutoff_reflection p
    (fun r => (r : ZMod (p ^ 3))⁻¹)
  have hpair : (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * harmonicLift p 1) =
      -(p : ZMod (p ^ 3)) ^ 2 * harmonicLift p 2 := by
    calc
      _ = ∑ r ∈ Finset.Ico 1 p,
          (p : ZMod (p ^ 3)) * ((r : ZMod (p ^ 3))⁻¹ +
            ((p - r : ℕ) : ZMod (p ^ 3))⁻¹) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, href]
        simp only [harmonicLift, pow_one]
        ring
      _ = _ := by
        unfold harmonicLift
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        exact pair_cubic_identity p r hr
  have htwo : IsUnit (2 : ZMod (p ^ 3)) :=
    interval_unit p 2 Fact.out (Finset.mem_Ico.mpr (by omega))
  apply htwo.mul_left_cancel
  rw [mul_zero, hpair, neg_mul, harmonic_two_annihilator p hp7, neg_zero]

private theorem cubic_product_expansion {A ι : Type*} [CommRing A]
    (s : Finset ι) (f : ι → A) (z t : A) (hz : z ^ 3 = 0) (ht : 2 * t = 1) :
    (∏ r ∈ s, (1 + z * f r)) = 1 + z * (∑ r ∈ s, f r) +
      z ^ 2 * t * ((∑ r ∈ s, f r) ^ 2 - ∑ r ∈ s, (f r) ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hrs ih =>
      simp only [Finset.prod_insert hrs, Finset.sum_insert hrs]
      rw [ih]
      linear_combination
        f r * t * ((∑ j ∈ s, f j) ^ 2 - ∑ j ∈ s, (f j) ^ 2) * hz -
          z ^ 2 * f r * (∑ j ∈ s, f j) * ht

def unitBlock (p j : ℕ) : ℕ := ∏ r ∈ Finset.Ico 1 p, (j * p + r)

private theorem normalized_block_eq_one (p j : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (∏ r ∈ Finset.Ico 1 p, (1 + (j : ZMod (p ^ 3)) * p * (r : ZMod (p ^ 3))⁻¹)) =
      1 := by
  let z : ZMod (p ^ 3) := j * p
  let t : ZMod (p ^ 3) := (2 : ZMod (p ^ 3))⁻¹
  have hz : z ^ 3 = 0 := by simp [z, mul_pow, cubic_nil]
  have ht : (2 : ZMod (p ^ 3)) * t = 1 :=
    ZMod.mul_inv_of_unit _ (interval_unit p 2 Fact.out (Finset.mem_Ico.mpr (by omega)))
  have he := cubic_product_expansion (Finset.Ico 1 p)
    (fun r => (r : ZMod (p ^ 3))⁻¹) z t hz ht
  have hz1 : z * harmonicLift p 1 = 0 := by
    dsimp [z]
    rw [mul_assoc, harmonic_one_annihilator p hp7, mul_zero]
  have hz2 : z ^ 2 * harmonicLift p 2 = 0 := by
    dsimp [z]
    rw [mul_pow, mul_assoc, harmonic_two_annihilator p hp7, mul_zero]
  simp only [harmonicLift, pow_one] at hz1
  simp only [harmonicLift] at hz2
  rw [he]
  linear_combination (1 + z * t * (∑ r ∈ Finset.Ico 1 p, (r : ZMod (p ^ 3))⁻¹)) * hz1 - t * hz2

theorem unit_block_congruent (p j : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (unitBlock p j : ZMod (p ^ 3)) = (unitBlock p 0 : ZMod (p ^ 3)) := by
  have hprod : (unitBlock p j : ZMod (p ^ 3)) =
      (unitBlock p 0 : ZMod (p ^ 3)) *
        ∏ r ∈ Finset.Ico 1 p,
          (1 + (j : ZMod (p ^ 3)) * p * (r : ZMod (p ^ 3))⁻¹) := by
    simp only [unitBlock, Nat.cast_prod, Nat.cast_add, Nat.cast_mul, zero_mul, zero_add,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r hr
    have hu := ZMod.mul_inv_of_unit (r : ZMod (p ^ 3))
      (interval_unit p r Fact.out hr)
    linear_combination -(j : ZMod (p ^ 3)) * p * hu
  rw [hprod, normalized_block_eq_one p j hp7, mul_one]

private theorem factorial_blocks (p k : ℕ) (hp : 1 ≤ p) :
    (k * p).factorial = p ^ k * k.factorial * ∏ j ∈ Finset.range k, unitBlock p j := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : ((k + 1) * p).factorial =
          (k * p).factorial * (unitBlock p k * ((k + 1) * p)) := by
        rw [← Finset.prod_Ico_id_eq_factorial]
        have hb : (∏ r ∈ Finset.Ico (k * p + 1) ((k + 1) * p + 1), r) =
            unitBlock p k * ((k + 1) * p) := by
          have hshift := Finset.prod_Ico_add' (fun r : ℕ => r) 1 (p + 1) (k * p)
          have hlow : 1 + k * p = k * p + 1 := by omega
          have htop : p + 1 + k * p = (k + 1) * p + 1 := by ring
          rw [hlow, htop] at hshift
          rw [← hshift, Finset.prod_Ico_succ_top hp]
          simp only [unitBlock]
          congr 1
          · apply Finset.prod_congr rfl
            intro r hr
            omega
          · omega
        have hsplit := Finset.prod_Ico_consecutive (fun r : ℕ => r)
          (show 1 ≤ k * p + 1 by omega)
          (show k * p + 1 ≤ (k + 1) * p + 1 by
            simp only [Nat.add_mul, Nat.one_mul]; omega)
        rw [← hsplit, Finset.prod_Ico_id_eq_factorial, hb]
      rw [hstep, ih, Nat.factorial_succ, pow_succ, Finset.prod_range_succ]
      ring

def nativeMultinomial (n : ℕ) : ℕ :=
  Nat.choose (6 * n) (3 * n) * Nat.choose (3 * n) n * Nat.choose (2 * n) n

private theorem multinomial_factorial_identity (n : ℕ) :
    nativeMultinomial n * n.factorial ^ 3 * (3 * n).factorial = (6 * n).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show 3 * n ≤ 6 * n by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 6 * n - 3 * n = 3 * n by omega] at h1
  rw [show 3 * n - n = 2 * n by omega] at h2
  rw [show 2 * n - n = n by omega] at h3
  calc
    nativeMultinomial n * n.factorial ^ 3 * (3 * n).factorial =
      Nat.choose (6 * n) (3 * n) * (3 * n).factorial *
        (Nat.choose (3 * n) n * n.factorial *
          (Nat.choose (2 * n) n * n.factorial * n.factorial)) := by
            unfold nativeMultinomial
            ring
    _ = Nat.choose (6 * n) (3 * n) * (3 * n).factorial *
        (Nat.choose (3 * n) n * n.factorial * (2 * n).factorial) := by rw [h3]
    _ = Nat.choose (6 * n) (3 * n) * (3 * n).factorial * (3 * n).factorial := by rw [h2]
    _ = (6 * n).factorial := h1

theorem nativeCoefficient_eq_integer (n : ℕ) :
    WPReview.nativeCoefficient n = (nativeMultinomial n : ℚ) / (1728 : ℚ) ^ n := by
  have hq : (nativeMultinomial n : ℚ) * (n.factorial : ℚ) ^ 3 *
      ((3 * n).factorial : ℚ) = ((6 * n).factorial : ℚ) := by
    exact_mod_cast multinomial_factorial_identity n
  unfold WPReview.nativeCoefficient
  field_simp
  linear_combination -hq

private theorem unitBlock_pos (p j : ℕ) : 0 < unitBlock p j := by
  unfold unitBlock
  apply Finset.prod_pos
  intro r hr
  have := (Finset.mem_Ico.mp hr).1
  omega

theorem native_multinomial_block_identity (p : ℕ) (hp : 1 ≤ p) :
    nativeMultinomial p * unitBlock p 0 ^ 3 =
      120 * unitBlock p 3 * unitBlock p 4 * unitBlock p 5 := by
  have hb1 := factorial_blocks p 1 hp
  have hb3 := factorial_blocks p 3 hp
  have hb6 := factorial_blocks p 6 hp
  norm_num [Finset.prod_range_succ] at hb1 hb3 hb6
  have hi := multinomial_factorial_identity p
  rw [hb1, hb3, hb6] at hi
  have hfactor : 0 < p ^ 6 * 6 * unitBlock p 0 * unitBlock p 1 * unitBlock p 2 := by
    have hp0 : 0 < p := by omega
    have hu0 := unitBlock_pos p 0
    have hu1 := unitBlock_pos p 1
    have hu2 := unitBlock_pos p 2
    positivity
  apply Nat.eq_of_mul_eq_mul_left hfactor
  convert hi using 1 <;> ring

theorem native_multinomial_congruent (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (nativeMultinomial p : ZMod (p ^ 3)) = 120 := by
  have he := congrArg (fun n : ℕ => (n : ZMod (p ^ 3)))
    (native_multinomial_block_identity p (by omega))
  push_cast at he
  rw [unit_block_congruent p 3 hp7, unit_block_congruent p 4 hp7,
    unit_block_congruent p 5 hp7] at he
  have hu : IsUnit (unitBlock p 0 : ZMod (p ^ 3)) := by
    simp only [unitBlock, zero_mul, zero_add, Nat.cast_prod]
    apply IsUnit.prod_iff.mpr
    intro r hr
    exact interval_unit p r Fact.out hr
  apply (hu.pow 3).mul_left_cancel
  linear_combination he

private theorem prime_not_dvd_1728 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬p ∣ 1728 := by
  have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h3 : ¬p ∣ 3 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  intro hd
  rw [show 1728 = 2 ^ 6 * 3 ^ 3 by norm_num] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact h2 (hp.dvd_of_dvd_pow h)
  · exact h3 (hp.dvd_of_dvd_pow h)

theorem native_factorial_normalization (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    WPReview.RationalCongruent p 3 (WPReview.nativeCoefficient p)
      (120 / (1728 : ℚ) ^ p) := by
  have hd : (p : ℤ) ^ 3 ∣ (nativeMultinomial p : ℤ) - 120 := by
    rw [← Nat.cast_pow]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [native_multinomial_congruent p hp7]
    ring
  have hdiff : WPReview.nativeCoefficient p - 120 / (1728 : ℚ) ^ p =
      (((nativeMultinomial p : ℤ) - 120 : ℤ) : ℚ) / (1728 : ℚ) ^ p := by
    rw [nativeCoefficient_eq_integer]
    push_cast
    ring
  have hden : (1728 : ℚ) ^ p ≠ 0 := pow_ne_zero p (by norm_num)
  have hvden : padicValRat p ((1728 : ℚ) ^ p) = 0 := by
    have hb := padicValRat.of_nat (p := p) (n := 1728)
    norm_num only [Nat.cast_ofNat] at hb
    rw [padicValRat.pow, hb,
      padicValNat.eq_zero_of_not_dvd (prime_not_dvd_1728 p Fact.out hp7)]
    simp
  by_cases hzero : (nativeMultinomial p : ℤ) - 120 = 0
  · left
    apply sub_eq_zero.mp
    rw [hdiff, hzero]
    simp
  · right
    have hnum : (((nativeMultinomial p : ℤ) - 120 : ℤ) : ℚ) ≠ 0 :=
      Int.cast_ne_zero.mpr hzero
    rw [hdiff, padicValRat.div hnum hden, hvden, sub_zero, padicValRat.of_int]
    have hval : 3 ≤ padicValInt p ((nativeMultinomial p : ℤ) - 120) :=
      ((padicValInt_dvd_iff 3 ((nativeMultinomial p : ℤ) - 120)).mp hd).resolve_left hzero
    exact_mod_cast hval

end WPNativeFactorialNormalization
