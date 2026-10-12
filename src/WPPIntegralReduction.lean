import WPNativeMomentDigitExpansion
import WPFiniteCartier
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators LaurentPolynomial
open LaurentPolynomial

namespace WPPIntegralReduction

theorem integral_iff_denominator_not_dvd (p : ℕ) [Fact p.Prime] (q : ℚ) :
    0 ≤ padicValRat p q ↔ ¬p ∣ q.den := by
  constructor
  · intro hq hd
    have hn : ¬p ∣ q.num.natAbs := by
      intro hdn
      have hpd1 : p ∣ 1 := by
        simpa only [q.reduced.gcd_eq_one] using Nat.dvd_gcd hdn hd
      have hp : p.Prime := Fact.out
      exact hp.ne_one (Nat.dvd_one.mp hpd1)
    have hvn := padicValNat.eq_zero_of_not_dvd hn
    have hvd := one_le_padicValNat_of_dvd q.den_ne_zero hd
    simp only [padicValRat, padicValInt, hvn, Nat.cast_zero, zero_sub] at hq
    omega
  · intro hd
    simp only [padicValRat, padicValNat.eq_zero_of_not_dvd hd,
      Nat.cast_zero, sub_zero]
    exact Int.natCast_nonneg _

theorem integral_denominator_cast_ne_zero (p : ℕ) [Fact p.Prime]
    (q : ℚ) (hq : 0 ≤ padicValRat p q) : (q.den : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact (integral_iff_denominator_not_dvd p q).mp hq

/-- The actual subring of rational coefficients with nonnegative p-valuation. -/
def integralRationals (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat p q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    by_cases hab : a + b = 0
    · simp [hab]
    · exact (le_min ha hb).trans (padicValRat.min_le_padicValRat_add hab)
  mul_mem' := by
    intro a b ha hb
    change 0 ≤ padicValRat p a at ha
    change 0 ≤ padicValRat p b at hb
    change 0 ≤ padicValRat p (a * b)
    by_cases ha0 : a = 0
    · simp [ha0]
    by_cases hb0 : b = 0
    · simp [hb0]
    rw [padicValRat.mul ha0 hb0]
    omega
  neg_mem' := by
    intro a ha
    change 0 ≤ padicValRat p a at ha
    change 0 ≤ padicValRat p (-a)
    simpa only [padicValRat.neg] using ha

/-- Rational reduction uses the literal reduced numerator and unit denominator. -/
def residueHom (p : ℕ) [Fact p.Prime] : integralRationals p →+* ZMod p where
  toFun q := (q.val : ZMod p)
  map_zero' := Rat.cast_zero
  map_one' := Rat.cast_one
  map_add' a b := Rat.cast_add_of_ne_zero
    (integral_denominator_cast_ne_zero p a.val a.property)
    (integral_denominator_cast_ne_zero p b.val b.property)
  map_mul' a b := Rat.cast_mul_of_ne_zero
    (integral_denominator_cast_ne_zero p a.val a.property)
    (integral_denominator_cast_ne_zero p b.val b.property)

theorem integral_residue_zero_iff (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : 0 ≤ padicValRat p q) :
    (q : ZMod p) = 0 ↔ WPReview.RationalCongruent p 1 q 0 := by
  have hd := (integral_iff_denominator_not_dvd p q).mp hq
  have hdc := integral_denominator_cast_ne_zero p q hq
  rw [Rat.cast_def, div_eq_zero_iff, or_iff_left hdc,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hvd := padicValNat.eq_zero_of_not_dvd hd
  rw [show (p : ℤ) ∣ q.num ↔ q.num = 0 ∨ 1 ≤ padicValInt p q.num by
    simpa only [pow_one] using (padicValInt_dvd_iff 1 q.num)]
  have hval : padicValRat p q = (padicValInt p q.num : ℤ) := by
    simp only [padicValRat, hvd, Nat.cast_zero, sub_zero]
  rw [WPReview.RationalCongruent, sub_zero, hval]
  constructor
  · rintro (h | h)
    · exact Or.inl (Rat.num_eq_zero.mp h)
    · exact Or.inr (by exact_mod_cast h)
  · rintro (h | h)
    · exact Or.inl (Rat.num_eq_zero.mpr h)
    · exact Or.inr (by exact_mod_cast h)

/-- Equality of actual residues is precisely first-digit rational congruence. -/
theorem integral_residue_eq_iff (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    (a : ZMod p) = (b : ZMod p) ↔ WPReview.RationalCongruent p 1 a b := by
  let aa : integralRationals p := ⟨a, ha⟩
  let bb : integralRationals p := ⟨b, hb⟩
  have hab : 0 ≤ padicValRat p (a - b) := (aa - bb).property
  change (a : ZMod p) = (b : ZMod p) ↔ WPGammaArithmetic.RationalCongruent p 1 a b
  rw [WPGammaArithmetic.rationalCongruent_iff_sub_zero]
  change (a : ZMod p) = (b : ZMod p) ↔ WPReview.RationalCongruent p 1 (a - b) 0
  rw [← integral_residue_zero_iff p (a - b) hab,
    Rat.cast_sub_of_ne_zero (integral_denominator_cast_ne_zero p a ha)
      (integral_denominator_cast_ne_zero p b hb), sub_eq_zero]

theorem cast_two_zpow (p : ℕ) [Fact p.Prime] (m : ℤ) :
    (((2 : ℚ) ^ m : ℚ) : ZMod p) = (2 : ZMod p) ^ m := by
  cases m with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast, Rat.cast_ofNat] using
      (Rat.cast_pow (α := ZMod p) (2 : ℚ) n)
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Rat.cast_pow]
    have hc : (((2 : ℚ)⁻¹ : ℚ) : ZMod p) = (2 : ZMod p)⁻¹ := by
      simpa only [Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 2)
    rw [hc]

theorem integer_denominator_unit (p : ℕ) (m : ℤ) (hm : ¬(p : ℤ) ∣ m) :
    padicValRat p (m : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hm]
  rfl

theorem integral_two_endpoint_difference (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) :
    0 ≤ padicValRat p ((2 : ℚ) ^ m - (2 : ℚ) ^ (-m)) := by
  let a : integralRationals p := ⟨(2 : ℚ) ^ m,
    by change 0 ≤ padicValRat p ((2 : ℚ)^m)
       rw [WPNativeMomentIntegrality.two_zpow_unit p hp m]⟩
  let b : integralRationals p := ⟨(2 : ℚ) ^ (-m),
    by change 0 ≤ padicValRat p ((2 : ℚ)^(-m))
       rw [WPNativeMomentIntegrality.two_zpow_unit p hp (-m)]⟩
  exact (a - b).property

/-- Nonresonant original primitive coefficients vanish after actual rational reduction. -/
theorem primitive_nonresonant_residue (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) (hm : ¬(p : ℤ) ∣ m) :
    (WPNativeMomentIntegrality.primitiveWeight p m : ZMod p) = 0 := by
  have hmc : (m : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hm
  have hpint : 0 ≤ padicValRat p (p : ℚ) := by
    rw [padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
  have hdiff := integral_two_endpoint_difference p hp m
  have hpden := integral_denominator_cast_ne_zero p (p : ℚ) hpint
  have hdiffden := integral_denominator_cast_ne_zero p _ hdiff
  have hmul : 0 ≤ padicValRat p
      ((p : ℚ) * ((2 : ℚ)^m - (2 : ℚ)^(-m))) := by
    let a : integralRationals p := ⟨(p : ℚ), hpint⟩
    let b : integralRationals p := ⟨_, hdiff⟩
    exact (a * b).property
  have hnum : (((m : ℚ).num : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Rat.num_intCast] using hmc
  unfold WPNativeMomentIntegrality.primitiveWeight
  rw [Rat.cast_div_of_ne_zero (integral_denominator_cast_ne_zero p _ hmul) hnum,
    Rat.cast_mul_of_ne_zero hpden hdiffden, Rat.cast_natCast,
    ZMod.natCast_self, zero_mul, zero_div]

/-- At a signed resonance the prime cancels in Q before residue reduction. -/
theorem primitive_resonant_rewrite (p : ℕ) [Fact p.Prime] (b : ℤ) :
    WPNativeMomentIntegrality.primitiveWeight p (b * (p : ℤ)) =
      ((2 : ℚ) ^ (b * (p : ℤ)) - (2 : ℚ) ^ (-(b * (p : ℤ)))) / (b : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  unfold WPNativeMomentIntegrality.primitiveWeight
  push_cast
  rw [mul_comm (p : ℚ)]
  rw [mul_div_mul_right _ _ hpq]

/-- The actual resonant two endpoints reduce using their full signed exponent. -/
theorem primitive_resonant_residue (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (b : ℤ) (hb : ¬(p : ℤ) ∣ b) :
    (WPNativeMomentIntegrality.primitiveWeight p (b * (p : ℤ)) : ZMod p) =
      ((2 : ZMod p) ^ b - (2 : ZMod p) ^ (-b)) / (b : ZMod p) := by
  have hbc : (b : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb
  have hdiff := integral_two_endpoint_difference p hp (b * (p : ℤ))
  have hnum : (((b : ℚ).num : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Rat.num_intCast] using hbc
  rw [primitive_resonant_rewrite,
    Rat.cast_div_of_ne_zero (integral_denominator_cast_ne_zero p _ hdiff) hnum,
    Rat.cast_sub_of_ne_zero
      (integral_denominator_cast_ne_zero p _
        (by rw [WPNativeMomentIntegrality.two_zpow_unit p hp (b * (p : ℤ))]))
      (integral_denominator_cast_ne_zero p _
        (by rw [WPNativeMomentIntegrality.two_zpow_unit p hp (-(b * (p : ℤ)))])),
    cast_two_zpow, cast_two_zpow, Rat.cast_intCast]
  have hpow (z : ℤ) : (2 : ZMod p) ^ (z * (p : ℤ)) = (2 : ZMod p) ^ z := by
    rw [mul_comm z, zpow_mul, zpow_natCast, ZMod.pow_card]
  rw [hpow, show -(b * (p : ℤ)) = (-b) * (p : ℤ) by ring, hpow]

theorem primitive_weight_general_integral (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) (hm : m ≠ 0) (hbound : m.natAbs < p ^ 2) :
    0 ≤ padicValRat p (WPNativeMomentIntegrality.primitiveWeight p m) := by
  let a : integralRationals p := ⟨(p : ℚ) / (m : ℚ),
    WPNativeMomentIntegrality.prime_over_small_integer_integral p m hm hbound⟩
  let b : integralRationals p := ⟨(2 : ℚ)^m - (2 : ℚ)^(-m),
    integral_two_endpoint_difference p hp m⟩
  have h := (a * b).property
  change 0 ≤ padicValRat p
    ((p : ℚ) / (m : ℚ) * ((2 : ℚ)^m - (2 : ℚ)^(-m))) at h
  simpa only [WPNativeMomentIntegrality.primitiveWeight, div_mul_eq_mul_div] using h

theorem resonant_quotient_unit (p : ℕ) [Fact p.Prime] (m b : ℤ)
    (hm : m ≠ 0) (hbound : m.natAbs < p ^ 2)
    (hsplit : m = b * (p : ℤ)) : ¬(p : ℤ) ∣ b := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hb0 : b ≠ 0 := by intro h; simp [h, hsplit] at hm
  have hbabs : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
  have habs : m.natAbs = b.natAbs * p := by
    rw [hsplit, Int.natAbs_mul, Int.natAbs_natCast]
  have hblt : b.natAbs < p := by
    rw [habs] at hbound
    nlinarith
  intro hd
  have hdabs : p ∣ b.natAbs := Int.natCast_dvd.mp hd
  have hle := Nat.le_of_dvd hbabs hdabs
  omega

/-- Every original finite primitive index has its actual signed quotient selection. -/
theorem primitive_residue_selection (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (m : ℤ) (hm : m ≠ 0) (hbound : m.natAbs < p ^ 2) :
    (WPNativeMomentIntegrality.primitiveWeight p m : ZMod p) =
      if (p : ℤ) ∣ m then
        ((2 : ZMod p) ^ (m / (p : ℤ)) - (2 : ZMod p) ^ (-(m / (p : ℤ)))) /
          ((m / (p : ℤ) : ℤ) : ZMod p)
      else 0 := by
  by_cases hd : (p : ℤ) ∣ m
  · rw [if_pos hd]
    have hsplit : m = (m / (p : ℤ)) * (p : ℤ) := (Int.ediv_mul_cancel hd).symm
    have hb := resonant_quotient_unit p m (m / (p : ℤ)) hm hbound hsplit
    have he := primitive_resonant_residue p hp (m / (p : ℤ)) hb
    simpa only [← hsplit] using he
  · rw [if_neg hd]
    exact primitive_nonresonant_residue p hp m hd

theorem cast_sum_integral (p : ℕ) [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    (((∑ i ∈ s, f i : ℚ) : ℚ) : ZMod p) = ∑ i ∈ s, (f i : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs (j : ι) (hj : j ∈ s) := hf j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ padicValRat p (∑ j ∈ s, f j) :=
      (integralRationals p).sum_mem hfs
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      Rat.cast_add_of_ne_zero (integral_denominator_cast_ne_zero p _ hfi)
        (integral_denominator_cast_ne_zero p _ hsum), ih hfs]

/-- Whole finite Laurent primitive reduction: no nonresonant or signed band is omitted. -/
theorem finite_primitive_residue (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (s : Finset ℤ) (a : ℤ → ℚ)
    (ha : ∀ j ∈ s, 0 ≤ padicValRat p (a j))
    (hzero : ∀ j ∈ s, j + 1 ≠ 0)
    (hbound : ∀ j ∈ s, (j + 1).natAbs < p ^ 2) :
    (((∑ j ∈ s, a j * WPNativeMomentIntegrality.primitiveWeight p (j + 1) : ℚ) : ℚ) :
        ZMod p) =
      ∑ j ∈ s, if (p : ℤ) ∣ j + 1 then
        (a j : ZMod p) *
          (((2 : ZMod p) ^ ((j + 1) / (p : ℤ)) -
              (2 : ZMod p) ^ (-((j + 1) / (p : ℤ)))) /
            (((j + 1) / (p : ℤ) : ℤ) : ZMod p))
        else 0 := by
  classical
  have hw (j : ℤ) (hj : j ∈ s) :=
    primitive_weight_general_integral p hp (j + 1) (hzero j hj) (hbound j hj)
  have hterm (j : ℤ) (hj : j ∈ s) :
      0 ≤ padicValRat p (a j * WPNativeMomentIntegrality.primitiveWeight p (j + 1)) :=
    (integralRationals p).mul_mem (ha j hj) (hw j hj)
  rw [cast_sum_integral p s _ hterm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Rat.cast_mul_of_ne_zero (integral_denominator_cast_ne_zero p _ (ha j hj))
    (integral_denominator_cast_ne_zero p _ (hw j hj)),
    primitive_residue_selection p hp (j + 1) (hzero j hj) (hbound j hj)]
  split_ifs <;> simp

/-- The two actual reduced endpoints, with their signed primitive index. -/
def fieldWeight (p : ℕ) [Fact p.Prime] (m : ℤ) : ZMod p :=
  ((2 : ZMod p)^m - (2 : ZMod p)^(-m)) / (m : ZMod p)

noncomputable def fieldPrimitive (p : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (Finsupp.linearCombination (ZMod p) (fun j : ℤ => fieldWeight p (j + 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

noncomputable def selectedPrimitive (p : ℕ) [Fact p.Prime] :
    (ZMod p)[T;T⁻¹] →ₗ[ZMod p] ZMod p :=
  (Finsupp.linearCombination (ZMod p) (fun j : ℤ =>
    if (p : ℤ) ∣ j + 1 then fieldWeight p ((j + 1) / (p : ℤ)) else 0)).comp
      (AddMonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem fieldPrimitive_monomial (p : ℕ) [Fact p.Prime] (a : ZMod p) (j : ℤ) :
    fieldPrimitive p (C a * T j) = a * fieldWeight p (j + 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single j a) = _
  rw [Finsupp.linearCombination_single]
  rfl

theorem selectedPrimitive_monomial (p : ℕ) [Fact p.Prime] (a : ZMod p) (j : ℤ) :
    selectedPrimitive p (C a * T j) =
      a * (if (p : ℤ) ∣ j + 1 then fieldWeight p ((j + 1) / (p : ℤ)) else 0) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination (ZMod p) _ (Finsupp.single j a) = _
  rw [Finsupp.linearCombination_single]
  rfl

/-- Exact equality of complete finite selected and Cartier primitive functionals. -/
theorem fieldPrimitive_cartier (p : ℕ) [Fact p.Prime] (P : (ZMod p)[T;T⁻¹]) :
    fieldPrimitive p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos P) =
      selectedPrimitive p P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [WPFiniteCartier.cartier_add, map_add, map_add, hP, hQ]
  | C_mul_T j a =>
    rw [selectedPrimitive_monomial]
    by_cases hd : (p : ℤ) ∣ j + 1
    · rw [if_pos hd]
      let b := (j + 1) / (p : ℤ)
      have hj : j = (p : ℤ) * ((b - 1) + 1) - 1 := by
        have he := Int.mul_ediv_cancel' hd
        dsimp only [b]
        linear_combination -he
      rw [hj, WPFiniteCartier.cartier_selected_monomial, fieldPrimitive_monomial]
      have hsplit : ((p : ℤ) * ((b - 1) + 1) - 1 + 1) / (p : ℤ) = b := by
        have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        rw [sub_add_cancel, sub_add_cancel]
        exact Int.mul_ediv_cancel_left b hpz
      rw [hsplit]
      congr 2
      ring
    · rw [if_neg hd, WPFiniteCartier.cartier_unselected_monomial p _ _ _ hd,
        map_zero, mul_zero]

/-- Actual rational coefficients reduced individually; unit denominators are checked at use. -/
noncomputable def reduceLaurent (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹]) :
    (ZMod p)[T;T⁻¹] :=
  AddMonoidAlgebra.ofCoeff (P.coeff.mapRange (fun q : ℚ => (q : ZMod p)) Rat.cast_zero)

theorem reduceLaurent_coeff (p : ℕ) [Fact p.Prime] (P : ℚ[T;T⁻¹]) (j : ℤ) :
    (reduceLaurent p P).coeff j = (P.coeff j : ZMod p) := rfl

noncomputable def rationalPrimitive (p : ℕ) (P : ℚ[T;T⁻¹]) : ℚ :=
  P.coeff.sum fun j a => a * WPNativeMomentIntegrality.primitiveWeight p (j + 1)

/-- NC66's entire finite primitive reduces to its actual Cartier differential. -/
theorem rationalPrimitive_residue_cartier (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : ℚ[T;T⁻¹])
    (hcoeff : ∀ j, 0 ≤ padicValRat p (P.coeff j))
    (hzero : ∀ j ∈ P.coeff.support, j + 1 ≠ 0)
    (hbound : ∀ j ∈ P.coeff.support, (j + 1).natAbs < p ^ 2) :
    (rationalPrimitive p P : ZMod p) =
      fieldPrimitive p (WPFiniteCartier.cartier p (Fact.out : p.Prime).pos (reduceLaurent p P)) := by
  rw [fieldPrimitive_cartier]
  have he := finite_primitive_residue p hp P.coeff.support P.coeff
    (fun j _hj => hcoeff j) hzero hbound
  change (rationalPrimitive p P : ZMod p) = _ at he
  rw [he]
  unfold selectedPrimitive reduceLaurent
  change _ = (P.coeff.mapRange (fun q : ℚ => (q : ZMod p)) Rat.cast_zero).sum
    (fun j a => a * (if (p : ℤ) ∣ j + 1 then fieldWeight p ((j + 1) / (p : ℤ)) else 0))
  rw [Finsupp.sum_mapRange_index (by intro j; simp)]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro j _hj
  unfold fieldWeight
  split_ifs with h <;> simp [h]

end WPPIntegralReduction
