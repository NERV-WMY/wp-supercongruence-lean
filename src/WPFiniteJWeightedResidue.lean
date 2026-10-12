import WPFiniteJCarrier
import Mathlib.Algebra.Polynomial.Reverse

open scoped Polynomial LaurentPolynomial
open Polynomial

namespace WPFiniteJWeightedResidue

open WPFiniteJSource WPFiniteJHighCoefficient WPFiniteFifthSourceContraction WPFiniteJCarrier

variable {K : Type*} [Field K]

/-- The full infinity coefficient of dlogQ=2/(x-4)+1/(x-1/4)-3/x.
    Negative powers cannot meet this density; its constant geometric row is zero. -/
noncomputable def infinityQ (P : K[T;T⁻¹]) : K :=
  -2 * (LaurentPolynomial.trunc P).eval 4 -
    (LaurentPolynomial.trunc P).eval (1 / 4) +
    3 * (LaurentPolynomial.trunc P).coeff 0

theorem trunc_coeff (P : K[T;T⁻¹]) (n : ℕ) :
    (LaurentPolynomial.trunc P).coeff n = P.coeff (n : ℤ) := by
  rfl

theorem trunc_C_mul (a : K) (P : K[T;T⁻¹]) :
    LaurentPolynomial.trunc (LaurentPolynomial.C a * P) = C a * LaurentPolynomial.trunc P := by
  ext n
  rw [trunc_coeff, coeff_C_mul, trunc_coeff]
  have he := shifted_coeff a 0 (n : ℤ) P
  simpa only [LaurentPolynomial.T_zero, mul_one, sub_zero] using he

theorem trunc_invert (P : K[X]) :
    LaurentPolynomial.trunc (LaurentPolynomial.invert P.toLaurent) = C (P.coeff 0) := by
  ext n
  rw [trunc_coeff, LaurentPolynomial.invert_apply]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, neg_zero, coeff_C_zero]
    exact toLaurent_coeff_nat P 0
  · rw [toLaurent_coeff_outside P _ (Or.inl (by omega)), coeff_C, if_neg hn]

theorem trunc_shift_invert (P : K[X]) (n : ℕ) :
    LaurentPolynomial.trunc (LaurentPolynomial.T (n : ℤ) *
      LaurentPolynomial.invert P.toLaurent) = reflect n (lowBand (n + 1) P) := by
  ext j
  rw [trunc_coeff, coeff_reflect, lowBand_coeff]
  have he := shifted_coeff (1 : K) (n : ℤ) (j : ℤ)
    (LaurentPolynomial.invert P.toLaurent)
  simp only [map_one, one_mul, LaurentPolynomial.invert_apply] at he
  rw [he]
  by_cases hj : j ≤ n
  · rw [revAt_le hj, if_pos (by omega)]
    rw [show -((j : ℤ) - n) = ((n - j : ℕ) : ℤ) by omega, toLaurent_coeff_nat]
  · rw [revAt_eq_self_of_lt (by omega), if_neg (by omega)]
    exact toLaurent_coeff_outside P _ (Or.inl (by omega))

theorem infinityQ_add (P Q : K[T;T⁻¹]) : infinityQ (P + Q) = infinityQ P + infinityQ Q := by
  simp only [infinityQ, map_add, eval_add, coeff_add]
  ring

theorem infinityQ_sub (P Q : K[T;T⁻¹]) : infinityQ (P - Q) = infinityQ P - infinityQ Q := by
  simp only [infinityQ, map_sub, eval_sub, coeff_sub]
  ring

theorem infinityQ_C_mul (a : K) (P : K[T;T⁻¹]) :
    infinityQ (LaurentPolynomial.C a * P) = a * infinityQ P := by
  simp only [infinityQ, trunc_C_mul, eval_mul, eval_C, coeff_C_mul]
  ring

theorem infinityQ_single (a : K) (n : ℤ) :
    infinityQ (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      if 0 < n then -a * (2 * (4 : K) ^ n.toNat + (1 / 4 : K) ^ n.toNat) else 0 := by
  unfold infinityQ
  rw [LaurentPolynomial.trunc_C_mul_T]
  by_cases hn : 0 < n
  · rw [if_pos (by omega), if_pos hn]
    simp only [eval_monomial, coeff_monomial, if_neg (show n.toNat ≠ 0 by omega)]
    ring
  · rw [if_neg hn]
    by_cases hz : n = 0
    · subst n
      simp only [le_refl, if_true, Int.toNat_zero, monomial_zero_left, eval_C, coeff_C_zero]
      ring
    · rw [if_neg (by omega)]
      simp

theorem infinityQ_polynomial (P : K[X]) :
    infinityQ P.toLaurent = -2 * P.eval 4 - P.eval (1 / 4) + 3 * P.coeff 0 := by
  rw [infinityQ, trunc_toLaurent]

/-- Literal finite convolution with the geometric dlogQ rows at infinity. -/
noncomputable def fullInfinityCoefficient (P : K[T;T⁻¹]) : K :=
  -P.coeff.sum (fun n a => if 0 < n then a *
    (2 * (4 : K) ^ n.toNat + (1 / 4 : K) ^ n.toNat) else 0)

theorem infinityQ_full_coefficient (P : K[T;T⁻¹]) :
    infinityQ P = fullInfinityCoefficient P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [infinityQ_add, hP, hQ]
    unfold fullInfinityCoefficient
    rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index]
    · ring
    · intro n
      split_ifs <;> simp
    · intro n _ a b
      split_ifs <;> ring
  | C_mul_T n a =>
    rw [infinityQ_single]
    unfold fullInfinityCoefficient
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    change (if 0 < n then -a * (2 * (4 : K) ^ n.toNat + (1 / 4 : K) ^ n.toNat) else 0) =
      -(Finsupp.single n a).sum _
    rw [Finsupp.sum_single_index]
    · split_ifs <;> ring
    · split_ifs <;> simp

theorem lowBand_succ (n : ℕ) (P : K[X]) :
    lowBand (n + 1) P = lowBand n P + monomial n (P.coeff n) := by
  ext j
  rw [coeff_add, lowBand_coeff, lowBand_coeff, coeff_monomial]
  by_cases hj : j < n
  · rw [if_pos (by omega), if_pos hj, if_neg (by omega), add_zero]
  · by_cases hje : j = n
    · subst j
      simp
    · rw [if_neg (by omega), if_neg hj, if_neg (by omega), add_zero]

theorem trunc_shift_invert_eval (P : K[X]) (n : ℕ) (x : K) (hx : x ≠ 0) :
    (LaurentPolynomial.trunc (LaurentPolynomial.T (n : ℤ) *
      LaurentPolynomial.invert P.toLaurent)).eval x = x ^ n * (lowBand (n + 1) P).eval x⁻¹ := by
  rw [trunc_shift_invert]
  let _ : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have hdeg : (lowBand (n + 1) P).natDegree ≤ n := by
    simpa only [Nat.add_sub_cancel] using (cutoff_band_degree (n + 1) P).1
  have he := eval₂_reflect_mul_pow (RingHom.id K) x⁻¹ n (lowBand (n + 1) P) hdeg
  have he' : (reflect n (lowBand (n + 1) P)).eval x * (x⁻¹) ^ n =
      (lowBand (n + 1) P).eval x⁻¹ := by
    simpa only [eval₂_id, invOf_eq_inv, inv_inv] using he
  apply (mul_right_cancel₀ (pow_ne_zero n (inv_ne_zero hx)))
  rw [he']
  rw [mul_assoc, mul_comm ((lowBand (n + 1) P).eval x⁻¹), ← mul_assoc,
    ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]

theorem low_original_end (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (e : K) (he : e ^ p = e) (hz : (HJP p : K[X]).eval e = 0) :
    (lowBand p (HJP p)).eval e =
      -e * ((HJP p : K[X]).coeff p + (strictHigh p : K[X]).eval e) := by
  have hdeg := HJP_natDegree_le (K := K) p hp
  have hsplit := congrArg (fun P : K[X] => P.eval e)
    (full_cutoff_split p (HJP p : K[X]) (by omega))
  rw [hz, eval_add, eval_mul, eval_pow, eval_X, he] at hsplit
  unfold strictHigh
  rw [eval_sub, eval_C]
  linear_combination -hsplit

/-- The complete canceled original JT2b Laurent density before multiplication by dlogQ. -/
noncomputable def canceledJ (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 15 : K) *
    ((LaurentPolynomial.C 4 * LaurentPolynomial.T (p : ℤ) - LaurentPolynomial.C 11) *
      ((HJP p).toLaurent + LaurentPolynomial.invert (HJP p).toLaurent))

theorem actual_weighted_J (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    infinityQ (canceledJ p : K[T;T⁻¹]) =
      -11 * (HJP p : K[X]).coeff 0 / 5 + 4 * (HJP p : K[X]).coeff p / 5 +
        8 * (strictHigh p : K[X]).eval (1 / 4) / 15 +
        4 * (strictHigh p : K[X]).eval 4 / 15 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by rw [show (15 : K) = 3 * 5 by ring]; exact mul_ne_zero h3 h5
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have ha : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hai : (1 / 4 : K)⁻¹ = 4 := by simp
  have h41 : (4 : K)⁻¹ = 1 / 4 := by simp
  have hends := HJP_original_ends (K := K) p hp
  have hlo4 := low_original_end p hp (4 : K) h4p hends.1
  have hloa := low_original_end p hp (1 / 4 : K) ha hends.2
  have href4 := trunc_shift_invert_eval (HJP p : K[X]) p (4 : K) h4
  have hrefa := trunc_shift_invert_eval (HJP p : K[X]) p (1 / 4 : K) (div_ne_zero one_ne_zero h4)
  rw [h4p, h41, lowBand_succ, eval_add, eval_monomial, ha] at href4
  rw [ha, hai, lowBand_succ, eval_add, eval_monomial, h4p] at hrefa
  have hrc : (LaurentPolynomial.trunc (LaurentPolynomial.T (p : ℤ) *
      LaurentPolynomial.invert (HJP p : K[X]).toLaurent)).coeff 0 = (HJP p : K[X]).coeff p := by
    rw [trunc_shift_invert, coeff_reflect, revAt_zero, lowBand_coeff, if_pos (by omega)]
  have href : infinityQ (LaurentPolynomial.T (p : ℤ) *
      LaurentPolynomial.invert (HJP p : K[X]).toLaurent) =
      -8 * (lowBand p (HJP p : K[X])).eval (1 / 4) -
        (lowBand p (HJP p : K[X])).eval 4 / 4 := by
    unfold infinityQ
    rw [href4, hrefa, hrc]
    field_simp [h4]
    ring
  have hinv : infinityQ (LaurentPolynomial.invert (HJP p : K[X]).toLaurent) = 0 := by
    simp only [infinityQ, trunc_invert, eval_C, coeff_C_zero]
    ring
  have hpoly : (LaurentPolynomial.C 4 * LaurentPolynomial.T (p : ℤ) - LaurentPolynomial.C 11) *
      (HJP p : K[X]).toLaurent = ((C 4 * X ^ p - C 11) * HJP p : K[X]).toLaurent := by
    simp only [map_mul, map_sub, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  have hlocal : infinityQ (((C 4 * X ^ p - C 11) * HJP p : K[X]).toLaurent) =
      -33 * (HJP p : K[X]).coeff 0 := by
    rw [infinityQ_polynomial, coeff_zero_eq_eval_zero]
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, hends.1, hends.2,
      mul_zero, zero_pow (show p ≠ 0 by omega), coeff_zero_eq_eval_zero]
    ring
  unfold canceledJ
  rw [infinityQ_C_mul, mul_add, infinityQ_add, hpoly, hlocal,
    sub_mul, mul_assoc, infinityQ_sub, infinityQ_C_mul, infinityQ_C_mul, href, hinv,
    hlo4, hloa]
  field_simp [h4, h5, h15]
  ring

theorem actual_full_J_functional (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (2 : K) * infinityQ (canceledJ p) / 3 -
      207 * (WPFiniteJCarrier.GJ p : K[T;T⁻¹]).coeff (2 * (p : ℤ)) / 4 =
        JfullFunctional p := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by rw [show (15 : K) = 3 * 5 by ring]; exact mul_ne_zero h3 h5
  have h45 : (45 : K) ≠ 0 := by rw [show (45 : K) = 3 ^ 2 * 5 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) h5
  rw [actual_weighted_J p hp, actual_GJ_2p_coefficient p hp]
  unfold JfullFunctional JendpointFunctional
  rw [coeff_zero_eq_eval_zero]
  field_simp [h3, h4, h5, h15, h45]
  ring

theorem inversion_eval (P : K[T;T⁻¹]) (x : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) x (LaurentPolynomial.invert P) =
      LaurentPolynomial.eval₂ (RingHom.id K) x⁻¹ P := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | C_mul_T n a =>
    simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.id_apply]
    simp

theorem GJ_eval (p : ℕ) (x : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) x (GJ p) =
      (17 - 4 * (x : K) ^ p - 4 * ((x : K)⁻¹) ^ p) / 45 *
        ((HJP p : K[X]).eval (x : K) + (HJP p : K[X]).eval (x : K)⁻¹) := by
  unfold GJ
  simp only [map_sub, map_mul, map_add, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T_n, LaurentPolynomial.eval₂_T_neg_n,
    LaurentPolynomial.T_zero, map_one, RingHom.id_apply,
    inversion_eval, LaurentPolynomial.eval₂_toLaurent, eval₂_id,
    Units.val_inv_eq_inv_val]
  ring

theorem canceledJ_eval (p : ℕ) (x : Kˣ) :
    LaurentPolynomial.eval₂ (RingHom.id K) x (canceledJ p) =
      (4 * (x : K) ^ p - 11) / 15 *
        ((HJP p : K[X]).eval (x : K) + (HJP p : K[X]).eval (x : K)⁻¹) := by
  unfold canceledJ
  simp only [map_sub, map_mul, map_add, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T_n, RingHom.id_apply, inversion_eval,
    LaurentPolynomial.eval₂_toLaurent, eval₂_id, Units.val_inv_eq_inv_val]
  ring

/-- Original rational Frobenius weight; the surrounding density supplies dlogQ. -/
noncomputable def originalWeight (p : ℕ) (x : K) : K :=
  3 * (x * (4 * x - 11) / ((4 - x) * (4 * x - 1))) ^ p

theorem original_weight_scalar (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : K) (hx : x ≠ 0) (h4x : 4 - x ≠ 0) (hx4 : 4 * x - 1 ≠ 0) :
    originalWeight p x * (17 - 4 * x ^ p - 4 * (x⁻¹) ^ p) / 45 =
      (4 * x ^ p - 11) / 15 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by rw [show (15 : K) = 3 * 5 by ring]; exact mul_ne_zero h3 h5
  have h45 : (45 : K) ≠ 0 := by rw [show (45 : K) = 3 ^ 2 * 5 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) h5
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have h11p : (11 : K) ^ p = 11 := WPFiniteField.natCast_pow_char p 11
  have hpB : (4 * x - 11) ^ p = 4 * x ^ p - 11 := by rw [sub_pow_char, mul_pow, h4p, h11p]
  have hpA : (4 - x) ^ p = 4 - x ^ p := by rw [sub_pow_char, h4p]
  have hpA' : (4 * x - 1) ^ p = 4 * x ^ p - 1 := by rw [sub_pow_char, mul_pow, h4p, one_pow]
  have hA : 4 - x ^ p ≠ 0 := by rw [← hpA]; exact pow_ne_zero p h4x
  have hA' : 4 * x ^ p - 1 ≠ 0 := by rw [← hpA']; exact pow_ne_zero p hx4
  have hA'' : -1 + x ^ p * 4 ≠ 0 := by
    convert hA' using 1
    ring
  unfold originalWeight
  rw [div_pow, mul_pow, mul_pow, hpB, hpA, hpA', inv_pow]
  field_simp [pow_ne_zero p hx, hA, hA', hA'', h15, h45]
  ring_nf
  field_simp [hA'']
  ring

theorem original_weight_cancellation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (x : Kˣ) (h4x : 4 - (x : K) ≠ 0) (hx4 : 4 * (x : K) - 1 ≠ 0) :
    originalWeight p (x : K) * LaurentPolynomial.eval₂ (RingHom.id K) x (GJ p) =
      LaurentPolynomial.eval₂ (RingHom.id K) x (canceledJ p) := by
  rw [GJ_eval, canceledJ_eval, ← mul_assoc]
  congr 1
  simpa only [div_eq_mul_inv, mul_assoc] using
    original_weight_scalar p hp (x : K) x.ne_zero h4x hx4

end WPFiniteJWeightedResidue
