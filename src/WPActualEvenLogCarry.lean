import WPActualRankTwoCarryField
import Mathlib.Data.Nat.Choose.Central

open scoped Polynomial BigOperators
open Polynomial WPActualGaussProper WPActualRankTwoComparison
  WPActualRankTwoLegendreField WPActualRankTwoFirstLift WPActualNativeHasse

namespace WPActualEvenLogCarry

set_option maxHeartbeats 800000

/-- The literal central-binomial coefficient used by NC81, in any coefficient field. -/
noncomputable def centralCoefficient (K : Type*) [Field K] (n : ℕ) : K :=
  (Nat.centralBinom n : K) / (4 : K) ^ n

theorem centralCoefficient_zero (K : Type*) [Field K] : centralCoefficient K 0 = 1 := by
  simp [centralCoefficient]

theorem centralCoefficient_recurrence {K : Type*} [Field K] (h4 : (4 : K) ≠ 0) (n : ℕ) :
    2 * ((n : K) + 1) * centralCoefficient K (n + 1) =
      (2 * (n : K) + 1) * centralCoefficient K n := by
  have h := congrArg (fun z : ℕ => (z : K)) (Nat.succ_mul_centralBinom_succ n)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  unfold centralCoefficient
  rw [pow_succ]
  field_simp [h4]
  linear_combination 2 * h

theorem prime_half_identity (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * ((p - 1) / 2) + 1 = p := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem prime_half_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
  have h := congrArg (fun z : ℕ => (z : ZMod p)) (prime_half_identity p hp)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_self] using h

theorem signedChoose_recurrence (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hn : n ≤ (p - 1) / 2) :
    2 * ((n : ZMod p) + 1) * ((-1 : ZMod p) ^ (n + 1) * (((p - 1) / 2).choose (n + 1) : ZMod p)) =
      (2 * (n : ZMod p) + 1) * ((-1 : ZMod p) ^ n * (((p - 1) / 2).choose n : ZMod p)) := by
  have h := congrArg (fun z : ℕ => (z : ZMod p))
    (Nat.choose_succ_right_eq ((p - 1) / 2) n)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_add, Nat.cast_one] at h
  have hN := prime_half_field p hp
  rw [pow_succ]
  linear_combination -2 * (-1 : ZMod p) ^ n * h -
    ((-1 : ZMod p) ^ n * (((p - 1) / 2).choose n : ZMod p)) * hN

/-- The entire central-binomial row has the literal half-binomial field reduction. -/
theorem centralCoefficient_field_choose (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hn : n ≤ (p - 1) / 2) :
    centralCoefficient (ZMod p) n = (-1 : ZMod p) ^ n * (((p - 1) / 2).choose n : ZMod p) := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using small_cast_ne_zero p 4 (by omega) (by omega)
  induction n with
  | zero => simp [centralCoefficient_zero]
  | succ n ih =>
    have hin := ih (by omega)
    have h1 := centralCoefficient_recurrence h4 n
    have h2 := signedChoose_recurrence p n hp (by omega)
    rw [hin] at h1
    have hunit : (2 : ZMod p) * ((n : ZMod p) + 1) ≠ 0 := by
      apply mul_ne_zero
      · simpa only [Nat.cast_ofNat] using small_cast_ne_zero p 2 (by omega) (by omega)
      · simpa only [Nat.cast_add, Nat.cast_one] using small_cast_ne_zero p (n + 1) (by omega) (by omega)
    apply (mul_left_cancel₀ hunit)
    exact h1.trans h2.symm

theorem coeff_comp_neg {K : Type*} [CommRing K] (Q : K[X]) (n : ℕ) :
    (Q.comp (-X)).coeff n = Q.coeff n * (-1 : K) ^ n := by
  refine Polynomial.induction_on Q (fun a => ?_) (fun f g hf hg => ?_) (fun d a _ => ?_)
  · simp only [C_comp, coeff_C]
    by_cases hn : n = 0 <;> simp [hn]
  · rw [add_comp, coeff_add, coeff_add, hf, hg]; ring
  · have hpow : (-X : K[X]) ^ (d + 1) = C ((-1 : K) ^ (d + 1)) * X ^ (d + 1) := by
      calc
        _ = (C (-1 : K) * X) ^ (d + 1) := by simp
        _ = _ := by rw [mul_pow, ← C_pow]
    rw [mul_comp, C_comp, pow_comp, X_comp, hpow, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    by_cases hn : d + 1 = n
    · subst n; simp
    · simp only [if_neg (Ne.symm hn), zero_mul]

theorem coeff_one_sub_X_pow {K : Type*} [CommRing K] (N r : ℕ) :
    ((1 - X : K[X]) ^ N).coeff r = (-1 : K) ^ r * (N.choose r : K) := by
  have he : (1 - X : K[X]) ^ N = ((1 + X) ^ N).comp (-X) := by simp [sub_eq_add_neg]
  rw [he, coeff_comp_neg, coeff_one_add_X_pow]
  ring

/-- The whole finite log in q; division is only by the original 2r units. -/
noncomputable def centralLogPolynomial (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  rankCoefficientPolynomial ((p - 1) / 2)
    (fun r => if r = 0 then 0 else centralCoefficient (ZMod p) r / (2 * (r : ZMod p)))

theorem centralLogPolynomial_degree (p : ℕ) [Fact p.Prime] :
    (centralLogPolynomial p).natDegree ≤ (p - 1) / 2 := rankCoefficientPolynomial_degree _ _

theorem centralLogPolynomial_origin (p : ℕ) [Fact p.Prime] :
    (centralLogPolynomial p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, centralLogPolynomial, rankCoefficientPolynomial_coeff]
  simp

theorem centralLogPolynomial_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * theta (centralLogPolynomial p) = (1 - X) ^ ((p - 1) / 2) - 1 := by
  ext r
  rw [coeff_ofNat_mul, theta_coeff, coeff_sub, coeff_one_sub_X_pow, coeff_one]
  cases r with
  | zero => simp
  | succ r =>
    rw [centralLogPolynomial, rankCoefficientPolynomial_coeff]
    simp only [Nat.lt_succ_iff]
    by_cases hr : r + 1 ≤ (p - 1) / 2
    · rw [if_pos hr, if_neg (by omega : r + 1 ≠ 0)]
      have hu : (2 : ZMod p) * ((r + 1 : ℕ) : ZMod p) ≠ 0 := by
        apply mul_ne_zero
        · simpa only [Nat.cast_ofNat] using small_cast_ne_zero p 2 (by omega) (by omega)
        · exact small_cast_ne_zero p (r + 1) (by omega) (by omega)
      simp only [if_neg (by omega : r + 1 ≠ 0), sub_zero]
      calc
        _ = (2 * ((r + 1 : ℕ) : ZMod p)) *
            (centralCoefficient (ZMod p) (r + 1) / (2 * ((r + 1 : ℕ) : ZMod p))) := by ring
        _ = centralCoefficient (ZMod p) (r + 1) := mul_div_cancel₀ _ hu
        _ = _ := centralCoefficient_field_choose p (r + 1) hp hr
    · rw [if_neg hr, Nat.choose_eq_zero_of_lt (by omega)]
      simp

theorem centralLogPolynomial_pullback_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * ((centralLogPolynomial p).comp (1 - X ^ 2)).derivative = X - X ^ p := by
  have h := congrArg (fun P : (ZMod p)[X] => P.comp (1 - X ^ 2))
    (centralLogPolynomial_source p (by omega : 7 ≤ p))
  simp only [theta, mul_comp, ofNat_comp, X_comp, sub_comp, pow_comp, one_comp] at h
  have hexp : 2 * ((p - 1) / 2) = p - 1 := by have := prime_half_identity p (by omega); omega
  rw [show (1 - (1 - X ^ 2) : (ZMod p)[X]) = X ^ 2 by ring,
    ← pow_mul, hexp] at h
  rw [derivative_comp, derivative_sub, derivative_one, derivative_X_pow]
  norm_num [map_ofNat] at h ⊢
  have hexp1 : p - 1 + 1 = p := by omega
  have hx : (X : (ZMod p)[X]) * X ^ (p - 1) = X ^ p := by rw [← pow_succ', hexp1]
  linear_combination -X * h - hx

theorem centralLogPolynomial_pullback_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((centralLogPolynomial p).comp (1 - X ^ 2)).natDegree ≤ p - 1 := by
  have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
  have h := Polynomial.natDegree_comp_le (p := centralLogPolynomial p) (q := 1 - X ^ 2)
  have hexp : ((p - 1) / 2) * 2 = p - 1 := by have := prime_half_identity p hp; omega
  exact h.trans ((Nat.mul_le_mul (centralLogPolynomial_degree p) hq).trans (by omega))

theorem finite_derivative_zero_one (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hd : P.natDegree < p) (he : P.eval 1 = 0) (hs : P.derivative = 0) : P = 0 := by
  have h := finite_derivative_zero p (P.comp (X + 1))
    (by
      have hq : (X + 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
      exact Polynomial.natDegree_comp_le.trans_lt
        ((Nat.mul_le_mul_left _ hq).trans_lt (by simpa using hd)))
    (by simpa only [eval_comp, eval_add, eval_X, eval_one, zero_add] using he)
    (by simp only [derivative_comp, hs, zero_comp, mul_zero])
  have ht := congrArg (fun Q : (ZMod p)[X] => Q.comp (X - 1)) h
  simpa only [Polynomial.comp_assoc, add_comp, X_comp, one_comp, sub_add_cancel,
    comp_X, zero_comp] using ht

/-- The literal complete even log has the actual central-binomial pullback. -/
theorem actual_evenLog_central (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    evenLogPolynomial p + C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) =
      (centralLogPolynomial p).comp (1 - X ^ 2) := by
  let D := evenLogPolynomial p + C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
    (centralLogPolynomial p).comp (1 - X ^ 2)
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    have h := congrArg (fun P : (ZMod p)[X] => P.coeff 2) hz
    norm_num [coeff_one] at h
  have hs : D.derivative = 0 := by
    have hh : (1 - X ^ 2) * D.derivative = 0 := by
      dsimp only [D]
      rw [derivative_sub, derivative_add, derivative_C]
      linear_combination evenLogPolynomial_source p hp - centralLogPolynomial_pullback_source p hp
    exact (mul_eq_zero.mp hh).resolve_left hq
  have hd : D.natDegree ≤ p - 1 := by
    have hc : (C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)).natDegree ≤ p - 1 := by simp
    have hadd : (evenLogPolynomial p + C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)).natDegree ≤ p - 1 :=
      by simpa only [Nat.max_self] using natDegree_add_le_of_le (evenLogPolynomial_degree p) hc
    simpa only [D, Nat.max_self] using natDegree_sub_le_of_le hadd
      (centralLogPolynomial_pullback_degree p (by omega : 7 ≤ p))
  have he : D.eval 1 = 0 := by
    simp only [D, eval_sub, eval_add, eval_C, evenLogPolynomial_endpoint_one p hp,
      eval_comp, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self, centralLogPolynomial_origin]
    ring
  exact sub_eq_zero.mp (finite_derivative_zero_one p D (by omega) he hs)

end WPActualEvenLogCarry
