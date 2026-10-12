import WPActualMomentDefect
import Mathlib.FieldTheory.RatFunc.Basic

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentIntegral WPActualPullbackSource WPActualMomentDefect

namespace WPActualLogarithmicEta

noncomputable def rationalVariable : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) Polynomial.X

theorem rationalVariable_ne_zero : rationalVariable ≠ 0 :=
  RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

/-- The faithful Laurent inclusion into actual rational functions of y. -/
noncomputable def ratify : ℚ[T;T⁻¹] →+* RatFunc ℚ :=
  LaurentPolynomial.eval₂ (algebraMap ℚ (RatFunc ℚ))
    (Units.mk0 rationalVariable rationalVariable_ne_zero)

theorem ratify_C (a : ℚ) : ratify (C a) = algebraMap ℚ (RatFunc ℚ) a := by
  simp [ratify, LaurentPolynomial.eval₂_C]

theorem ratify_toLaurent (P : ℚ[X]) :
    ratify (Polynomial.toLaurent P) = algebraMap ℚ[X] (RatFunc ℚ) P := by
  rw [ratify, LaurentPolynomial.eval₂_toLaurent]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    change algebraMap ℚ (RatFunc ℚ) a * rationalVariable ^ n =
      algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C a) * rationalVariable ^ n
    congr 1
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) a

theorem ratify_injective : Function.Injective ratify := by
  intro P Q hPQ
  obtain ⟨k, F, hF⟩ := LaurentPolynomial.exists_T_pow (P - Q)
  have hzero : ratify (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
  have hFzero : F = 0 := by
    apply RatFunc.algebraMap_injective ℚ
    rw [map_zero, ← ratify_toLaurent, hF, map_mul, hzero, zero_mul]
  rw [hFzero, map_zero] at hF
  have hmul := congrArg (fun L : ℚ[T;T⁻¹] => L * T (-(k : ℤ))) hF
  simp only [zero_mul, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one] at hmul
  exact sub_eq_zero.mp hmul.symm

theorem actual_Vpull_ne_zero : Vpull ≠ 0 := by
  intro h
  have hv := congrArg (evaluate 3 (by norm_num)) h
  rw [evaluate_Vpull, map_zero] at hv
  norm_num at hv

theorem actual_Spull_ne_zero : Spull ≠ 0 := by
  intro h
  have hs := congrArg (evaluate 3 (by norm_num)) h
  rw [evaluate_Spull, evaluate_Vpull, map_zero] at hs
  norm_num at hs

/-- Literal logarithmic differential coefficient, with its original finite poles. -/
noncomputable def dlog (L : ℚ[T;T⁻¹]) : RatFunc ℚ := ratify (derivative L) / ratify L

/-- The actual eta=chi*dlogV+He(V)*dlogS, retaining the full Fe and He. -/
noncomputable def eta (p N e : ℕ) : RatFunc ℚ :=
  ratify (chi p N e) * dlog Vpull + ratify (Hpull e Vpull) * dlog Spull

theorem baseDensity_actual_dlog (p : ℕ) (hp : 1 ≤ p) :
    ratify Spull ^ p * dlog Vpull = ratify (baseDensity p) := by
  have hV : ratify Vpull ≠ 0 := by simpa using ratify_injective.ne actual_Vpull_ne_zero
  have hpow : (ratify Vpull) ^ p = (ratify Vpull) ^ (p - 1) * ratify Vpull := by
    rw [← pow_succ]
    congr 1
    omega
  rw [dlog, ← map_pow, Spull_power, map_mul, map_pow, hpow]
  unfold baseDensity
  simp only [map_mul, map_pow]
  field_simp [hV]

theorem logarithmicSDensity_actual_dlog (p : ℕ) (hp : 1 ≤ p) :
    ratify Spull ^ p * dlog Spull = ratify (logarithmicSDensity p) := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hC : (C (p : ℚ) : ℚ[T;T⁻¹]) ≠ 0 := by
    intro h
    have hh := congrArg (evaluate 3 (by norm_num)) h
    rw [evaluate_C, map_zero] at hh
    exact hpq hh
  have hi : p - 1 + 1 = p := by omega
  have hc : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by exact_mod_cast hi
  have hlog : logarithmicSDensity p = Spull ^ (p - 1) * derivative Spull := by
    apply mul_left_cancel₀ hC
    rw [← derivative_Spull_power p hp]
    simpa only [hi, hc, mul_assoc] using derivative_pow_succ Spull (p - 1)
  have hS : ratify Spull ≠ 0 := by simpa using ratify_injective.ne actual_Spull_ne_zero
  have hpow : ratify Spull ^ p = ratify Spull ^ (p - 1) * ratify Spull := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hlog, map_mul, map_pow, dlog, hpow]
  field_simp [hS]

/-- The explicit weighted Laurent source is exactly S^p times the literal rational eta. -/
theorem actual_eta_weighted_source (p N e : ℕ) (hp : 1 ≤ p) :
    ratify Spull ^ p * eta p N e = ratify (weightedEta p N e) := by
  unfold eta
  calc
    _ = ratify (chi p N e) * (ratify Spull ^ p * dlog Vpull) +
        ratify (Hpull e Vpull) * (ratify Spull ^ p * dlog Spull) := by ring
    _ = _ := by
      rw [baseDensity_actual_dlog p hp, logarithmicSDensity_actual_dlog p hp]
      simp only [weightedEta, map_add, map_mul]

theorem actual_native_cutoff_NC60 (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualShortMoment p (p - 1 - p / 6) = baseMoment p -
      (p : ℚ) / 9 * etaPeriod p ((p - 1) / 2) (p - 1 - p / 6) := by
  apply actual_short_moment_period_decomposition p ((p - 1) / 2) _ (by omega)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hodd with ⟨k, hk⟩
  omega

theorem actual_full_native_moment_NC60_precision (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
      WPNativeMomentIntegrality.actualMonomialMoment p n) =
      baseMoment p - (p : ℚ) / 9 * etaPeriod p ((p - 1) / 2) (p - 1 - p / 6) ∨
    (3 : ℤ) ≤ padicValRat p
      ((∑ n ∈ Finset.range p, WPReview.nativeCoefficient n *
        WPNativeMomentIntegrality.actualMonomialMoment p n) -
        (baseMoment p - (p : ℚ) / 9 * etaPeriod p ((p - 1) / 2) (p - 1 - p / 6))) := by
  have h := WPNativeMomentIntegrality.actual_full_literal_cutoff_moment_precision p (by omega)
  change _ = actualShortMoment p (p - 1 - p / 6) ∨
    (3 : ℤ) ≤ padicValRat p (_ - actualShortMoment p (p - 1 - p / 6)) at h
  rw [actual_native_cutoff_NC60 p hp] at h
  exact h

end WPActualLogarithmicEta
