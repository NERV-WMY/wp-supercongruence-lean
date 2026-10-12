import WPUniversalRankTwo
import WPPIntegralReduction
import WPNativeCutoff

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction

namespace WPActualNativeHasse

theorem actual_native_coefficient_integral (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : 0 ≤ padicValRat p (WPReview.nativeCoefficient n) := by
  rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp hn]
  have hdiv : 3 * n / p ≤ 6 * n / p := Nat.div_le_div_right (by omega)
  exact sub_nonneg.mpr (by exact_mod_cast hdiv)

/-- Every literal coefficient above d vanishes in the field, including the full high tail. -/
theorem actual_native_coefficient_field_tail (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) (hd : p / 6 < n) :
    (WPReview.nativeCoefficient n : ZMod p) = 0 := by
  have hp0 : 0 < p := by omega
  have h6 : 1 ≤ 6 * n / p := by
    apply (Nat.le_div_iff_mul_le hp0).mpr
    omega
  have hdouble : 2 * (3 * n / p) ≤ 6 * n / p := by
    apply (Nat.le_div_iff_mul_le hp0).mpr
    have hmul := Nat.div_mul_le_self (3 * n) p
    nlinarith
  have hv : 1 ≤ padicValRat p (WPReview.nativeCoefficient n) := by
    rw [WPNativeMomentIntegrality.native_coefficient_valuation_below_prime p n hp hn]
    omega
  apply (integral_residue_zero_iff p _ (actual_native_coefficient_integral p n hp hn)).mpr
  exact Or.inr (by simpa using hv)

/-- The original rational native recurrence, with every denominator cleared. -/
theorem actual_native_cleared_recurrence (n : ℕ) :
    72 * ((n : ℚ) + 1) ^ 3 * WPReview.nativeCoefficient (n + 1) =
      (2 * (n : ℚ) + 1) * (6 * (n : ℚ) + 1) * (6 * (n : ℚ) + 5) *
        WPReview.nativeCoefficient n := by
  linear_combination 72 * WPReview.nativeCoefficient_recurrence n

theorem actual_native_field_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    72 * ((n : ZMod p) + 1) ^ 3 * (WPReview.nativeCoefficient (n + 1) : ZMod p) =
      (2 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5) *
        (WPReview.nativeCoefficient n : ZMod p) := by
  let R := integralRationals p
  let a : R := ⟨WPReview.nativeCoefficient (n + 1),
    actual_native_coefficient_integral p (n + 1) hp hn⟩
  let b : R := ⟨WPReview.nativeCoefficient n,
    actual_native_coefficient_integral p n hp (by omega)⟩
  have hr : 72 * ((n : R) + 1) ^ 3 * a =
      (2 * (n : R) + 1) * (6 * (n : R) + 1) * (6 * (n : R) + 5) * b := by
    apply Subtype.ext
    exact actual_native_cleared_recurrence n
  have hf := congrArg (residueHom p) hr
  simp only [map_mul, map_pow, map_add, map_natCast, map_ofNat, map_one] at hf
  exact hf

/-- The actual Fe reduced coefficientwise, rather than an unrelated Hasse polynomial. -/
noncomputable def nativeField (p e : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  ∑ n ∈ Finset.range (e + 1), monomial n (WPReview.nativeCoefficient n : ZMod p)

theorem nativeField_coeff (p e n : ℕ) [Fact p.Prime] :
    (nativeField p e).coeff n = if n < e + 1 then (WPReview.nativeCoefficient n : ZMod p) else 0 := by
  classical
  simp only [nativeField, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < e + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b _hb hbn; simp [hbn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by have := Finset.mem_range.mp hb; omega
    simp [hbn]

theorem actual_full_native_field_cutoff (p e : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (he : e < p) (hd : p / 6 ≤ e) :
    nativeField p e = nativeField p (p / 6) := by
  ext n
  rw [nativeField_coeff, nativeField_coeff]
  by_cases hnd : n < p / 6 + 1
  · have hne : n < e + 1 := by omega
    rw [if_pos hnd, if_pos hne]
  · rw [if_neg hnd]
    by_cases hne : n < e + 1
    · rw [if_pos hne]
      exact actual_native_coefficient_field_tail p n hp (by omega) (by omega)
    · rw [if_neg hne]

theorem actual_native_field_degree (p : ℕ) [Fact p.Prime] :
    (nativeField p (p / 6)).natDegree ≤ p / 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeField_coeff, if_neg (by omega)]

theorem actual_native_field_origin (p e : ℕ) [Fact p.Prime] :
    (nativeField p e).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, nativeField_coeff]
  simp [WPReview.nativeCoefficient_zero]

noncomputable def theta {K : Type*} [CommRing K] (P : K[X]) : K[X] := X * derivative P
noncomputable def integerShift {K : Type*} [CommRing K] (a b : K) (P : K[X]) : K[X] :=
  C a * theta P + C b * P

/-- The actual native third-order operator multiplied by 72. -/
noncomputable def clearedOperator {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  72 * theta (theta (theta P)) - X * integerShift 2 1
    (integerShift 6 1 (integerShift 6 5 P))

theorem theta_coeff {K : Type*} [CommRing K] (P : K[X]) (n : ℕ) :
    (theta P).coeff n = (n : K) * P.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n => simp [theta, coeff_X_mul, coeff_derivative]; ring

theorem integerShift_coeff {K : Type*} [CommRing K] (a b : K) (P : K[X]) (n : ℕ) :
    (integerShift a b P).coeff n = (a * n + b) * P.coeff n := by
  simp only [integerShift, coeff_add, coeff_C_mul, theta_coeff]
  ring

theorem clearedOperator_coeff_zero {K : Type*} [CommRing K] (P : K[X]) :
    (clearedOperator P).coeff 0 = 0 := by
  simp [clearedOperator, theta_coeff]

theorem clearedOperator_coeff_succ {K : Type*} [CommRing K] (P : K[X]) (n : ℕ) :
    (clearedOperator P).coeff (n + 1) =
      72 * ((n : K) + 1) ^ 3 * P.coeff (n + 1) -
      (2 * (n : K) + 1) * (6 * (n : K) + 1) * (6 * (n : K) + 5) * P.coeff n := by
  simp only [clearedOperator, coeff_sub, coeff_ofNat_mul, theta_coeff,
    coeff_X_mul, integerShift_coeff, Nat.cast_add, Nat.cast_one]
  ring

/-- The complete actual field native polynomial solves its finite third-order ODE. -/
theorem actual_native_field_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    clearedOperator (nativeField p (p / 6)) = 0 := by
  have hd1 : p / 6 + 1 < p := by omega
  ext k
  cases k with
  | zero => rw [clearedOperator_coeff_zero, coeff_zero]
  | succ n =>
    rw [clearedOperator_coeff_succ, coeff_zero, nativeField_coeff, nativeField_coeff]
    by_cases hn : n + 1 < p / 6 + 1
    · rw [if_pos hn, if_pos (by omega)]
      exact sub_eq_zero.mpr (actual_native_field_recurrence p n hp (by omega))
    · rw [if_neg hn]
      by_cases hnd : n < p / 6 + 1
      · have hneq : n = p / 6 := by omega
        rw [if_pos hnd]
        have hr := actual_native_field_recurrence p n hp (by omega)
        rw [actual_native_coefficient_field_tail p (n + 1) hp (by omega) (by omega)] at hr
        simpa only [mul_zero, zero_sub] using sub_eq_zero.mpr hr
      · rw [if_neg hnd]
        ring

theorem actual_native_cutoff_field_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    clearedOperator (nativeField p (p - 1 - p / 6)) = 0 := by
  rw [actual_full_native_field_cutoff p _ (by omega) (by omega) (by omega)]
  exact actual_native_field_ODE p (by omega)

end WPActualNativeHasse
