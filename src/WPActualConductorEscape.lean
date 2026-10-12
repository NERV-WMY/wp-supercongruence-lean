import WPFiniteConductorCoefficient
import WPFiniteConductorIntegrality
import Mathlib.Algebra.Polynomial.Taylor

open scoped BigOperators
open Polynomial

namespace WPForcedSourceStokes

open WPFiniteConductorPolynomial

/-- A zero-inclusive valuation bound; zero is retained at every precision. -/
def precisionZero (p k : ℕ) (a : ℚ) : Prop := a = 0 ∨ (k : ℤ) ≤ padicValRat p a

theorem precisionZero_add (p k : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : precisionZero p k a) (hb : precisionZero p k b) :
    precisionZero p k (a + b) := by
  rcases ha with rfl | ha
  · simpa [precisionZero] using hb
  rcases hb with rfl | hb
  · exact Or.inr (by simpa using ha)
  by_cases hab : a + b = 0
  · exact Or.inl hab
  exact Or.inr ((le_min ha hb).trans (padicValRat.min_le_padicValRat_add hab))

theorem precisionZero_mul_integral (p k : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : precisionZero p k a) (hb : 0 ≤ padicValRat p b) :
    precisionZero p k (a * b) := by
  rcases ha with rfl | ha
  · exact Or.inl (by simp)
  by_cases ha0 : a = 0
  · exact Or.inl (by simp [ha0])
  by_cases hb0 : b = 0
  · exact Or.inl (by simp [hb0])
  apply Or.inr
  rw [padicValRat.mul ha0 hb0]
  omega

theorem precisionZero_sum {ι : Type*} (p k : ℕ) [Fact p.Prime]
    (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, precisionZero p k (f i)) :
    precisionZero p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact precisionZero_add p k _ _ (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem native_top_three_valuation (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (hhigh : p - 3 ≤ n) :
    padicValRat p (WPReview.nativeCoefficient n) = 3 := by
  apply WPNativeMomentIntegrality.native_high_tail_valuation p n (by omega) hn
  have hd : 3 ≤ p / 6 := by omega
  omega

def escapePoint : ℚ := 50 / 99
def escapeRoot : ℚ := 8 / 1331
noncomputable def escapeBase : ℚ[X] := X ^ 5 * collision

theorem original_escape_kernel_jets :
    lam.eval escapePoint = escapeRoot ∧
    (derivative lam).eval escapePoint = 297 / 50 * escapeRoot ∧
    escape.eval escapePoint = 0 ∧
    (derivative escapeBase).eval escapePoint = 473 / 50 * escapeBase.eval escapePoint ∧
    (scaledKernel 0).eval escapePoint = 0 ∧
    (derivative (scaledKernel 0)).eval escapePoint =
      2541 * escapeBase.eval escapePoint * escapeRoot ∧
    (scaledKernel 1).eval escapePoint =
      25725 / 11 * escapeBase.eval escapePoint * escapeRoot ^ 2 ∧
    (derivative (scaledKernel 1)).eval escapePoint =
      42756 * escapeBase.eval escapePoint * escapeRoot ^ 2 := by
  norm_num [escapePoint, escapeRoot, escapeBase, scaledKernel, kernelInput,
    G0, G1, G2, K, LP20, RP20, m, lam, ell, collision, escape,
    derivative_mul, derivative_pow_succ]

/-- The actual double-pole coefficient, retaining the full original numerator. -/
noncomputable def conductorEscapeDouble (p : ℕ) : ℚ :=
  (originalNumerator p (p - 2)).eval escapePoint / escapeBase.eval escapePoint

/-- The actual simple-pole coefficient in e=99x-50, computed before reduction. -/
noncomputable def conductorEscapeSimple (p : ℕ) : ℚ :=
  ((derivative (originalNumerator p (p - 2))).eval escapePoint *
      escapeBase.eval escapePoint -
    (originalNumerator p (p - 2)).eval escapePoint *
      (derivative escapeBase).eval escapePoint) /
    (99 * (escapeBase.eval escapePoint) ^ 2)

theorem escape_base_nonzero : escapeBase.eval escapePoint ≠ 0 := by
  norm_num [escapeBase, escapePoint, collision]

theorem full_numerator_escape_value (p : ℕ) (hp : 4 ≤ p) :
    (originalNumerator p (p - 2)).eval escapePoint =
      2 * WPReview.nativeCoefficient (p - 3) * escapeRoot ^ (p - 2) *
        (25725 / 11 * escapeBase.eval escapePoint * escapeRoot ^ 2) := by
  rw [original_full_numerator_split p hp]
  simp only [eval_add, eval_mul, eval_C, eval_pow]
  rw [original_escape_kernel_jets.1, original_escape_kernel_jets.2.2.2.2.1,
    original_escape_kernel_jets.2.2.2.2.2.2.1]
  simp [sourceDivisor, original_escape_kernel_jets.2.2.1]

theorem actual_conductor_escape_double (p : ℕ) (hp : 4 ≤ p) :
    conductorEscapeDouble p =
      51450 / 11 * escapeRoot ^ p * WPReview.nativeCoefficient (p - 3) := by
  rw [conductorEscapeDouble, full_numerator_escape_value p hp]
  rw [show escapeRoot ^ p = escapeRoot ^ (p - 2) * escapeRoot ^ 2 by
    rw [← pow_add, show p - 2 + 2 = p by omega]]
  field_simp [escape_base_nonzero]
  ring

theorem full_numerator_escape_derivative (p : ℕ) (hp : 4 ≤ p) :
    (derivative (originalNumerator p (p - 2))).eval escapePoint =
      2 * WPReview.nativeCoefficient (p - 3) *
        ((((p - 2 : ℕ) : ℚ) * escapeRoot ^ (p - 3) * (297 / 50 * escapeRoot)) *
            (25725 / 11 * escapeBase.eval escapePoint * escapeRoot ^ 2) +
          escapeRoot ^ (p - 2) * (42756 * escapeBase.eval escapePoint * escapeRoot ^ 2)) +
      2 * WPReview.nativeCoefficient (p - 2) * escapeRoot ^ (p - 1) *
        (2541 * escapeBase.eval escapePoint * escapeRoot) := by
  rw [original_full_numerator_split p hp]
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_add, eval_mul, eval_C, eval_pow]
  have hD : sourceDivisor.eval escapePoint = 0 := by
    simp [sourceDivisor, original_escape_kernel_jets.2.2.1]
  have hDd : (derivative sourceDivisor).eval escapePoint = 0 := by
    norm_num [sourceDivisor, derivative_mul, derivative_pow_succ, escape,
      collision, escapePoint]
  rw [hD, hDd]
  simp only [zero_mul, add_zero, zero_add]
  rw [derivative_pow, derivative_pow]
  simp only [eval_mul, eval_pow, eval_C]
  rw [show p - 2 - 1 = p - 3 by omega, show p - 1 - 1 = p - 2 by omega]
  rcases original_escape_kernel_jets with ⟨hl, hld, _, _, hk0, hk0d, hk1, hk1d⟩
  rw [hl, hld, hk0, hk0d, hk1, hk1d]
  ring

theorem actual_conductor_escape_simple (p : ℕ) (hp : 4 ≤ p) :
    conductorEscapeSimple p = 7 / 33 * escapeRoot ^ p *
      (242 * WPReview.nativeCoefficient (p - 2) +
        (1323 * (p : ℚ) - 681) * WPReview.nativeCoefficient (p - 3)) := by
  rw [conductorEscapeSimple, full_numerator_escape_derivative p hp,
    full_numerator_escape_value p hp, original_escape_kernel_jets.2.2.2.1]
  have hpow2 : escapeRoot ^ p = escapeRoot ^ (p - 2) * escapeRoot ^ 2 := by
    rw [← pow_add, show p - 2 + 2 = p by omega]
  have hpow1 : escapeRoot ^ (p - 1) = escapeRoot ^ (p - 2) * escapeRoot := by
    rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
  have hpow3 : escapeRoot ^ (p - 3) * escapeRoot = escapeRoot ^ (p - 2) := by
    rw [← pow_succ, show p - 3 + 1 = p - 2 by omega]
  rw [hpow1, hpow2]
  rw [show ((p - 2 : ℕ) : ℚ) = (p : ℚ) - 2 by rw [Nat.cast_sub (by omega)]; norm_num]
  have hr : ((p : ℚ) - 2) * escapeRoot ^ (p - 3) * (297 / 50 * escapeRoot) =
      ((p : ℚ) - 2) * (297 / 50) * escapeRoot ^ (p - 2) := by
    calc
      _ = ((p : ℚ) - 2) * (297 / 50) *
          (escapeRoot ^ (p - 3) * escapeRoot) := by ring
      _ = _ := by rw [hpow3]
  rw [hr]
  field_simp [escape_base_nonzero]
  ring

/-- The literal regular factor multiplying e^-2, expanded in x-50/99. -/
noncomputable def actualEscapeRegularSeries (p : ℕ) : PowerSeries ℚ :=
  (taylor escapePoint (originalNumerator p (p - 2)) : PowerSeries ℚ) *
    (taylor escapePoint escapeBase : PowerSeries ℚ)⁻¹

theorem actual_escape_series_double (p : ℕ) :
    PowerSeries.coeff 0 (actualEscapeRegularSeries p) = conductorEscapeDouble p := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, actualEscapeRegularSeries, map_mul,
    PowerSeries.constantCoeff_inv]
  simp [conductorEscapeDouble, div_eq_mul_inv]

theorem actual_escape_series_simple (p : ℕ) :
    PowerSeries.coeff 1 (actualEscapeRegularSeries p) / 99 = conductorEscapeSimple p := by
  rw [actualEscapeRegularSeries, PowerSeries.coeff_one_mul]
  have hi (Q : PowerSeries ℚ) : PowerSeries.coeff 1 Q⁻¹ =
      -(PowerSeries.constantCoeff Q)⁻¹ * PowerSeries.coeff 1 Q *
        (PowerSeries.constantCoeff Q)⁻¹ := by
    rw [PowerSeries.coeff_inv, show Finset.antidiagonal 1 = {(0, 1), (1, 0)} by rfl]
    norm_num [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv]
    ring
  rw [hi, PowerSeries.constantCoeff_inv]
  simp [conductorEscapeSimple]
  field_simp [escape_base_nonzero]
  ring

theorem actual_conductor_escape_double_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : precisionZero p 3 (conductorEscapeDouble p) := by
  let R := integralSubring p
  have h11 : (1 / 11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  have hq : escapeRoot ∈ R := by
    rw [escapeRoot, show (8 / 1331 : ℚ) = 8 * (1 / 11) ^ 3 by norm_num]
    exact R.mul_mem (natCast_mem R 8) (R.pow_mem h11 3)
  have hs : (51450 / 11 : ℚ) * escapeRoot ^ p ∈ R := by
    have h1 : (51450 / 11 : ℚ) ∈ R := by
      rw [show (51450 / 11 : ℚ) = 51450 * (1 / 11) by norm_num]
      exact R.mul_mem (natCast_mem R 51450) h11
    exact R.mul_mem h1 (R.pow_mem hq p)
  rw [actual_conductor_escape_double p (by omega), mul_comm]
  apply precisionZero_mul_integral p 3 _ _
  · apply Or.inr
    rw [native_top_three_valuation p (p - 3) hp (by omega) le_rfl]
    norm_num
  · exact hs

theorem actual_conductor_escape_simple_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : precisionZero p 3 (conductorEscapeSimple p) := by
  let R := integralSubring p
  have h3 : (1 / 3 : ℚ) ∈ R := small_inverse_integral p 3 (by norm_num) (by omega)
  have h11 : (1 / 11 : ℚ) ∈ R := small_inverse_integral p 11 (by norm_num) (by omega)
  have hq : escapeRoot ∈ R := by
    rw [escapeRoot, show (8 / 1331 : ℚ) = 8 * (1 / 11) ^ 3 by norm_num]
    exact R.mul_mem (natCast_mem R 8) (R.pow_mem h11 3)
  have hs : (7 / 33 : ℚ) * escapeRoot ^ p ∈ R := by
    have h1 : (7 / 33 : ℚ) ∈ R := by
      rw [show (7 / 33 : ℚ) = 7 * (1 / 3) * (1 / 11) by norm_num]
      exact R.mul_mem (R.mul_mem (natCast_mem R 7) h3) h11
    exact R.mul_mem h1 (R.pow_mem hq p)
  have hc2 : precisionZero p 3 (WPReview.nativeCoefficient (p - 2)) := by
    apply Or.inr
    rw [native_top_three_valuation p (p - 2) hp (by omega) (by omega)]
    norm_num
  have hc3 : precisionZero p 3 (WPReview.nativeCoefficient (p - 3)) := by
    apply Or.inr
    rw [native_top_three_valuation p (p - 3) hp (by omega) le_rfl]
    norm_num
  have ht1 : precisionZero p 3 (242 * WPReview.nativeCoefficient (p - 2)) := by
    rw [mul_comm]
    exact precisionZero_mul_integral p 3 _ _ hc2 (natCast_mem R 242)
  have ht2 : precisionZero p 3 ((1323 * (p : ℚ) - 681) * WPReview.nativeCoefficient (p - 3)) := by
    rw [mul_comm]
    exact precisionZero_mul_integral p 3 _ _ hc3
      (R.sub_mem (R.mul_mem (natCast_mem R 1323) (natCast_mem R p)) (natCast_mem R 681))
  rw [actual_conductor_escape_simple p (by omega), mul_comm]
  exact precisionZero_mul_integral p 3 _ _ (precisionZero_add p 3 _ _ ht1 ht2) hs

theorem literal_lambda_integral (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    lam ∈ coefficientSubring (integralSubring p) := by
  let R := integralSubring p
  let P := coefficientSubring R
  have h5 : (1 / 5 : ℚ) ∈ R := small_inverse_integral p 5 (by norm_num) (by omega)
  have hc : (729 / 15625 : ℚ) ∈ R := by
    rw [show (729 / 15625 : ℚ) = 729 * (1 / 5) ^ 6 by norm_num]
    exact R.mul_mem (natCast_mem R 729) (R.pow_mem h5 6)
  exact P.mul_mem (C_mem_coefficientSubring R _ hc)
    (P.pow_mem (X_mem_coefficientSubring R) 3)

/-- Every polynomial coefficient of the canceled full-to-short tail has three digits. -/
theorem canceled_full_short_conductor_precision (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (k : ℕ) :
    precisionZero p 3 ((Be p (p - 4) - Be p (p - 1 - p / 6)).coeff k) := by
  classical
  let R := integralSubring p
  let P := coefficientSubring R
  let f (n : ℕ) : ℚ[X] := C (2 * WPReview.nativeCoefficient n) *
    lam ^ (n + 1) * canceledKernel (p - 4 - n)
  have hcut : p - 1 - p / 6 + 1 ≤ p - 4 + 1 := by
    have hd : 3 ≤ p / 6 := by omega
    omega
  have htail : Be p (p - 4) - Be p (p - 1 - p / 6) =
      ∑ n ∈ Finset.Ico (p - 1 - p / 6 + 1) (p - 4 + 1), f n := by
    have h := Finset.sum_range_add_sum_Ico f hcut
    change (∑ n ∈ Finset.range (p - 4 + 1), f n) -
      (∑ n ∈ Finset.range (p - 1 - p / 6 + 1), f n) = _
    rw [← h]
    ring
  rw [htail, finsetSum_coeff]
  apply precisionZero_sum
  intro n hn
  have hn1 := (Finset.mem_Ico.mp hn).1
  have hn2 := (Finset.mem_Ico.mp hn).2
  have hc : precisionZero p 3 (WPReview.nativeCoefficient n) := by
    apply Or.inr
    rw [WPNativeMomentIntegrality.native_high_tail_valuation p n (by omega)
      (by omega) (by omega)]
    norm_num
  have hc2 : precisionZero p 3 (2 * WPReview.nativeCoefficient n) := by
    rw [mul_comm]
    exact precisionZero_mul_integral p 3 _ _ hc (natCast_mem R 2)
  have hk : lam ^ (n + 1) * canceledKernel (p - 4 - n) ∈ P :=
    P.mul_mem (P.pow_mem (literal_lambda_integral p (by omega)) (n + 1))
      (canceledKernel_integral p _ (by omega))
  dsimp [f]
  rw [mul_assoc, coeff_C_mul]
  exact precisionZero_mul_integral p 3 _ _ hc2
    ((mem_coefficientSubring R _).mp hk k)

theorem native_coefficient_at_prime_valuation (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) : padicValRat p (WPReview.nativeCoefficient p) = 0 := by
  have hprime : p.Prime := Fact.out
  have h6 : 6 * p < p ^ 2 := by nlinarith
  have h3 : 3 * p < p ^ 2 := by nlinarith
  have h1 : p < p ^ 2 := by nlinarith
  have hp0 : (p.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3p0 : ((3 * p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h6p0 : ((6 * p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1728 : (1728 : ℚ) ^ p ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold WPReview.nativeCoefficient
  rw [padicValRat.div h6p0 (mul_ne_zero (mul_ne_zero h3p0 (pow_ne_zero _ hp0)) h1728),
    padicValRat.mul (mul_ne_zero h3p0 (pow_ne_zero _ hp0)) h1728,
    padicValRat.mul h3p0 (pow_ne_zero _ hp0), padicValRat.pow, padicValRat.pow,
    WPNativeMomentIntegrality.native_normalizer_unit p hp, padicValRat.of_nat,
    padicValRat.of_nat, padicValRat.of_nat,
    WPGammaArithmetic.factorial_valuation_below_square p (6 * p) hprime h6,
    WPGammaArithmetic.factorial_valuation_below_square p (3 * p) hprime h3,
    WPGammaArithmetic.factorial_valuation_below_square p p hprime h1]
  simp [hprime.ne_zero]

theorem actual_native_endpoint_valuation (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) : padicValRat p (WPReview.nativeEndpoint p) = 3 := by
  have hprime : p.Prime := Fact.out
  rw [WPReview.nativeEndpoint_eq p (by omega),
    padicValRat.mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr hprime.ne_zero))
      (WPNativeMomentIntegrality.nativeCoefficient_ne_zero p), padicValRat.pow,
    padicValRat.self hprime.one_lt, native_coefficient_at_prime_valuation p hp]
  norm_num

theorem actual_native_square_endpoint_valuation (p : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) : padicValRat p (WPReview.nativeEndpoint p ^ 2) = 6 := by
  rw [padicValRat.pow, actual_native_endpoint_valuation p hp]
  norm_num

theorem native_top_three_square_valuation (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (hhigh : p - 3 ≤ n) :
    padicValRat p (WPReview.nativeCoefficient n ^ 2) = 6 := by
  rw [padicValRat.pow, native_top_three_valuation p n hp hn hhigh]
  norm_num

end WPForcedSourceStokes
