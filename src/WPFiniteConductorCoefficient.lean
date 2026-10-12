import WPFiniteConductorPolynomial
import Mathlib.RingTheory.PowerSeries.Inverse

open scoped BigOperators
open Polynomial

namespace WPFiniteConductorPolynomial

/-- The original quadratic f(s,x), interpreted only for coefficient extraction in s. -/
noncomputable def fSeries (x : ℚ) : PowerSeries ℚ :=
  PowerSeries.X ^ 2 - PowerSeries.C (2 * m.eval x) * PowerSeries.X +
    PowerSeries.C (lam.eval x)

/-- The literal polynomial x*g(s,x), before multiplication by (1-s). -/
noncomputable def GSeries (x : ℚ) : PowerSeries ℚ :=
  PowerSeries.C (G0.eval x) + PowerSeries.C (G1.eval x) * PowerSeries.X +
    PowerSeries.C (G2.eval x) * PowerSeries.X ^ 2

/-- The original unexpanded x*g formula from the two retained source witnesses. -/
noncomputable def originalSourceGSeries (x : ℚ) : PowerSeries ℚ :=
  12 * PowerSeries.C (1 - x) * PowerSeries.X *
      (PowerSeries.C (LP20.eval x) * (PowerSeries.X - PowerSeries.C (m.eval x)) +
        PowerSeries.C (ell.eval x) * PowerSeries.C (collision.eval x) * PowerSeries.C (RP20.eval x)) -
    PowerSeries.C x * PowerSeries.C (1 - x) * PowerSeries.C (LP20.eval x) *
      (4 * PowerSeries.C ((Polynomial.derivative m).eval x) * PowerSeries.X -
        2 * PowerSeries.C ((Polynomial.derivative lam).eval x)) +
    2 * PowerSeries.C x * PowerSeries.C (RP20.eval x) *
      (-2 * PowerSeries.C (1 - x) * PowerSeries.C (ell.eval x) *
          PowerSeries.C (collision.eval x) * PowerSeries.C ((Polynomial.derivative m).eval x) +
        (PowerSeries.X - PowerSeries.C (m.eval x)) * PowerSeries.C (K.eval x))

theorem original_source_witness_formula (x : ℚ) :
    GSeries x = originalSourceGSeries x := by
  norm_num [GSeries, originalSourceGSeries, G0, G1, G2,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, map_add, map_sub, map_mul, map_neg]
  simp only [map_ofNat]
  ring

noncomputable def kernelSeries (x : ℚ) : PowerSeries ℚ :=
  (1 - PowerSeries.X) * GSeries x

noncomputable def scaledKernelSeries (x : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (scaledKernel k).eval x / (lam.eval x) ^ (k + 1)

theorem kernelSeries_coefficient (x : ℚ) (k : ℕ) :
    PowerSeries.coeff k (kernelSeries x) = (kernelInput k).eval x := by
  rcases k with (_ | (_ | (_ | (_ | k))))
  all_goals norm_num [kernelSeries, GSeries, kernelInput,
    sub_mul, mul_add, mul_sub, mul_assoc, ← pow_succ,
    PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X]
  all_goals try split_ifs
  all_goals first | omega | ring

theorem scaledKernel_eval_step (x : ℚ) (k : ℕ) :
    (scaledKernel (k + 2)).eval x =
      2 * m.eval x * (scaledKernel (k + 1)).eval x -
        lam.eval x * (scaledKernel k).eval x +
        (lam.eval x) ^ (k + 2) * (kernelInput (k + 2)).eval x := by
  rw [scaledKernel]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat]

/-- The original reciprocal coefficient identity is proved by multiplying by f. -/
theorem original_kernel_series_identity (x : ℚ) (hl : lam.eval x ≠ 0) :
    fSeries x * scaledKernelSeries x = kernelSeries x := by
  apply PowerSeries.ext
  intro k
  rw [kernelSeries_coefficient]
  rcases k with (_ | (_ | k))
  · norm_num [fSeries, scaledKernelSeries, scaledKernel, kernelInput,
      sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul']
    field_simp [hl]
  · norm_num [fSeries, scaledKernelSeries, scaledKernel, kernelInput,
      sub_mul, add_mul, mul_assoc, PowerSeries.coeff_X_pow_mul']
    field_simp [hl]; ring
  · norm_num [fSeries, sub_mul, add_mul, mul_assoc,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
      scaledKernelSeries, Nat.add_sub_cancel]
    rw [scaledKernel_eval_step]
    simp only [pow_succ]
    field_simp [hl]
    rw [show k + 1 + 1 - 2 = k by omega]
    ring

theorem original_kernel_reciprocal (x : ℚ) (hl : lam.eval x ≠ 0) :
    kernelSeries x * (fSeries x)⁻¹ = scaledKernelSeries x := by
  have hf : PowerSeries.constantCoeff (fSeries x) ≠ 0 := by
    simpa [fSeries] using hl
  have h := original_kernel_series_identity x hl
  calc
    kernelSeries x * (fSeries x)⁻¹ =
      fSeries x * scaledKernelSeries x * (fSeries x)⁻¹ := by rw [h]
    _ = scaledKernelSeries x * (fSeries x * (fSeries x)⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ hf, mul_one]

/-- The original conductor definition, including g's original factor 1/x. -/
noncomputable def originalBe (p e : ℕ) (x : ℚ) : ℚ :=
  2 * (lam.eval x) ^ p / (x ^ 4 * collision.eval x * (escape.eval x) ^ 2) *
    PowerSeries.coeff (p - 2)
      ((WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) *
        PowerSeries.C (1 / x) * kernelSeries x * (fSeries x)⁻¹)

theorem originalBe_literal_witness_formula (p e : ℕ) (x : ℚ) :
    originalBe p e x =
      2 * (lam.eval x) ^ p / (x ^ 4 * collision.eval x * (escape.eval x) ^ 2) *
        PowerSeries.coeff (p - 2)
          ((WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) * PowerSeries.C (1 / x) *
            ((1 - PowerSeries.X) * originalSourceGSeries x) * (fSeries x)⁻¹) := by
  rw [originalBe, kernelSeries, original_source_witness_formula]

theorem native_series_times_kernel_coefficient_of_le (p e : ℕ) (x : ℚ)
    (he : e ≤ p - 2) :
    PowerSeries.coeff (p - 2)
      ((WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) * scaledKernelSeries x) =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n *
        ((scaledKernel (p - 2 - n)).eval x / (lam.eval x) ^ (p - 2 - n + 1)) := by
  classical
  unfold WPReview.nativePolynomial
  change PowerSeries.coeff (p - 2)
    (Polynomial.coeToPowerSeries.ringHom
      (∑ n ∈ Finset.range (e + 1), monomial n (WPReview.nativeCoefficient n)) *
        scaledKernelSeries x) = _
  simp only [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ p - 2 := by have := Finset.mem_range.mp hn; omega
  rw [Polynomial.coeToPowerSeries.ringHom_apply, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
    mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos hnle]
  rw [scaledKernelSeries, PowerSeries.coeff_mk]

theorem native_series_times_kernel_coefficient (p e : ℕ) (x : ℚ)
    (he : e + 4 ≤ p) :
    PowerSeries.coeff (p - 2)
      ((WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) * scaledKernelSeries x) =
      ∑ n ∈ Finset.range (e + 1), WPReview.nativeCoefficient n *
        ((scaledKernel (p - 2 - n)).eval x / (lam.eval x) ^ (p - 2 - n + 1)) := by
  apply native_series_times_kernel_coefficient_of_le
  omega

/-- The literal full native polynomial contributes only indices at most p-2. -/
theorem full_native_series_times_kernel_coefficient (p : ℕ) (hp : 2 ≤ p) (x : ℚ) :
    PowerSeries.coeff (p - 2)
      ((WPReview.nativePolynomial p : PowerSeries ℚ) * scaledKernelSeries x) =
      ∑ n ∈ Finset.range (p - 1), WPReview.nativeCoefficient n *
        ((scaledKernel (p - 2 - n)).eval x / (lam.eval x) ^ (p - 2 - n + 1)) := by
  classical
  have hpoly : WPReview.nativePolynomial p = WPReview.nativePolynomial (p - 1) +
      monomial (p - 1) (WPReview.nativeCoefficient (p - 1)) := by
    unfold WPReview.nativePolynomial
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
  rw [hpoly, Polynomial.coe_add, add_mul, map_add]
  have hlast : PowerSeries.coeff (p - 2)
      (((monomial (p - 1) (WPReview.nativeCoefficient (p - 1)) : ℚ[X]) : PowerSeries ℚ) *
        scaledKernelSeries x) = 0 := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
  rw [hlast, add_zero]
  simpa only [show p - 2 + 1 = p - 1 by omega] using
    native_series_times_kernel_coefficient_of_le p (p - 2) x le_rfl

/-- Before cusp/escape cancellation, the full literal source has its original divisor. -/
theorem original_full_Be_numerator (p : ℕ) (hp : 2 ≤ p) (x : ℚ)
    (hx : x ≠ 0) (hM : collision.eval x ≠ 0) (hE : escape.eval x ≠ 0) :
    originalBe p (p - 1) x = (originalNumerator p (p - 2)).eval x /
      sourceDivisor.eval x := by
  classical
  have hl : lam.eval x ≠ 0 := by
    simpa [lam] using mul_ne_zero (by norm_num : (729 / 15625 : ℚ) ≠ 0)
      (pow_ne_zero 3 hx)
  have hD : sourceDivisor.eval x ≠ 0 := by
    simpa [sourceDivisor] using mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hx) hM)
      (pow_ne_zero 2 hE)
  apply (eq_div_iff hD).mpr
  unfold originalBe
  rw [show p - 1 + 1 = p by omega]
  have hseries :
      (WPReview.nativePolynomial p : PowerSeries ℚ) *
          PowerSeries.C (1 / x) * kernelSeries x * (fSeries x)⁻¹ =
        PowerSeries.C (1 / x) *
          ((WPReview.nativePolynomial p : PowerSeries ℚ) * scaledKernelSeries x) := by
    rw [← original_kernel_reciprocal x hl]
    ring
  rw [hseries, PowerSeries.coeff_C_mul, full_native_series_times_kernel_coefficient p hp x]
  unfold originalNumerator
  rw [eval_finsetSum, show p - 2 + 1 = p - 1 by omega]
  simp only [eval_mul, eval_C, eval_pow]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ p - 2 := by have := Finset.mem_range.mp hn; omega
  have hpw : p = (p - 2 - n + 1) + (n + 1) := by omega
  have hlpow : (lam.eval x) ^ p =
      (lam.eval x) ^ (p - 2 - n + 1) * (lam.eval x) ^ (n + 1) := by
    conv_lhs => rw [hpw]
    exact pow_add _ _ _
  rw [hlpow]
  norm_num [sourceDivisor]
  field_simp [hx, hM, hE, hl]

/-- The two uncanceled literal escape terms are retained as A1 and A0. -/
theorem original_full_numerator_split (p : ℕ) (hp : 4 ≤ p) :
    originalNumerator p (p - 2) = sourceDivisor * Be p (p - 4) +
      C (2 * WPReview.nativeCoefficient (p - 3)) * lam ^ (p - 2) * scaledKernel 1 +
      C (2 * WPReview.nativeCoefficient (p - 2)) * lam ^ (p - 1) * scaledKernel 0 := by
  have hprefix : originalNumerator p (p - 2) = originalNumerator p (p - 4) +
      C (2 * WPReview.nativeCoefficient (p - 3)) * lam ^ (p - 2) * scaledKernel 1 +
      C (2 * WPReview.nativeCoefficient (p - 2)) * lam ^ (p - 1) * scaledKernel 0 := by
    let a (n : ℕ) : ℚ[X] :=
      C (2 * WPReview.nativeCoefficient n) * lam ^ (n + 1) * scaledKernel (p - 2 - n)
    change (∑ n ∈ Finset.range (p - 2 + 1), a n) =
      (∑ n ∈ Finset.range (p - 4 + 1), a n) + _ + _
    have hsum := Finset.sum_range_succ a (p - 2)
    have hsum' := Finset.sum_range_succ a (p - 3)
    rw [show p - 3 + 1 = p - 2 by omega] at hsum'
    rw [show p - 4 + 1 = p - 3 by omega, hsum, hsum']
    dsimp [a]
    rw [show p - 3 + 1 = p - 2 by omega, show p - 2 + 1 = p - 1 by omega,
      show p - 2 - (p - 3) = 1 by omega, Nat.sub_self]
  rw [hprefix, ← Be_original_numerator p (p - 4) (by omega)]

/-- The explicit polynomial is the ORIGINAL coefficient-defined conductor. -/
theorem Be_eq_original_coefficient (p e : ℕ) (he : e + 4 ≤ p) (x : ℚ)
    (hx : x ≠ 0) (hM : collision.eval x ≠ 0) (hE : escape.eval x ≠ 0) :
    (Be p e).eval x = originalBe p e x := by
  classical
  have hl : lam.eval x ≠ 0 := by
    simpa [lam] using mul_ne_zero (by norm_num : (729 / 15625 : ℚ) ≠ 0)
      (pow_ne_zero 3 hx)
  have hD : sourceDivisor.eval x ≠ 0 := by
    simpa [sourceDivisor] using mul_ne_zero (mul_ne_zero (pow_ne_zero 5 hx) hM)
      (pow_ne_zero 2 hE)
  have hN := congrArg (fun P : ℚ[X] => P.eval x) (Be_original_numerator p e he)
  rw [eval_mul] at hN
  apply (mul_left_cancel₀ hD)
  rw [hN]
  unfold originalBe
  have hseries :
      (WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) *
          PowerSeries.C (1 / x) * kernelSeries x * (fSeries x)⁻¹ =
        PowerSeries.C (1 / x) *
          ((WPReview.nativePolynomial (e + 1) : PowerSeries ℚ) * scaledKernelSeries x) := by
    rw [← original_kernel_reciprocal x hl]
    ring
  rw [hseries, PowerSeries.coeff_C_mul, native_series_times_kernel_coefficient p e x he]
  unfold originalNumerator
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ e := by have := Finset.mem_range.mp hn; omega
  have hp : p = (p - 2 - n + 1) + (n + 1) := by omega
  have hlpow : (lam.eval x) ^ p =
      (lam.eval x) ^ (p - 2 - n + 1) * (lam.eval x) ^ (n + 1) := by
    conv_lhs => rw [hp]
    exact pow_add _ _ _
  rw [hlpow]
  norm_num [sourceDivisor]
  field_simp [hx, hM, hE, hl]

end WPFiniteConductorPolynomial
