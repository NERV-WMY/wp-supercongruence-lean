import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Tactic

open scoped PowerSeries LaurentSeries

set_option backward.isDefEq.respectTransparency false

namespace WPFirstResidue.LaurentDifferential

variable {K : Type*} [Field K]

theorem algebraMap_constant (a : K) :
    algebraMap K K⸨X⸩ a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
  exact PowerSeries.coe_C a

theorem derivative_coefficient (f : K⸨X⸩) (j : ℤ) :
    (LaurentSeries.derivative K f).coeff j = (j + 1 : ℤ) * f.coeff (j + 1) := by
  simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_coeff,
    zsmul_eq_mul]

theorem derivative_residue_zero (f : K⸨X⸩) :
    (LaurentSeries.derivative K f).coeff (-1) = 0 := by
  rw [derivative_coefficient]
  norm_num

theorem derivative_monomial_mul (n : ℤ) (c : K) (f : K⸨X⸩) :
    LaurentSeries.derivative K (HahnSeries.single n c * f) =
      HahnSeries.single (n - 1) ((n : K) * c) * f +
        HahnSeries.single n c * LaurentSeries.derivative K f := by
  ext j
  rw [derivative_coefficient, HahnSeries.coeff_single_mul,
    HahnSeries.coeff_add, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
    derivative_coefficient]
  have hj : j - (n - 1) = j + 1 - n := by omega
  have hj' : j - n + 1 = j + 1 - n := by omega
  rw [hj, hj']
  push_cast
  ring

theorem derivative_powerSeries (f : K⟦X⟧) :
    LaurentSeries.derivative K (f : K⸨X⸩) =
      ((PowerSeries.derivative K f : K⟦X⟧) : K⸨X⸩) := by
  ext j
  rw [derivative_coefficient, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  cases j with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
      if_neg (by omega), if_neg (by omega), Int.natAbs_natCast,
      PowerSeries.coeff_derivative]
    push_cast
    ring
  | negSucc n =>
    cases n with
    | zero => norm_num
    | succ n =>
      rw [if_pos (by omega), if_pos (by omega)]
      simp

/-- Product differentiation for full Laurent series, including their principal parts. -/
theorem derivative_mul (f g : K⸨X⸩) :
    LaurentSeries.derivative K (f * g) =
      LaurentSeries.derivative K f * g + f * LaurentSeries.derivative K g := by
  obtain ⟨m, F, hF⟩ : ∃ m : ℤ, ∃ F : K⟦X⟧,
      f = HahnSeries.single m 1 * (F : K⸨X⸩) :=
    ⟨f.order, f.powerSeriesPart, f.single_order_mul_powerSeriesPart.symm⟩
  obtain ⟨n, G, hG⟩ : ∃ n : ℤ, ∃ G : K⟦X⟧,
      g = HahnSeries.single n 1 * (G : K⸨X⸩) :=
    ⟨g.order, g.powerSeriesPart, g.single_order_mul_powerSeriesPart.symm⟩
  rw [hF, hG]
  have hs : (HahnSeries.single m 1 : K⸨X⸩) * HahnSeries.single n 1 =
      HahnSeries.single (m + n) 1 := by
    rw [HahnSeries.single_mul_single, one_mul]
  have hprod : (HahnSeries.single m 1 * (F : K⸨X⸩)) *
      (HahnSeries.single n 1 * (G : K⸨X⸩)) =
        HahnSeries.single (m + n) 1 * ((F * G : K⟦X⟧) : K⸨X⸩) := by
    rw [PowerSeries.coe_mul, ← hs]
    ring
  rw [hprod, derivative_monomial_mul, derivative_monomial_mul,
    derivative_monomial_mul, derivative_powerSeries, derivative_powerSeries,
    derivative_powerSeries, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    PowerSeries.coe_add,
    PowerSeries.coe_mul, PowerSeries.coe_mul]
  simp only [mul_add, add_mul, mul_assoc]
  have hmn : HahnSeries.single (m + n - 1) (((m + n : ℤ) : K) * 1) =
      HahnSeries.single (m - 1) (m : K) * HahnSeries.single n 1 +
        HahnSeries.single m 1 * HahnSeries.single (n - 1) (n : K) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    simp only [mul_one, one_mul]
    rw [show m - 1 + n = m + n - 1 by omega,
      show m + (n - 1) = m + n - 1 by omega, ← HahnSeries.single_add]
    push_cast
    simp
  rw [hmn, ← hs]
  rw [PowerSeries.coe_mul]
  ring

/-- Formal integration by parts has zero residue in every characteristic. -/
theorem residue_integration_by_parts (f g : K⸨X⸩) :
    (f * LaurentSeries.derivative K g).coeff (-1) =
      -(LaurentSeries.derivative K f * g).coeff (-1) := by
  have h := derivative_residue_zero (f * g)
  rw [derivative_mul, HahnSeries.coeff_add] at h
  linear_combination h

theorem derivative_one : LaurentSeries.derivative K (1 : K⸨X⸩) = 0 := by
  ext j
  rw [derivative_coefficient, HahnSeries.coeff_zero]
  by_cases hj : j + 1 = 0
  · simp [hj]
  · simp [HahnSeries.coeff_one, hj]

/-- The literal coefficient derivative, equipped with its proved Leibniz law. -/
noncomputable def nativeDerivation : Derivation K K⸨X⸩ K⸨X⸩ where
  toFun := LaurentSeries.derivative K
  map_add' f g := (LaurentSeries.derivative K).map_add f g
  map_smul' a f := by
    change LaurentSeries.derivative K (algebraMap K K⸨X⸩ a * f) =
      a • LaurentSeries.derivative K f
    rw [algebraMap_constant, HahnSeries.C_mul_eq_smul]
    exact (LaurentSeries.derivative K).map_smul a f
  map_one_eq_zero' := derivative_one (K := K)
  leibniz' f g := by
    change LaurentSeries.derivative K (f * g) =
      f * LaurentSeries.derivative K g + g * LaurentSeries.derivative K f
    rw [derivative_mul]
    ring

theorem nativeDerivation_apply (f : K⸨X⸩) :
    nativeDerivation f = LaurentSeries.derivative K f := rfl

theorem derivative_constant (a : K) :
    LaurentSeries.derivative K (algebraMap K K⸨X⸩ a) = 0 := by
  rw [algebraMap_constant]
  ext j
  rw [derivative_coefficient, HahnSeries.coeff_zero]
  by_cases hj : j + 1 = 0
  · simp [hj]
  · simp [HahnSeries.C_apply, hj]

theorem derivative_pow (x : K⸨X⸩) (n : ℕ) :
    LaurentSeries.derivative K (x ^ n) =
      (n : K⸨X⸩) * x ^ (n - 1) * LaurentSeries.derivative K x := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul]
    exact derivative_one
  | succ n hn =>
    rw [pow_succ, derivative_mul, hn]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem derivative_polynomial_evaluation (P : Polynomial K) (x : K⸨X⸩) :
    LaurentSeries.derivative K (P.eval₂ (algebraMap K K⸨X⸩) x) =
      P.derivative.eval₂ (algebraMap K K⸨X⸩) x * LaurentSeries.derivative K x := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.eval₂_add, map_add, hP, hQ,
      Polynomial.derivative_add, Polynomial.eval₂_add]
    ring
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, derivative_mul, derivative_constant,
      derivative_pow, Polynomial.derivative_monomial, Polynomial.eval₂_monomial]
    simp only [zero_mul, zero_add, map_mul, map_natCast]
    ring

theorem derivative_inverse (f : K⸨X⸩) :
    LaurentSeries.derivative K f⁻¹ =
      -(f⁻¹ ^ 2 * LaurentSeries.derivative K f) := by
  by_cases hf : f = 0
  · subst f
    simp only [inv_zero, map_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, neg_zero]
  · have h := derivative_mul f f⁻¹
    rw [mul_inv_cancel₀ hf, derivative_one] at h
    have he : f * LaurentSeries.derivative K f⁻¹ =
        -(LaurentSeries.derivative K f * f⁻¹) := by linear_combination -h
    calc
      _ = (f⁻¹ * f) * LaurentSeries.derivative K f⁻¹ := by
        rw [inv_mul_cancel₀ hf, one_mul]
      _ = f⁻¹ * (f * LaurentSeries.derivative K f⁻¹) := by ring
      _ = _ := by rw [he]; ring

theorem derivative_quotient (f g : K⸨X⸩) :
    LaurentSeries.derivative K (f / g) =
      (LaurentSeries.derivative K f * g - f * LaurentSeries.derivative K g) / g ^ 2 := by
  by_cases hg : g = 0
  · subst g
    simp only [div_zero, map_zero, mul_zero, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · rw [div_eq_mul_inv, derivative_mul, derivative_inverse]
    have hs : g * g⁻¹ ^ 2 = g⁻¹ := by
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hg, one_mul]
    calc
      _ = LaurentSeries.derivative K f * g⁻¹ -
          f * LaurentSeries.derivative K g * g⁻¹ ^ 2 := by ring
      _ = LaurentSeries.derivative K f * (g * g⁻¹ ^ 2) -
          f * LaurentSeries.derivative K g * g⁻¹ ^ 2 := by rw [hs]
      _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring

end WPFirstResidue.LaurentDifferential
