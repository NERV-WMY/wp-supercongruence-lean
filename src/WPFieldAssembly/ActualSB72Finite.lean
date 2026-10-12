import WPFiniteZSource
import WPFiniteLoop
import WPActualPartialHarmonic

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1600000

section SmallDegree
variable {K : Type*} [Field K]

private theorem euler_degree_le (P : K[X]) :
    (X * P.derivative).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    rw [coeff_X_mul, coeff_derivative,
      coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1), zero_mul]

private theorem euler_top_coefficient (P : K[X]) :
    (X * P.derivative).coeff P.natDegree = P.leadingCoeff * (P.natDegree : K) := by
  cases hd : P.natDegree with
  | zero => simp
  | succ n =>
    rw [coeff_X_mul, coeff_derivative, leadingCoeff, hd]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem flat_small_degree_equal (p : ℕ) [CharP K p]
    (E f : K[X]) (hE : E ≠ 0) (hf : f ≠ 0)
    (hEd : E.natDegree < p) (hfd : f.natDegree < p)
    (hflat : f * E.derivative - f.derivative * E = 0) :
    E.natDegree = f.natDegree := by
  have he : f * (X * E.derivative) - (X * f.derivative) * E = 0 := by
    linear_combination X * hflat
  have hc := congrArg (fun P : K[X] => P.coeff (f.natDegree + E.natDegree)) he
  rw [coeff_sub, coeff_zero,
    coeff_mul_add_eq_of_natDegree_le le_rfl (euler_degree_le E)] at hc
  have hc' : ((X * f.derivative) * E).coeff (f.natDegree + E.natDegree) =
      (X * f.derivative).coeff f.natDegree * E.coeff E.natDegree :=
    coeff_mul_add_eq_of_natDegree_le (euler_degree_le f) le_rfl
  rw [hc', euler_top_coefficient, euler_top_coefficient] at hc
  change f.leadingCoeff * (E.leadingCoeff * (E.natDegree : K)) -
    (f.leadingCoeff * (f.natDegree : K)) * E.leadingCoeff = 0 at hc
  have hz : (f.leadingCoeff * E.leadingCoeff) *
      ((E.natDegree : K) - (f.natDegree : K)) = 0 := by linear_combination hc
  have hcast := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (leadingCoeff_ne_zero.mpr hf) (leadingCoeff_ne_zero.mpr hE)))
  exact CharP.natCast_injOn_Iio K p hEd hfd hcast

/-- A proved degree band excludes every nonconstant Frobenius quotient. -/
theorem flat_small_degree_endpoint_zero (p : ℕ) [CharP K p]
    (E f : K[X]) (hf : f ≠ 0)
    (hEd : E.natDegree < p) (hfd : f.natDegree < p)
    (hflat : f * E.derivative - f.derivative * E = 0)
    (a : K) (hEa : E.eval a = 0) (hfa : f.eval a = 1) : E = 0 := by
  by_cases hE : E = 0
  · exact hE
  have hd := flat_small_degree_equal p E f hE hf hEd hfd hflat
  let c : K := E.leadingCoeff / f.leadingCoeff
  let B : K[X] := E - Polynomial.C c * f
  have hBd : B.natDegree < p :=
    (natDegree_sub_le _ _).trans_lt
      (max_lt hEd ((natDegree_C_mul_le c f).trans_lt hfd))
  have hBflat : f * B.derivative - f.derivative * B = 0 := by
    dsimp only [B]
    rw [derivative_sub, derivative_C_mul]
    linear_combination hflat
  have hBc : B.coeff f.natDegree = 0 := by
    have hEc : E.coeff f.natDegree = E.leadingCoeff := by rw [← hd]; rfl
    dsimp only [B]
    rw [coeff_sub, coeff_C_mul, hEc]
    change E.leadingCoeff - c * f.leadingCoeff = 0
    dsimp only [c]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hf)).symm
  have hB : B = 0 := by
    by_contra hB
    have hdeg := flat_small_degree_equal p B f hB hf hBd hfd hBflat
    have hlead : B.leadingCoeff = 0 := by
      rw [leadingCoeff, hdeg]
      exact hBc
    exact hB (leadingCoeff_eq_zero.mp hlead)
  have hc : c = 0 := by
    have h := congrArg (fun P : K[X] => P.eval a) hB
    change (E - Polynomial.C c * f).eval a = (0 : K[X]).eval a at h
    rw [eval_zero] at h
    simpa only [eval_sub, eval_mul, eval_C, hEa, hfa, mul_one, zero_sub,
      neg_eq_zero] using h
  dsimp only [B] at hB
  simpa only [hc, Polynomial.C_0, zero_mul, sub_zero] using hB

end SmallDegree

section FinitePrimitive
variable {K : Type*} [Field K]

/-- The retained finite SB72 primitive, with its full literal cutoff. -/
noncomputable def Dstar (p : ℕ) : K[X] :=
  -Polynomial.C (1 / 3 : K) * (WPFiniteWSource.deltaE p).comp
    WPFiniteWSource.squaredCoordinate

theorem Dstar_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Dstar p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  unfold Dstar
  rw [← Polynomial.C_neg]
  exact (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans
    ((Nat.mul_le_mul (WPFiniteWSource.deltaE_degree (K := K) p hp) hs).trans (by omega)))

theorem Dstar_literal_sum (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Dstar p : K[X]) = Polynomial.C (1 / 6 : K) *
      ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        Polynomial.C ((1 - (4 : K) ^ j) / (j : K)) *
          WPFiniteWSource.squaredCoordinate ^ j := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 := WPFiniteField.denominator_ne_zero (K := K) p 6
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2 h3 h6
  simp only [Dstar, WPFiniteWSource.deltaE, sum_comp, mul_comp, C_comp,
    pow_comp, X_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 := WPFiniteField.denominator_ne_zero (K := K) p j
    (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1, by
      have := (Finset.mem_Ico.mp hj).2; omega⟩)
  simp only [← mul_assoc, ← Polynomial.C_neg, ← Polynomial.C_mul]
  congr 2
  field_simp [h2, h3, h6, hj0]
  ring

theorem Dstar_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]) * (Dstar p).derivative =
      Polynomial.C (5 / 2 : K) *
        (1 - WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2)) := by
  let s : K[X] := WPFiniteWSource.squaredCoordinate
  let E : K[X] := WPFiniteWSource.deltaE p
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h3 h5
  have hu : (5 : K[X]) * Polynomial.C (5 : K)⁻¹ = 1 := by
    change Polynomial.C (5 : K) * Polynomial.C (5 : K)⁻¹ = Polynomial.C 1
    rw [← Polynomial.C_mul, mul_inv_cancel₀ h5]
  have hs : (5 : K[X]) * s = X + 1 := by
    dsimp only [s, WPFiniteWSource.squaredCoordinate]
    rw [← mul_assoc, hu, one_mul]
  have hfactor : (25 : K[X]) * (1 - 4 * s) * (1 - s) = -WPFiniteZSource.Abar := by
    have he : (5 - 4 * (5 * s)) * (5 - 5 * s) = -(WPFiniteZSource.Abar : K[X]) := by
      rw [hs]
      unfold WPFiniteZSource.Abar
      ring
    linear_combination he
  have hA : (WPFiniteZSource.Abar : K[X]) =
      -(25 * (1 - 4 * s) * (1 - s)) := by linear_combination hfactor
  have he := congrArg (fun P : K[X] => P.comp s)
    (WPFiniteWSource.deltaE_cleared_source (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, ofNat_comp, X_comp, C_comp, pow_comp] at he
  change (1 - 4 * s) * (1 - s) * E.derivative.comp s =
    Polynomial.C (3 / 2 : K) * (1 - s ^ ((p - 1) / 2)) at he
  have hd : (Dstar p : K[X]).derivative =
      (-Polynomial.C (1 / 3 : K)) * E.derivative.comp s * Polynomial.C (5 : K)⁻¹ := by
    simp only [Dstar, derivative_mul, derivative_neg, derivative_C, neg_zero,
      zero_mul, zero_add, derivative_comp]
    dsimp only [s, E, WPFiniteWSource.squaredCoordinate]
    simp only [derivative_C_mul, derivative_add, derivative_X, derivative_one,
      add_zero, mul_one]
    ring
  have hscalar : (25 : K[X]) * (-Polynomial.C (1 / 3 : K)) *
      Polynomial.C (5 : K)⁻¹ * Polynomial.C (3 / 2 : K) =
      -Polynomial.C (5 / 2 : K) := by
    change Polynomial.C (25 : K) * (-Polynomial.C (1 / 3 : K)) *
      Polynomial.C (5 : K)⁻¹ * Polynomial.C (3 / 2 : K) =
      -Polynomial.C (5 / 2 : K)
    rw [← Polynomial.C_neg, ← Polynomial.C_mul, ← Polynomial.C_mul,
      ← Polynomial.C_mul, ← Polynomial.C_neg]
    congr 1
    field_simp [h3, h5]
    ring
  rw [hd, hA]
  change _ = Polynomial.C (5 / 2 : K) * (1 - s ^ ((p - 1) / 2))
  calc
    _ = -(25 * (-Polynomial.C (1 / 3 : K)) * Polynomial.C (5 : K)⁻¹) *
        ((1 - 4 * s) * (1 - s) * E.derivative.comp s) := by ring
    _ = _ := by rw [he]; linear_combination -(1 - s ^ ((p - 1) / 2)) * hscalar

private theorem deltaE_eval (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (z : K) :
    (WPFiniteWSource.deltaE p : K[X]).eval z =
      (1 / 2 : K) * (WPFiniteLoop.L ((p - 1) / 2) (4 * z) -
        WPFiniteLoop.L ((p - 1) / 2) z) := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2
  simp only [WPFiniteWSource.deltaE, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X, WPFiniteLoop.L, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 := WPFiniteField.denominator_ne_zero (K := K) p j
    (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1, by
      have := (Finset.mem_Ico.mp hj).2; omega⟩)
  rw [mul_pow]
  field_simp [h2, hj0]

/-- Both primitive endpoints retain the corrected finite-log inversion sign. -/
theorem Dstar_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Dstar p : K[X]).eval (1 / 4) = WPFiniteNC122.q p + WPFiniteNC122.h p / 6 ∧
      (Dstar p : K[X]).eval 4 = -WPFiniteNC122.q p - WPFiniteNC122.h p / 3 := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 := WPFiniteField.denominator_ne_zero (K := K) p 6
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2 h3 h4 h5 h6
  have hsa : (WPFiniteWSource.squaredCoordinate : K[X]).eval (1 / 4) = 1 / 4 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add,
      eval_X, eval_one]
    field_simp [h4, h5]
    ring
  have hsb : (WPFiniteWSource.squaredCoordinate : K[X]).eval 4 = 1 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add,
      eval_X, eval_one]
    field_simp [h5]
    ring
  have h41 : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  obtain ⟨hL1, hL4, hLq⟩ := WPFiniteLoop.L_rational_ends (K := K) p hp
  simp only [Dstar, eval_mul, eval_neg, eval_C, eval_comp, hsa, hsb,
    deltaE_eval p hp, h41, mul_one, hL1, hL4, hLq, WPFiniteNC122.h, WPFiniteNC122.q]
  constructor <;> field_simp [h2, h3, h6] <;> ring

theorem actual_harmonic_is_finite_h (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualGaussBottom.fieldHarmonic p (p / 6) = (WPFiniteNC122.h p : ZMod p) := by
  rw [WPActualPartialHarmonic.actual_harmonic_sixth p (by omega)]
  unfold WPFiniteNC122.h WPFiniteNC122.q
  ring

end FinitePrimitive

end WPFieldAssembly.ActualBpairContraction
