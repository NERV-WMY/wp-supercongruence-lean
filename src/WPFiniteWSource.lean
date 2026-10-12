import WPFiniteABSourceTail

open scoped BigOperators
open Polynomial

namespace WPFiniteWSource

open WPFiniteAffineLog WPFiniteKSource WPFiniteJSource WPFiniteJHighCoefficient
  WPFiniteABSourceTail

variable {K : Type*} [Field K]

/-- Literal even logarithm difference as a polynomial in the squared coordinate. -/
noncomputable def deltaE (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
    C (((4 : K) ^ j - 1) / (2 * (j : K))) * X ^ j

noncomputable def squaredCoordinate : K[X] := C (5 : K)⁻¹ * (X + 1)

/-- Original normalized NC49/SB31 primitive, with its entire literal cutoff. -/
noncomputable def W (p : ℕ) : K[X] :=
  C (2 * epsilon p / 15) *
    ((deltaE p).comp squaredCoordinate - C ((deltaE p).eval (1 / 5)))

theorem half_exponent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    p = 2 * ((p - 1) / 2) + 1 := by
  obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem four_half_power (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 : K) ^ ((p - 1) / 2) = 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hp2 : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 2
  rw [half_exponent p hp, pow_succ, pow_mul,
    show (2 : K) ^ 2 = 4 by norm_num] at hp2
  apply mul_right_cancel₀ h2
  simpa only [one_mul] using hp2

theorem deltaE_square (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (deltaE p : K[X]).comp (X ^ 2) = (EP p).comp (2 * X) - EP p := by
  simp only [EP_half_cutoff p hp]
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp]
  rw [← Finset.sum_sub_distrib]
  unfold deltaE
  rw [sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  have hpow : (2 * X : K[X]) ^ (2 * j) = C ((4 : K) ^ j) * (X ^ 2) ^ j := by
    rw [pow_mul, mul_pow, show (2 : K[X]) ^ 2 = C (4 : K) by simp only [map_ofNat]; norm_num]
    rw [mul_pow, map_pow]
  rw [hpow, ← pow_mul]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, map_sub, map_mul, map_one]
  ring

theorem squaredCoordinate_conic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (squaredCoordinate : K[X]).comp conic = X ^ 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc : C (5 : K)⁻¹ * 5 = (1 : K[X]) := by
    change C (5 : K)⁻¹ * C (5 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h5, C_1]
  simp only [squaredCoordinate, mul_comp, C_comp, add_comp, X_comp, one_comp, conic]
  linear_combination X ^ 2 * hc

theorem W_conic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (W p : K[X]).comp conic = C (2 * epsilon p / 15) *
      ((EP p).comp (2 * X) - EP p - C ((deltaE p).eval (1 / 5))) := by
  rw [W, mul_comp, C_comp, sub_comp, C_comp, comp_assoc,
    squaredCoordinate_conic p hp, deltaE_square p hp]

theorem deltaE_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (deltaE p).eval (1 / 5) = WPFifthEntropy.C p u := by
  have he := congrArg (fun P : K[X] => P.eval u) (deltaE_square (K := K) p hp)
  rw [eval_comp, eval_pow, eval_X, hu, eval_sub, eval_comp,
    eval_mul, eval_ofNat, eval_X] at he
  simp only [EP, eval_mul, eval_C, eval_add, eval_comp,
    eval_neg, eval_X, LP_eval_eq, WPFifthEntropy.C, WPFiniteField.E,
    div_eq_mul_inv] at he ⊢
  linear_combination he

theorem W_origin (p : ℕ) : (W p : K[X]).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [W, squaredCoordinate, one_div]

theorem deltaE_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (deltaE p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  have hN : 1 ≤ (p - 1) / 2 := by omega
  have ht : ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      (C (((4 : K) ^ j - 1) / (2 * (j : K))) * X ^ j : K[X]) =
      ∑ j ∈ Finset.Ico 1 ((p - 1) / 2),
        C (((4 : K) ^ j - 1) / (2 * (j : K))) * X ^ j := by
    rw [Finset.sum_Ico_succ_top hN, four_half_power p hp]
    simp
  rw [deltaE, ht]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hr := Finset.mem_Ico.mp hj
  exact (natDegree_C_mul_le _ _).trans (by simpa using (show j ≤ (p - 1) / 2 - 1 by omega))

theorem W_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (W p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  have hS : (squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  unfold W
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_comp_le.trans (by
      have := Nat.mul_le_mul (deltaE_degree (K := K) p hp) hS
      simpa only [Nat.mul_one] using this)
  · simp

noncomputable def geometricP (n : ℕ) (c : K) : K[X] :=
  ∑ r ∈ Finset.range n, C (c ^ (r + 1)) * X ^ r

theorem geometricP_source (n : ℕ) (c : K) :
    (1 - C c * X) * geometricP n c = C c * (1 - (C c * X) ^ n) := by
  induction n with
  | zero => simp [geometricP]
  | succ n ih =>
    rw [geometricP, Finset.sum_range_succ]
    change (1 - C c * X) * (geometricP n c + C (c ^ (n + 1)) * X ^ n) = _
    rw [mul_add, ih]
    simp only [pow_succ, mul_pow, map_mul, map_pow]
    ring

theorem deltaE_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (deltaE p : K[X]).derivative = C (1 / 2 : K) *
      (geometricP ((p - 1) / 2) 4 - geometricP ((p - 1) / 2) 1) := by
  rw [deltaE, derivative_sum, Finset.sum_Ico_eq_sum_range]
  simp only [show (p - 1) / 2 + 1 - 1 = (p - 1) / 2 by omega]
  rw [geometricP, geometricP, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show 1 + r = r + 1 by omega]
  have hru := WPFiniteField.denominator_ne_zero (K := K) p (r + 1)
    (Finset.mem_Ico.mpr ⟨by omega, by have := Finset.mem_range.mp hr; omega⟩)
  rw [derivative_C_mul_X_pow]
  simp only [Nat.cast_add, Nat.cast_one, one_pow, Nat.add_sub_cancel,
    div_eq_mul_inv, mul_inv_rev, map_mul, map_sub, map_one]
  have hc : C ((r : K) + 1)⁻¹ * C ((r : K) + 1) = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ (by simpa only [Nat.cast_add, Nat.cast_one] using hru), C_1]
  linear_combination (C ((4 : K) ^ (r + 1)) - 1) * C (2 : K)⁻¹ * X ^ r * hc

theorem deltaE_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - 4 * X : K[X]) * (1 - X) * (deltaE p).derivative =
      C (3 / 2 : K) * (1 - X ^ ((p - 1) / 2)) := by
  have h4 := geometricP_source ((p - 1) / 2) (4 : K)
  have h1 := geometricP_source ((p - 1) / 2) (1 : K)
  simp only [mul_pow, ← map_pow, four_half_power p hp, C_1, one_mul] at h4
  simp only [map_one, one_mul] at h1
  rw [deltaE_derivative p hp]
  simp only [div_eq_mul_inv, map_mul, map_ofNat, map_one] at h4 h1 ⊢
  linear_combination C (2 : K)⁻¹ * ((1 - X) * h4 - (1 - 4 * X) * h1)

theorem W_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) * (W p).derivative =
      (X + 1) ^ ((p - 1) / 2) - C (epsilon p) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hc5 : C (5 : K)⁻¹ * 5 = (1 : K[X]) := by
    change C (5 : K)⁻¹ * C (5 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h5, C_1]
  have hA : (4 - X : K[X]) * (4 * X - 1) =
      -25 * (1 - 4 * squaredCoordinate) * (1 - squaredCoordinate) := by
    unfold squaredCoordinate
    linear_combination (-25 * (X + 1) + 4 * (X + 1) ^ 2 * (5 * C (5 : K)⁻¹ + 1)) * hc5
  have hs := congrArg (fun Q : K[X] => Q.comp squaredCoordinate)
    (deltaE_cleared_source (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, ofNat_comp, X_comp, C_comp, pow_comp] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have hscale : (-25 : K) * (2 * epsilon p / 15) * (1 / 5) * (3 / 2) = -epsilon p := by
    generalize hd2 : (2 : K) = d2
    generalize hd5 : (5 : K) = d5
    generalize hd15 : (15 : K) = d15
    have h2u := hd2 ▸ h2
    have h5u := hd5 ▸ h5
    have h15u := hd15 ▸ h15
    field_simp [h2u, h5u, h15u]
    subst d2 d5 d15
    ring
  have hpS : C (epsilon p) * (squaredCoordinate : K[X]) ^ ((p - 1) / 2) =
      (X + 1) ^ ((p - 1) / 2) := by
    rw [squaredCoordinate, mul_pow, epsilon, map_pow]
    have hunit : C (5 : K) * C (5 : K)⁻¹ = (1 : K[X]) := by
      rw [← C_mul, mul_inv_cancel₀ h5, C_1]
    rw [← mul_assoc, ← mul_pow, hunit, one_pow, one_mul]
  rw [W, derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub,
    derivative_C, sub_zero, derivative_comp]
  have hderS : (squaredCoordinate : K[X]).derivative = C (5 : K)⁻¹ := by
    simp [squaredCoordinate]
  rw [hderS]
  calc
    _ = C ((-25 : K) * (2 * epsilon p / 15) * (1 / 5)) *
        ((1 - 4 * squaredCoordinate) * (1 - squaredCoordinate) *
          (deltaE p).derivative.comp squaredCoordinate) := by
            rw [hA]
            simp only [one_div, map_mul, map_neg, map_ofNat]
            ring
    _ = C ((-25 : K) * (2 * epsilon p / 15) * (1 / 5)) *
        (C (3 / 2) * (1 - squaredCoordinate ^ ((p - 1) / 2))) := by rw [hs]
    _ = -C (epsilon p) * (1 - squaredCoordinate ^ ((p - 1) / 2)) := by
      rw [← mul_assoc, ← map_mul, hscale, map_neg]
    _ = C (epsilon p) * squaredCoordinate ^ ((p - 1) / 2) - C (epsilon p) := by ring
    _ = _ := by rw [hpS]

end WPFiniteWSource
