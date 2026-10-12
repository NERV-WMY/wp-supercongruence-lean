import WPFiniteWSource

open Polynomial

namespace WPFinitePSource

open WPFiniteAffineLog WPFiniteABSourceTail WPFiniteWSource

variable {K : Type*} [Field K]

noncomputable def logDifference (p : ℕ) : K[X] :=
  (LP p).comp (C 4 * X) - (LP p).comp (C (1 / 4 : K) * X)

/-- The complete original negative phase, including its literal logarithm row. -/
noncomputable def Cminus (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[X] :=
  C (4 * (WPFiniteNC122.q p - WPFifthEntropy.C p u) / 15) -
    C (2 / epsilon p) * W p + C (2 / 15 : K) * logDifference p

/-- Exactly x^p times the original P=x^p A+B0+x^(-p) Cminus. -/
noncomputable def Pnumerator (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[X] :=
  X ^ (2 * p) * A p (W p) u + X ^ p * B0 p (W p) u + Cminus p u

theorem LP_comp_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (U : K[X]) :
    (1 - U) * ((LP p).comp U).derivative = (1 - U ^ (p - 1)) * U.derivative := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [derivative_comp, LP_derivative_closed_eq]
  simp only [sub_comp, pow_comp, one_comp, X_comp]
  calc
    _ = ((1 - U) ^ p - (1 - U) * U ^ (p - 1)) * U.derivative := by
      have hpow : (1 - U) ^ (p - 1) * (1 - U) = (1 - U) ^ p := by
        rw [← pow_succ, Nat.sub_add_cancel hp]
      linear_combination U.derivative * hpow
    _ = _ := by
      rw [sub_pow_char, one_pow, show U ^ p = U ^ (p - 1) * U by
        rw [← pow_succ, Nat.sub_add_cancel hp]]
      ring

theorem LP_scaled_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : K) (hc : c ^ p = c) :
    (1 - C c * X) * ((LP p).comp (C c * X)).derivative =
      C c * (1 - X ^ (p - 1)) := by
  have he := LP_comp_cleared_source p (C c * X : K[X])
  simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one,
    mul_pow] at he
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hcc : (C c : K[X]) ^ (p - 1) * C c = C c := by
    rw [← pow_succ, Nat.sub_add_cancel hp, ← map_pow, hc]
  calc
    _ = (1 - C c ^ (p - 1) * X ^ (p - 1)) * C c := he
    _ = _ := by linear_combination -X ^ (p - 1) * hcc

theorem pole_product (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) =
      -4 * (1 - 4 * X) * (1 - C (1 / 4 : K) * X) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc : 4 * C (1 / 4 : K) = (1 : K[X]) := by
    change C (4 : K) * C (1 / 4 : K) = 1
    rw [← C_mul, mul_one_div_cancel h4, C_1]
  linear_combination (4 * X ^ 2 - X) * hc

theorem logTrace_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) * (logTrace p).derivative =
      15 * X * (1 - X ^ (p - 1)) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hb := LP_scaled_cleared_source p (4 : K) h4p
  have ha := LP_scaled_cleared_source p (1 / 4 : K) hap
  simp only [map_ofNat] at hb
  have hc : 4 * C (1 / 4 : K) = (1 : K[X]) := by
    change C (4 : K) * C (1 / 4 : K) = 1
    rw [← C_mul, mul_one_div_cancel h4, C_1]
  rw [pole_product p hp, logTrace]
  simp only [derivative_add, derivative_mul, derivative_neg, derivative_C, derivative_ofNat,
    zero_mul, zero_add, map_ofNat]
  linear_combination 4 * C (1 / 4 : K) * (1 - C (1 / 4 : K) * X) * hb -
    16 * (1 - 4 * X) * ha +
    (15 - 4 * C (1 / 4 : K)) * X * (1 - X ^ (p - 1)) * hc

theorem logDifference_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) * (logDifference p).derivative =
      -15 * (1 - X ^ (p - 1)) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hb := LP_scaled_cleared_source p (4 : K) h4p
  have ha := LP_scaled_cleared_source p (1 / 4 : K) hap
  simp only [map_ofNat] at hb
  have hc : 4 * C (1 / 4 : K) = (1 : K[X]) := by
    change C (4 : K) * C (1 / 4 : K) = 1
    rw [← C_mul, mul_one_div_cancel h4, C_1]
  rw [pole_product p hp, logDifference, derivative_sub]
  simp only [map_ofNat]
  linear_combination -4 * (1 - C (1 / 4 : K) * X) * hb +
    4 * (1 - 4 * X) * ha + (1 - X ^ (p - 1)) * hc

theorem Pnumerator_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Pnumerator p u).derivative =
      C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) * (W p).derivative +
        C (2 / 15 : K) * (X ^ p * (logTrace p).derivative + (logDifference p).derivative) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have heps : epsilon p ≠ (0 : K) := by
    exact pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hs : (2 / epsilon p : K) = 4 * (1 / (2 * epsilon p)) := by
    generalize hd2 : (2 : K) = d2
    have hd2u := hd2 ▸ h2
    field_simp [hd2u, heps]
    subst d2
    ring
  have hc2 : C (2 / epsilon p : K) = 4 * C (1 / (2 * epsilon p) : K) := by
    rw [hs, map_mul, map_ofNat]
  have hc17 : C (17 / (2 * epsilon p) : K) = 17 * C (1 / (2 * epsilon p) : K) := by
    simp only [div_eq_mul_inv, one_mul, map_mul, map_ofNat]
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hdXp : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, hp0, map_zero, zero_mul]
  have hdX2p : (X ^ (2 * p) : K[X]).derivative = 0 := by
    rw [derivative_X_pow, Nat.cast_mul, hp0, mul_zero, map_zero, zero_mul]
  simp only [Pnumerator, Cminus, A, B0, Bpoly, derivative_add, derivative_sub,
    derivative_mul, derivative_C, derivative_ofNat, zero_mul, zero_add, hdXp, hdX2p, hc2, hc17]
  ring

theorem Pnumerator_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (4 - X : K[X]) * (4 * X - 1) *
        ((Pnumerator p u).derivative + C (1 / 2 : K) * X ^ (p - 1)) =
      C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) *
        (X + 1) ^ ((p - 1) / 2) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have heps : epsilon p ≠ (0 : K) := by
    exact pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hlambda : C (1 / (2 * epsilon p) : K) * C (epsilon p) = C (1 / 2 : K) := by
    rw [← C_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    calc
      (epsilon p)⁻¹ * (2 : K)⁻¹ * epsilon p = (2 : K)⁻¹ * ((epsilon p)⁻¹ * epsilon p) := by ring
      _ = _ := by rw [inv_mul_cancel₀ heps, mul_one]
  have hgamma : C (2 / 15 : K) * 15 = (2 : K[X]) := by
    change C (2 / 15 : K) * C (15 : K) = C (2 : K)
    rw [← C_mul, div_mul_cancel₀ _ h15]
  have hc2 : C (1 / 2 : K) * 2 = (1 : K[X]) := by
    change C (1 / 2 : K) * C (2 : K) = 1
    rw [← C_mul, one_div_mul_cancel h2, C_1]
  have hxpow : (X : K[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hxp2 : (X : K[X]) ^ (2 * p) = X ^ p * X ^ p := by
    rw [← pow_add]
    congr 1
    omega
  have hcancel :
      -C (1 / 2 : K) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) +
        2 * (X ^ p * X - X ^ p * X ^ p - 1 + X ^ (p - 1)) +
        C (1 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) = (0 : K[X]) := by
    linear_combination
      2 * (X ^ p * X ^ p + 1 - X ^ p * X - X ^ (p - 1)) * hc2 +
        (17 - 4 * X) * C (1 / 2 : K) * hxpow + 4 * C (1 / 2 : K) * hxp2
  calc
    _ = C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) *
          ((X + 1) ^ ((p - 1) / 2) - C (epsilon p)) +
        C (2 / 15 : K) * (X ^ p * (15 * X * (1 - X ^ (p - 1))) -
          15 * (1 - X ^ (p - 1))) +
        C (1 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) := by
      rw [Pnumerator_derivative p hp u]
      linear_combination
        C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) * W_cleared_source (K := K) p hp +
          C (2 / 15 : K) * X ^ p * logTrace_cleared_source (K := K) p hp +
          C (2 / 15 : K) * logDifference_cleared_source (K := K) p hp
    _ = C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) *
          (X + 1) ^ ((p - 1) / 2) -
        C (1 / 2 : K) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) +
        2 * (X ^ p * X - X ^ p * X ^ p - 1 + X ^ (p - 1)) +
        C (1 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) := by
      calc
        _ = C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) *
              (X + 1) ^ ((p - 1) / 2) -
            (C (1 / (2 * epsilon p)) * C (epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) +
            (C (2 / 15 : K) * 15) *
              (X ^ p * X - X ^ p * (X ^ (p - 1) * X) - 1 + X ^ (p - 1)) +
            C (1 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) := by ring
        _ = _ := by rw [hlambda, hgamma, hxpow]
    _ = _ := by linear_combination hcancel

theorem A_literal_even_difference (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    A p (W p) u = C (-4 / 15 : K) *
      (C (WPFiniteNC122.q p) + (deltaE p).comp squaredCoordinate) := by
  have heps : epsilon p ≠ (0 : K) := by
    exact pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hs : (2 / epsilon p : K) * (2 * epsilon p / 15) = 4 / 15 := by
    calc
      _ = (4 / 15 : K) * ((epsilon p)⁻¹ * epsilon p) := by ring
      _ = _ := by rw [inv_mul_cancel₀ heps, mul_one]
  rw [A, W, ← mul_assoc, ← C_mul, hs, deltaE_fifth p hp u hu]
  simp only [uSlot, div_eq_mul_inv, map_mul, map_add, map_neg, map_ofNat]
  ring

end WPFinitePSource
