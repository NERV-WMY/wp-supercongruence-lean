import WPFinitePSource

open scoped BigOperators
open Polynomial

namespace WPFiniteLVSource

open WPFiniteAffineLog WPFiniteKSource WPFiniteJSource WPFiniteJHighCoefficient
  WPFiniteABSourceTail WPFiniteWSource WPFinitePSource WPFiniteCubicLog

variable {K : Type*} [Field K]

noncomputable def evenSquared (p : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1), C (1 / (2 * (j : K))) * X ^ j

noncomputable def V : K[X] := squaredCoordinate * (C (5 : K)⁻¹ * (4 * X - 11)) ^ 2

noncomputable def LV (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  C (WPFiniteNC122.q p) + (evenSquared p).comp V

theorem evenSquared_square (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (evenSquared p : K[X]).comp (X ^ 2) = EP p := by
  rw [EP_half_cutoff p hp, evenSquared, sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_comp, C_comp, pow_comp, X_comp, ← pow_mul,
    Nat.cast_mul, Nat.cast_ofNat, one_div]

theorem V_conic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (V : K[X]).comp conic = Tc ^ 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc5 : C (5 : K)⁻¹ * 5 = (1 : K[X]) := by
    change C (5 : K)⁻¹ * C (5 : K) = 1
    rw [← C_mul, inv_mul_cancel₀ h5, C_1]
  have hb : (C (5 : K)⁻¹ * (4 * X - 11) : K[X]).comp conic = 4 * X ^ 2 - 3 := by
    simp only [mul_comp, C_comp, sub_comp, ofNat_comp, X_comp, conic]
    linear_combination (4 * X ^ 2 - 3) * hc5
  rw [V, mul_comp, pow_comp, squaredCoordinate_conic p hp, hb]
  unfold Tc
  ring

theorem LV_conic (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (LV p : K[X]).comp conic = (LPsrc p).comp Tc := by
  have he := congrArg (fun Q : K[X] => Q.comp Tc) (evenSquared_square (K := K) p hp)
  simp only [comp_assoc, pow_comp, X_comp] at he
  rw [LV, add_comp, C_comp, comp_assoc, V_conic p hp, he,
    LPsrc, add_comp, C_comp]

theorem evenSquared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (evenSquared p : K[X]).derivative = C (1 / 2 : K) *
      geometricP ((p - 1) / 2) 1 := by
  rw [evenSquared, derivative_sum, Finset.sum_Ico_eq_sum_range]
  simp only [show (p - 1) / 2 + 1 - 1 = (p - 1) / 2 by omega,
    geometricP, one_pow, map_one, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show 1 + r = r + 1 by omega, derivative_C_mul_X_pow]
  have hu : ((r + 1 : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p (r + 1)
    (Finset.mem_Ico.mpr ⟨by omega, by have := Finset.mem_range.mp hr; omega⟩)
  have hs : (1 / (2 * ((r + 1 : ℕ) : K))) * ((r + 1 : ℕ) : K) = (1 / 2 : K) := by
    simp only [one_div, mul_inv_rev]
    calc
      _ = (2 : K)⁻¹ * ((((r + 1 : ℕ) : K))⁻¹ * ((r + 1 : ℕ) : K)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hu, mul_one]
  rw [hs, Nat.add_sub_cancel]

theorem evenSquared_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X : K[X]) * (evenSquared p).derivative =
      C (1 / 2 : K) * (1 - X ^ ((p - 1) / 2)) := by
  have hg := geometricP_source ((p - 1) / 2) (1 : K)
  simp only [map_one, one_mul] at hg
  rw [evenSquared_derivative p hp]
  linear_combination C (1 / 2 : K) * hg

theorem LV_geometric_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - V : K[X]) * (LV p).derivative =
      C (1 / 2 : K) * (1 - V ^ ((p - 1) / 2)) * V.derivative := by
  have he := congrArg (fun Q : K[X] => Q.comp V)
    (evenSquared_cleared_source (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, X_comp, C_comp, pow_comp] at he
  rw [LV, derivative_add, derivative_C, zero_add, derivative_comp]
  linear_combination V.derivative * he

theorem V_numerator (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (125 : K[X]) * V = (X + 1) * (4 * X - 11) ^ 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc5 : (5 : K[X]) * C (5 : K)⁻¹ = 1 := by
    change C (5 : K) * C (5 : K)⁻¹ = 1
    rw [← C_mul, mul_inv_cancel₀ h5, C_1]
  have hc3 : (125 : K[X]) * (C (5 : K)⁻¹) ^ 3 = 1 := by
    have he := congrArg (fun z : K[X] => z ^ 3) hc5
    simpa only [mul_pow, show (5 : K[X]) ^ 3 = 125 by norm_num, one_pow] using he
  unfold V squaredCoordinate
  linear_combination (X + 1) * (4 * X - 11) ^ 2 * hc3

theorem V_norm (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (125 : K[X]) * (1 - V) = (4 - X) * (4 * X - 1) ^ 2 := by
  linear_combination -V_numerator (K := K) p hp

theorem V_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (125 : K[X]) * V.derivative = 3 * (4 * X - 11) * (4 * X - 1) := by
  have he := congrArg (fun Q : K[X] => Q.derivative) (V_numerator (K := K) p hp)
  simp only [derivative_mul, derivative_ofNat, zero_mul, zero_add, derivative_add,
    derivative_one, derivative_X, add_zero, derivative_pow, derivative_sub,
    mul_one, sub_zero, Nat.cast_ofNat, map_ofNat,
    show 2 - 1 = 1 by omega, pow_one] at he
  linear_combination he

theorem V_half_power (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 * X - 11 : K[X]) * V ^ ((p - 1) / 2) =
      squaredCoordinate ^ ((p - 1) / 2) * (4 * X ^ p - 11) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h5p : (5 : K) ^ p = 5 := WPFiniteField.natCast_pow_char p 5
  have h5N : (5 : K) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ h5
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), h5p, one_mul]
  have hci : (C (5 : K)⁻¹ : K[X]) ^ (2 * ((p - 1) / 2)) = 1 := by
    rw [show 2 * ((p - 1) / 2) = p - 1 by have := half_exponent p hp; omega,
      ← map_pow, inv_pow, h5N, inv_one, C_1]
  have hnum (n : ℕ) : (C (n : K) : K[X]) ^ p = C (n : K) := by
    rw [← map_pow, WPFiniteField.natCast_pow_char p n]
  have hb : (4 * X - 11 : K[X]) ^ p = 4 * X ^ p - 11 := by
    have h4pow : (4 : K[X]) ^ p = 4 := by simpa only [Nat.cast_ofNat, map_ofNat] using hnum 4
    have h11pow : (11 : K[X]) ^ p = 11 := by simpa only [Nat.cast_ofNat, map_ofNat] using hnum 11
    rw [sub_pow_char, mul_pow, h4pow, h11pow]
  unfold V
  rw [mul_pow, ← pow_mul, mul_pow, hci, one_mul]
  calc
    _ = squaredCoordinate ^ ((p - 1) / 2) * (4 * X - 11) ^ p := by
      have he : (4 * X - 11 : K[X]) ^ (2 * ((p - 1) / 2)) * (4 * X - 11) =
          (4 * X - 11) ^ p := by rw [← pow_succ, ← half_exponent p hp]
      linear_combination squaredCoordinate ^ ((p - 1) / 2) * he
    _ = _ := by rw [hb]

theorem LV_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) * (LV p).derivative =
      C (3 / 2 : K) * ((4 * X - 11) - squaredCoordinate ^ ((p - 1) / 2) * (4 * X ^ p - 11)) := by
  have hn : (4 * X - 1 : K[X]) ≠ 0 := by
    intro he
    have hc := congrArg (fun Q : K[X] => Q.coeff 1) he
    simp at hc
    norm_num [coeff_one] at hc
    exact WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
      (by simpa only [Nat.cast_ofNat] using hc)
  apply mul_right_cancel₀ hn
  have hgeom := LV_geometric_source (K := K) p hp
  have hnorm := V_norm (K := K) p hp
  have hder := V_derivative (K := K) p hp
  have hhalf := V_half_power (K := K) p hp
  simp only [div_eq_mul_inv, map_mul, map_ofNat, map_one] at hgeom ⊢
  linear_combination
    125 * hgeom - (LV p).derivative * hnorm +
      C (2 : K)⁻¹ * (1 - V ^ ((p - 1) / 2)) * hder -
      3 * C (2 : K)⁻¹ * (4 * X - 1) * hhalf

noncomputable def sourceRemainder (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K[X] :=
  X ^ p * LV p - 3 * Pnumerator p u

theorem epsilon_squaredCoordinate_power (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    C (epsilon p) * (squaredCoordinate : K[X]) ^ ((p - 1) / 2) =
      (X + 1) ^ ((p - 1) / 2) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  rw [squaredCoordinate, mul_pow, epsilon, map_pow]
  have hunit : C (5 : K) * C (5 : K)⁻¹ = (1 : K[X]) := by
    rw [← C_mul, mul_inv_cancel₀ h5, C_1]
  rw [← mul_assoc, ← mul_pow, hunit, one_pow, one_mul]

/-- The entire cleared derivative of x^p(L_V-3P), retaining the negative phase. -/
theorem sourceRemainder_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (4 - X : K[X]) * (4 * X - 1) * (sourceRemainder p u).derivative =
      C (3 / 2 : K) * (X ^ p * (4 * X - 11) -
        6 * X ^ p * squaredCoordinate ^ ((p - 1) / 2) +
        4 * squaredCoordinate ^ ((p - 1) / 2)) +
      C (3 / 2 : K) * (4 - X) * (4 * X - 1) * X ^ (p - 1) := by
  have heps : epsilon p ≠ (0 : K) := by
    exact pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hunit : C (1 / (2 * epsilon p) : K) * C (epsilon p) = C (1 / 2 : K) := by
    rw [← C_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
    calc
      (epsilon p)⁻¹ * (2 : K)⁻¹ * epsilon p = (2 : K)⁻¹ * ((epsilon p)⁻¹ * epsilon p) := by ring
      _ = _ := by rw [inv_mul_cancel₀ heps, mul_one]
  have hxp2 : (X : K[X]) ^ (2 * p) = X ^ p * X ^ p := by
    rw [← pow_add]
    congr 1
    omega
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hdXp : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, hp0, map_zero, zero_mul]
  have hlv := LV_cleared_source (K := K) p hp
  have hpnum := Pnumerator_cleared_source (K := K) p hp u
  have hs := epsilon_squaredCoordinate_power (K := K) p hp
  have hc3 : C (3 / 2 : K) = 3 * C (1 / 2 : K) := by
    simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  rw [hc3] at hlv ⊢
  simp only [sourceRemainder, derivative_sub, derivative_mul, hdXp, derivative_ofNat,
    zero_mul, zero_add]
  linear_combination X ^ p * hlv - 3 * hpnum +
    3 * C (1 / (2 * epsilon p)) * (17 * X ^ p - 4 * X ^ (2 * p) - 4) * hs -
    3 * (17 * X ^ p - 4 * X ^ (2 * p) - 4) * squaredCoordinate ^ ((p - 1) / 2) * hunit +
    12 * C (1 / 2 : K) * squaredCoordinate ^ ((p - 1) / 2) * hxp2

end WPFiniteLVSource
