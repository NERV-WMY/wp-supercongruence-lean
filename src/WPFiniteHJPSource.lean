import WPFiniteLVSource

open Polynomial

namespace WPFiniteHJPSource

open WPFiniteKSource WPFiniteJSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPFiniteWSource WPFiniteLVSource

variable {K : Type*} [Field K]

theorem JLP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (1 - X ^ 2 : K[X]) * (JLP p).derivative = LPsrc p := by
  rw [JLP_eq_harmonic p hp, JHP_cleared_derivative p hp]

/-- Genuine finite conic HJP source; this polynomial is distinct from native H_J. -/
theorem HJP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 - X : K[X]) * (4 * X - 1) * (HJP p).derivative =
      C (15 / 2 : K) * squaredCoordinate ^ ((p - 1) / 2) * LV p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have hunit : 2 * C (2 : K)⁻¹ = (1 : K[X]) := by
    change C (2 : K) * C (2 : K)⁻¹ = 1
    rw [← C_mul, mul_inv_cancel₀ h2, C_1]
  have hconicder : (conic : K[X]).derivative = 10 * X := by
    unfold conic
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X_pow,
      derivative_one, zero_mul, zero_add, sub_zero, Nat.cast_ofNat, map_ofNat,
      show 2 - 1 = 1 by omega, pow_one]
    ring
  have hTcder : (Tc : K[X]).derivative = 3 * (4 * X ^ 2 - 1) := by
    unfold Tc
    simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X_pow,
      derivative_X, zero_mul, zero_add, mul_one, Nat.cast_ofNat, map_ofNat,
      show 3 - 1 = 2 by omega]
    ring
  have hnorm : (1 - Tc ^ 2 : K[X]) = (1 - X ^ 2) * (4 * X ^ 2 - 1) ^ 2 := by
    unfold Tc
    ring
  have hAcomp : ((4 - X) * (4 * X - 1) : K[X]).comp conic =
      25 * (1 - X ^ 2) * (4 * X ^ 2 - 1) := by
    simp only [mul_comp, sub_comp, ofNat_comp, X_comp, one_comp, conic, Nat.cast_ofNat]
    ring
  have hScomp : (squaredCoordinate ^ ((p - 1) / 2) : K[X]).comp conic = X ^ (p - 1) := by
    rw [pow_comp, squaredCoordinate_conic p hp, ← pow_mul]
    congr 1
    have he := half_exponent p hp
    omega
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have hXpder : (X ^ p : K[X]).derivative = 0 := by
    rw [derivative_X_pow, hp0, map_zero, zero_mul]
  have hh := congrArg (fun Q : K[X] => Q.derivative) (HJP_conic_pullback (K := K) p hp)
  rw [derivative_comp, derivative_mul, hXpder, zero_mul, zero_add, hconicder] at hh
  have hj := congrArg (fun Q : K[X] => Q.comp Tc) (JLP_cleared_source (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp] at hj
  have hj' : (1 - X ^ 2 : K[X]) * (4 * X ^ 2 - 1) ^ 2 * ((JLP p).comp Tc).derivative =
      (LPsrc p).comp Tc * (3 * (4 * X ^ 2 - 1)) := by
    rw [derivative_comp, hTcder]
    rw [hnorm] at hj
    linear_combination (3 * (4 * X ^ 2 - 1)) * hj
  have hxpow : (X : K[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  let Q : K[X] := (4 - X) * (4 * X - 1) * (HJP p).derivative -
    C (15 / 2 : K) * squaredCoordinate ^ ((p - 1) / 2) * LV p
  have hQprod : Q.comp conic * (10 * X * (4 * X ^ 2 - 1)) = 0 := by
    dsimp only [Q]
    rw [sub_comp, mul_comp, hAcomp, mul_comp, mul_comp, C_comp, hScomp, LV_conic p hp]
    simp only [div_eq_mul_inv, map_mul, map_ofNat]
    linear_combination
      25 * (1 - X ^ 2) * (4 * X ^ 2 - 1) ^ 2 * hh + 25 * X ^ p * hj' -
      150 * C (2 : K)⁻¹ * (LPsrc p).comp Tc * (4 * X ^ 2 - 1) * hxpow -
      75 * X ^ p * (LPsrc p).comp Tc * (4 * X ^ 2 - 1) * hunit
  have hfactor : (10 * X * (4 * X ^ 2 - 1) : K[X]) ≠ 0 := by
    have htail : (4 * X ^ 2 - 1 : K[X]) ≠ 0 := by
      intro hz
      have he := congrArg (fun F : K[X] => F.coeff 0) hz
      norm_num [coeff_one] at he
    change (C (10 : K) * X * (4 * X ^ 2 - 1)) ≠ 0
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h10) X_ne_zero) htail
  have hQcomp : Q.comp conic = 0 := (mul_eq_zero.mp hQprod).resolve_right hfactor
  have hQ : Q = 0 := by
    rcases comp_eq_zero_iff.mp hQcomp with hz | ⟨_, hc⟩
    · exact hz
    · have hd : (conic : K[X]).natDegree = 2 := by
        unfold conic
        change (C (5 : K) * X ^ 2 - 1).natDegree = 2
        compute_degree
        exact h5
      have he := congrArg (fun F : K[X] => F.natDegree) hc
      rw [hd, natDegree_C] at he
      omega
  exact sub_eq_zero.mp hQ

end WPFiniteHJPSource
