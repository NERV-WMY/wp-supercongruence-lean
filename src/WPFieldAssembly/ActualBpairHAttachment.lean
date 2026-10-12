import WPFieldAssembly.ActualBpairTriangles
import WPFieldAssembly.ActualKwFiniteHBridge

open scoped BigOperators Polynomial
open Polynomial

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The literal SB72 primitive has exactly the original moving even source. -/
theorem Dstar_moving_even_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -C (3 : K) * Dstar p =
      (WPFiniteWSource.deltaE p : K[X]).comp WPFiniteWSource.squaredCoordinate := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : C (3 : K) * C (1 / 3 : K) = (1 : K[X]) := by
    rw [← map_mul, mul_one_div_cancel h3, map_one]
  unfold Dstar
  linear_combination ((WPFiniteWSource.deltaE p : K[X]).comp
    WPFiniteWSource.squaredCoordinate) * hc

/-- Degree and the genuine source identify the entire half-cutoff primitive. -/
theorem branchHPolynomial_full_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    branchHPolynomial p z = ActualKwFiniteHBridge.HPrimitive ((p - 1) / 2)
      (fun n => ((WPFiniteWSource.deltaE p : K[X]).comp
        WPFiniteWSource.squaredCoordinate).coeff n) z := by
  let N := (p - 1) / 2
  let E : K[X] := (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate
  let Q : K[X] := ActualKwFiniteHBridge.HPrimitive N (fun n => E.coeff n) z
  have hN : N < p := by dsimp only [N]; omega
  have hE : E.natDegree ≤ N := ActualKwFiniteHBridge.movingEven_degree p
  have hQ : Q.natDegree < p :=
    (ActualKwFiniteHBridge.HPrimitive_degree N _ z).trans_lt hN
  have hQ0 : Q.eval 0 = 0 := ActualKwFiniteHBridge.HPrimitive_eval_zero N _ z
  have he : (-C (3 : K) * Dstar p : K[X]) = E := Dstar_moving_even_source p hp
  have hs := ActualKwFiniteHBridge.HPrimitive_polynomial_derivative p N hN E hE z
  change (X - C z) * Q.derivative = E - C (E.eval z) at hs
  rw [← he] at hs
  exact (branchHPolynomial_unique p hp z Q hQ hQ0 hs).symm

/-- The finite triangle uses the same four ordered D_N values, for every pair of points. -/
theorem branchH_movingH (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z w : K) :
    branchH p z w = ActualKwFiniteHBridge.movingH p z w := by
  rw [← branchHPolynomial_eval, branchHPolynomial_full_primitive p hp,
    ActualKwFiniteHBridge.HPrimitive_eval]
  exact ActualKwFiniteHBridge.finiteH_movingEven_D p hp z w

theorem branchH_ordered_D (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z w : K) :
    branchH p z w =
      (WPFiniteLoop.D ((p - 1) / 2) ((4 / 5 : K) * (1 + w)) ((4 / 5 : K) * (1 + z)) -
        WPFiniteLoop.D ((p - 1) / 2) (4 / 5 : K) ((4 / 5 : K) * (1 + z)) -
          WPFiniteLoop.D ((p - 1) / 2) ((1 / 5 : K) * (1 + w)) ((1 / 5 : K) * (1 + z)) +
            WPFiniteLoop.D ((p - 1) / 2) (1 / 5 : K) ((1 / 5 : K) * (1 + z))) / 2 := by
  exact branchH_movingH p hp z w

/-- Both fixed rational brackets retain the original lower endpoint terms. -/
theorem branchH_quarter_ordered_D (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (w : K) :
    branchH p (1 / 4) w =
      (WPFiniteLoop.D ((p - 1) / 2) ((4 / 5 : K) * (1 + w)) 1 -
        WPFiniteLoop.D ((p - 1) / 2) (4 / 5 : K) 1 -
          WPFiniteLoop.D ((p - 1) / 2) ((1 / 5 : K) * (1 + w)) (1 / 4) +
            WPFiniteLoop.D ((p - 1) / 2) (1 / 5 : K) (1 / 4)) / 2 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hsum : (1 + 1 / 4 : K) = 5 / 4 := by
    apply (eq_div_iff h4).mpr
    linear_combination (mul_one_div_cancel h4)
  have hb : (4 / 5 : K) * (1 + 1 / 4) = 1 := by
    rw [hsum]
    calc
      _ = ((5 : K)⁻¹ * 5) * (4 * (4 : K)⁻¹) := by
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [inv_mul_cancel₀ h5, mul_inv_cancel₀ h4, one_mul]
  have ha : (1 / 5 : K) * (1 + 1 / 4) = 1 / 4 := by
    rw [hsum]
    simp only [div_eq_mul_inv, one_mul]
    calc
      _ = ((5 : K)⁻¹ * 5) * (4 : K)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ h5, one_mul]
  rw [branchH_ordered_D p hp, hb, ha]

theorem branchH_four_ordered_D (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (w : K) :
    branchH p 4 w =
      (WPFiniteLoop.D ((p - 1) / 2) ((4 / 5 : K) * (1 + w)) 4 -
        WPFiniteLoop.D ((p - 1) / 2) (4 / 5 : K) 4 -
          WPFiniteLoop.D ((p - 1) / 2) ((1 / 5 : K) * (1 + w)) 1 +
            WPFiniteLoop.D ((p - 1) / 2) (1 / 5 : K) 1) / 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hsum : (1 + 4 : K) = 5 := by ring
  have hb : (4 / 5 : K) * (1 + 4) = 4 := by rw [hsum, div_mul_cancel₀ _ h5]
  have ha : (1 / 5 : K) * (1 + 4) = 1 := by rw [hsum, div_mul_cancel₀ _ h5]
  rw [branchH_ordered_D p hp, hb, ha]

end WPFieldAssembly.ActualBpairContraction
