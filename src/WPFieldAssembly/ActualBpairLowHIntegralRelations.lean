import WPFieldAssembly.ActualBpairLowHEndpoints

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFiniteNC122Residue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

/-- The whole branch quotients retain the actual cubic factor and H(q)/q source. -/
noncomputable def lowHBranchAQuotient (H : K[X]) : K[X] :=
  -C (16 / 125 : K) * (X - C 4) * (X - C (1 / 4)) * H.divX.comp VP

noncomputable def lowHBranchBQuotient (H : K[X]) : K[X] :=
  -C (16 / 125 : K) * (X - C (1 / 4)) ^ 2 * H.divX.comp VP

theorem lowHCubicV_branch_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (VP : K[X]) = -C (16 / 125 : K) * (X - C 4) * (X - C (1 / 4)) ^ 2 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (C : K →+* K[X]) (mul_one_div_cancel h4)
  simp only [map_mul, map_ofNat, map_one] at hc
  have ha : (4 : K[X]) * (X - C (1 / 4 : K)) = 4 * X - 1 := by
    linear_combination -hc
  rw [VP, ← ha]
  simp only [div_eq_mul_inv, map_mul, map_ofNat]
  ring

/-- These are both genuine proper-end quotients of the full y=H(V), not imposed endpoint values. -/
theorem lowHBranchQuotients_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHCubicY H = (X - C (1 / 4)) * lowHBranchAQuotient H ∧
      lowHCubicY H = (X - C 4) * lowHBranchBQuotient H := by
  unfold lowHBranchAQuotient lowHBranchBQuotient
  rw [lowHCubicY_source H h0, lowHCubicV_branch_factor p hp]
  constructor <;> ring

theorem lowHqCubicDensity_branch_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) : lowHqCubicDensity H = 2 * lowHBranchAQuotient H + lowHBranchBQuotient H := by
  have he := congrArg Polynomial.derivative (lowHCubicV_branch_factor (K := K) p hp)
  simp only [derivative_mul, derivative_neg, derivative_C, neg_zero, zero_mul, zero_add,
    derivative_sub, derivative_X, sub_zero, derivative_pow, Nat.cast_ofNat, C_ofNat,
    Nat.reduceSub, pow_one, mul_one, derivative_ofNat] at he
  unfold lowHqCubicDensity lowHBranchAQuotient lowHBranchBQuotient
  rw [he]
  simp only [map_ofNat]
  ring

/-- This is the full polynomial J_Q source after its original origin simple pole is separated. -/
noncomputable def lowHJQDensity (H : K[X]) : K[X] :=
  lowHBranchAQuotient H + 2 * lowHBranchBQuotient H - 3 * (lowHCubicY H).divX

noncomputable def lowHRegularBranchDensity (H : K[X]) : K[X] :=
  C (1 / 15 : K) * (lowHBranchAQuotient H - lowHBranchBQuotient H)

/-- The entire reciprocal/log source keeps the original origin subtraction. -/
theorem lowH_auxiliary_density_identity (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) :
    lowHJQDensity H + 15 * lowHRegularBranchDensity H =
      lowHqCubicDensity H - 3 * (lowHCubicY H).divX := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have hc := congrArg (C : K →+* K[X]) (mul_one_div_cancel h15)
  simp only [map_mul, map_ofNat, map_one] at hc
  rw [lowHqCubicDensity_branch_source p hp]
  unfold lowHJQDensity lowHRegularBranchDensity
  linear_combination (lowHBranchAQuotient H - lowHBranchBQuotient H) * hc

/-- The auxiliary dx/x primitive still contains all original positive coefficients. -/
theorem lowH_auxiliary_origin_integral (p : ℕ) (H : K[X]) (c : K) :
    (lowHIntegralP p (lowHCubicY H).divX).eval c = originPrimitive p (lowHCubicY H) c := by
  rw [lowHIntegralP_eval]
  have hx : X * (lowHCubicY H).divX = lowHCubicY H - C ((lowHCubicY H).coeff 0) := by
    linear_combination X_mul_divX_add (lowHCubicY H)
  rw [hx]
  unfold originPrimitive
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := Finset.mem_Ico.mp hn; omega
  rw [coeff_sub, coeff_C, if_neg hn0, sub_zero]

theorem lowHIntegralP_sub_C_mul (p : ℕ) (a : K) (F G : K[X]) :
    lowHIntegralP p (F - C a * G) = lowHIntegralP p F - C a * lowHIntegralP p G := by
  have hx : X * (F - C a * G) = X * F - C a * (X * G) := by ring
  unfold lowHIntegralP
  rw [hx]
  simp only [unitPrimitiveP, coeff_sub, coeff_C_mul, map_sub, map_mul, sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The whole middle density cancels both auxiliary functions at each original endpoint. -/
theorem lowH_auxiliary_whole_integral (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) (c : K) :
    (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval c =
      (lowHqPrimitive p H).eval (VP.eval c) - (lowHqPrimitive p H).eval (VP.eval 0) -
        3 * originPrimitive p (lowHCubicY H) c := by
  rw [lowH_auxiliary_density_identity p hp]
  change (lowHIntegralP p (lowHqCubicDensity H - C (3 : K) * (lowHCubicY H).divX)).eval c = _
  rw [lowHIntegralP_sub_C_mul, eval_sub, eval_mul, eval_C,
    lowHqCubicDensity_integral p hp d hd hband H hH h0, lowH_auxiliary_origin_integral]

theorem lowH_auxiliary_both_end_integrals (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) :
    (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval (1 / 4) =
        -(lowHqPrimitive p H).eval (VP.eval 0) - 3 * originPrimitive p (lowHCubicY H) (1 / 4) ∧
      (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval 4 =
        -(lowHqPrimitive p H).eval (VP.eval 0) - 3 * originPrimitive p (lowHCubicY H) 4 := by
  have hz : (lowHqPrimitive p H).eval 0 = 0 := unitPrimitiveP_zero p H 0
  simp only [lowH_auxiliary_whole_integral p hp d hd hband H hH h0,
    lowHCubicV_quarter p hp, lowHCubicV_four, hz, zero_sub, and_self]

theorem lowHIntegralP_add_C_mul (p : ℕ) (a : K) (F G : K[X]) :
    lowHIntegralP p (F + C a * G) = lowHIntegralP p F + C a * lowHIntegralP p G := by
  have he := lowHIntegralP_sub_C_mul p (-a) F G
  simpa only [map_neg, neg_mul, sub_neg_eq_add] using he

/-- The two original endpoints cancel together; neither auxiliary integral has a prescribed value. -/
theorem lowH_auxiliary_middle_contraction (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) :
    (2 / 45 : K) * ((1 / 4) * (lowHIntegralP p (lowHJQDensity H)).eval 4 -
        4 * (lowHIntegralP p (lowHJQDensity H)).eval (1 / 4)) +
      (2 / 3 : K) * ((1 / 4) * (lowHIntegralP p (lowHRegularBranchDensity H)).eval 4 -
        4 * (lowHIntegralP p (lowHRegularBranchDensity H)).eval (1 / 4)) =
      (1 / 6 : K) * (lowHqPrimitive p H).eval (VP.eval 0) -
        (2 / 15 : K) * ((1 / 4) * originPrimitive p (lowHCubicY H) 4 -
          4 * originPrimitive p (lowHCubicY H) (1 / 4)) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; ring
  have h45 : (45 : K) ≠ 0 := by convert mul_ne_zero (pow_ne_zero 2 h3) h5 using 1; ring
  have h60 : (60 : K) ≠ 0 := by convert mul_ne_zero (mul_ne_zero h4 h3) h5 using 1; ring
  have h180 : (180 : K) ≠ 0 := by convert mul_ne_zero h4 h45 using 1; ring
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have he := lowH_auxiliary_both_end_integrals p hp d hd hband H hH h0
  have hlin (c : K) :
      (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval c =
        (lowHIntegralP p (lowHJQDensity H)).eval c +
          15 * (lowHIntegralP p (lowHRegularBranchDensity H)).eval c := by
    change (lowHIntegralP p (lowHJQDensity H + C (15 : K) * lowHRegularBranchDensity H)).eval c = _
    rw [lowHIntegralP_add_C_mul, eval_add, eval_mul, eval_C]
  calc
    _ = (2 / 45 : K) * ((1 / 4) *
        (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval 4 -
        4 * (lowHIntegralP p (lowHJQDensity H + 15 * lowHRegularBranchDensity H)).eval (1 / 4)) := by
      rw [hlin, hlin]
      field_simp [h4, h3, h45, h180]
      ring
    _ = _ := by
      rw [he.1, he.2]
      field_simp [h4, h6, h15, h60, h180]
      ring

end WPFieldAssembly.ActualBpairContraction

