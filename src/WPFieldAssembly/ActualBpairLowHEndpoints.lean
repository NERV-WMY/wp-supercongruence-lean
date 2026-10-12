import WPFieldAssembly.ActualBpairLowHEuler
import WPFiniteNC122Residue

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFiniteNC122Residue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The original auxiliary q integral, with no endpoint value assigned. -/
noncomputable def lowHqPrimitive (p : ℕ) (H : K[X]) : K[X] := unitPrimitiveP p H 0

noncomputable def lowHCubicY (H : K[X]) : K[X] := H.comp VP

noncomputable def lowHqCubicDensity (H : K[X]) : K[X] := H.divX.comp VP * VP.derivative

theorem lowHCubicV_degree : (VP : K[X]).natDegree ≤ 3 := by
  have h1 : (4 - (X : K[X])).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have h2 : (4 * (X : K[X]) - 1).natDegree ≤ 1 := by
    have hh : (4 * (X : K[X])).natDegree ≤ 1 := by
      change (Polynomial.C (4 : K) * X).natDegree ≤ 1
      exact (natDegree_C_mul_le _ _).trans (by simp)
    exact (natDegree_sub_le _ _).trans (max_le hh (by simp))
  have hs : ((4 * (X : K[X]) - 1) ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le.trans (by omega)
  have hm : ((4 - (X : K[X])) * (4 * X - 1) ^ 2).natDegree ≤ 3 :=
    natDegree_mul_le.trans (by omega)
  rw [VP, mul_assoc]
  exact (natDegree_C_mul_le _ _).trans hm

theorem lowHCubicV_four : (VP : K[X]).eval 4 = 0 := by
  simp only [VP, eval_mul, eval_C, eval_sub, eval_ofNat, eval_X, sub_self, mul_zero, zero_mul]

theorem lowHCubicV_quarter (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (VP : K[X]).eval (1 / 4) = 0 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hs : (4 : K) * (1 / 4) - 1 = 0 := by rw [mul_one_div_cancel h4, sub_self]
  simp only [VP, eval_mul, eval_C, eval_sub, eval_ofNat, eval_X, eval_pow, eval_one,
    hs, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem lowHCubicY_source (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHCubicY H = VP * H.divX.comp VP := by
  have he := congrArg (fun Q : K[X] => Q.comp VP) (X_mul_divX_add H)
  simp only [mul_comp, X_comp, h0, map_zero, add_zero] at he
  exact he.symm

theorem lowHCubicY_degree (d : ℕ) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHCubicY H).natDegree ≤ 3 * d := by
  exact natDegree_comp_le.trans (by
    have he := Nat.mul_le_mul hH (lowHCubicV_degree (K := K))
    simpa only [Nat.mul_comm] using he)

theorem lowHCubicY_both_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).eval (1 / 4) = 0 ∧ (lowHCubicY H).eval 4 = 0 := by
  have hz : H.eval 0 = 0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  simp only [lowHCubicY, eval_comp, lowHCubicV_quarter p hp, lowHCubicV_four, hz, and_self]

theorem lowHqPrimitive_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : K[X]) (hdeg : H.natDegree < p) (h0 : H.coeff 0 = 0) :
    (lowHqPrimitive p H).derivative = H.divX := by
  apply mul_left_cancel₀ (X_ne_zero (R := K))
  have he := X_mul_divX_add H
  rw [h0, map_zero, add_zero] at he
  rw [he]
  exact originPrimitiveP_source p H hdeg h0

theorem lowHqPrimitive_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) : (lowHqPrimitive p H).natDegree ≤ d := by
  have hJ : (lowHqPrimitive p H).natDegree < p := by
    change (unitPrimitiveP p H 0).natDegree < p
    have he := unitPrimitiveP_degree p H (0 : K)
    omega
  have hR : H.divX.natDegree ≤ d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have he := lowH_primitive_sharp_degree p _ _ hJ
    (lowHqPrimitive_derivative p H (by omega) h0) (d - 1) hR
  omega

theorem lowHqCubicDensity_degree (d : ℕ) (hd : 1 ≤ d) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHqCubicDensity H).natDegree ≤ 3 * d - 1 := by
  have hdiv : H.divX.natDegree ≤ d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have hc : (H.divX.comp (VP : K[X])).natDegree ≤ (d - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hdiv lowHCubicV_degree)
  have hdV : (VP : K[X]).derivative.natDegree ≤ 2 :=
    (natDegree_derivative_le _).trans (by have := lowHCubicV_degree (K := K); omega)
  have he : (lowHqCubicDensity H).natDegree ≤ (d - 1) * 3 + 2 :=
    natDegree_mul_le.trans (Nat.add_le_add hc hdV)
  omega

/-- This identifies the literal unit integral at every endpoint while retaining T_H(V(0)). -/
theorem lowHqCubicDensity_integral (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) (c : K) :
    (lowHIntegralP p (lowHqCubicDensity H)).eval c =
      (lowHqPrimitive p H).eval (VP.eval c) - (lowHqPrimitive p H).eval (VP.eval 0) := by
  let J : K[X] := (lowHqPrimitive p H).comp VP -
    Polynomial.C ((lowHqPrimitive p H).eval (VP.eval 0))
  have hT := lowHqPrimitive_degree p hp d hd (by omega) H hH h0
  have hJ : J.natDegree < p := by
    have hc : ((lowHqPrimitive p H).comp (VP : K[X])).natDegree ≤ d * 3 :=
      natDegree_comp_le.trans (Nat.mul_le_mul hT lowHCubicV_degree)
    exact (natDegree_sub_le _ _).trans_lt (max_lt (by omega) (by simpa using (by omega : 0 < p)))
  have hJ0 : J.eval 0 = 0 := by simp only [J, eval_sub, eval_comp, eval_C, sub_self]
  have hder : J.derivative = lowHqCubicDensity H := by
    rw [show J = (lowHqPrimitive p H).comp VP -
      Polynomial.C ((lowHqPrimitive p H).eval (VP.eval 0)) from rfl,
      derivative_sub, derivative_C, sub_zero, derivative_comp,
      lowHqPrimitive_derivative p H (by omega) h0]
    rw [lowHqCubicDensity]
    ring
  have hR : (lowHqCubicDensity H).natDegree < p - 1 := by
    have he := lowHqCubicDensity_degree d hd H hH
    omega
  have hz : (X * lowHqCubicDensity H).coeff 0 = 0 := by simp
  have hs : X * J.derivative = X * lowHqCubicDensity H := by rw [hder]
  have he := WPFinitePrimitiveTransport.originPrimitiveP_unique p (X * lowHqCubicDensity H)
    (by have hm : (X * lowHqCubicDensity H).natDegree ≤ 1 + (lowHqCubicDensity H).natDegree :=
          by simpa only [natDegree_X] using (natDegree_mul_le (p := (X : K[X])) (q := lowHqCubicDensity H))
        omega) hz J hJ hJ0 hs c
  rw [← lowHIntegralP_eval] at he
  rw [← he]
  simp only [J, eval_sub, eval_comp, eval_C]

/-- Both original branch integrals are the same unevaluated origin correction. -/
theorem lowHqCubicDensity_both_end_integrals (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (d : ℕ) (hd : 1 ≤ d) (hband : 6 * d < p) (H : K[X]) (hH : H.natDegree ≤ d)
    (h0 : H.coeff 0 = 0) :
    (lowHIntegralP p (lowHqCubicDensity H)).eval (1 / 4) =
        -(lowHqPrimitive p H).eval (VP.eval 0) ∧
      (lowHIntegralP p (lowHqCubicDensity H)).eval 4 =
        -(lowHqPrimitive p H).eval (VP.eval 0) := by
  have hz : (lowHqPrimitive p H).eval 0 = 0 := unitPrimitiveP_zero p H 0
  simp only [lowHqCubicDensity_integral p hp d hd hband H hH h0,
    lowHCubicV_quarter p hp, lowHCubicV_four, hz, zero_sub, and_self]

end WPFieldAssembly.ActualBpairContraction
