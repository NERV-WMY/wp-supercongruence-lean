import WPFiniteProductTail

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPFiniteAffineLog WPFiniteProductTail
open LaurentPolynomial (T)

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- The original full logarithm ell(x/c), with cutoff p-1. -/
noncomputable def lowHLog (p : ℕ) (c : K) : K[X] :=
  (LP p).comp (C c⁻¹ * X)

/-- The literal unit-pivot integral of R from zero to X. -/
noncomputable def lowHIntegralP (p : ℕ) (R : K[X]) : K[X] :=
  unitPrimitiveP p (X * R) 0

theorem lowHIntegralP_eval (p : ℕ) (R : K[X]) (c : K) :
    (lowHIntegralP p R).eval c = originPrimitive p (X * R) c := by
  rw [lowHIntegralP, unitPrimitiveP_eval, unitPrimitive_origin]

theorem lowHIntegralP_zero (p : ℕ) (R : K[X]) :
    (lowHIntegralP p R).eval 0 = 0 := unitPrimitiveP_zero p _ 0

theorem lowHIntegralP_degree (p : ℕ) (R : K[X]) :
    (lowHIntegralP p R).natDegree ≤ p - 1 := unitPrimitiveP_degree p _ 0

private theorem lowH_X_mul_degree (p : ℕ) (hp : 19 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 1) : (X * R).natDegree < p := by
  have hm : (X * R).natDegree ≤ 1 + R.natDegree := by
    simpa only [natDegree_X] using (natDegree_mul_le (p := (X : K[X])) (q := R))
  omega

theorem lowHIntegralP_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) :
    (lowHIntegralP p R).derivative = R := by
  apply mul_left_cancel₀ (X_ne_zero (R := K))
  exact originPrimitiveP_source p (X * R) (lowH_X_mul_degree p hp R hR) (by simp)

private theorem lowH_originPrimitive_remove_zero (p : ℕ) (R : K[X]) (c : K) :
    originPrimitive p (R - C (R.coeff 0)) c = originPrimitive p R c := by
  unfold originPrimitive
  apply Finset.sum_congr rfl
  intro i hi
  have hi0 : i ≠ 0 := by have := (Finset.mem_Ico.mp hi).1; omega
  rw [coeff_sub, coeff_C, if_neg hi0, sub_zero]

private theorem lowH_full_log_diagonal_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (hW0 : W.coeff 0 = 0) (c : K) (hc : c ≠ 0) :
    (W * (LP p).comp (C c * X)).coeff p =
      -(c ^ p) * originPrimitive p W c⁻¹ := by
  classical
  conv_lhs => rw [W_full_cutoff p W hW hW0]
  simp only [Finset.sum_mul, finsetSum_coeff]
  unfold originPrimitive
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega : i ≤ p),
    LP_scaled_coeff, if_pos (by omega : 1 ≤ p - i ∧ p - i < p)]
  have hpower : c ^ (p - i) * c ^ i = c ^ p := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : i ≤ p)]
  have hquot : c ^ (p - i) = c ^ p / c ^ i :=
    (eq_div_iff (pow_ne_zero i hc)).mpr hpower
  rw [hquot]
  simp only [div_eq_mul_inv, inv_pow]
  rw [reversed_unit p i hi]
  ring

/-- The actual p diagonal is retained, including the original reversed log index. -/
theorem lowH_full_log_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p) (c : K) (hc : c ≠ 0) :
    (R * (LP p).comp (C c * X)).coeff p =
      -(c ^ p) * originPrimitive p R c⁻¹ := by
  let W := R - C (R.coeff 0)
  have hW : W.natDegree < p := by
    exact (natDegree_sub_le _ _).trans_lt (max_lt hR (by simpa using (by omega : 0 < p)))
  have hW0 : W.coeff 0 = 0 := by simp only [W, coeff_sub, coeff_C, if_true, sub_self]
  have he : R = C (R.coeff 0) + W := by dsimp only [W]; ring
  conv_lhs => rw [he]
  rw [add_mul, coeff_add, coeff_C_mul, LP_scaled_coeff,
    if_neg (by omega : ¬(1 ≤ p ∧ p < p)), mul_zero, zero_add,
    lowH_full_log_diagonal_zero p W hW hW0 c hc]
  rw [lowH_originPrimitive_remove_zero]

theorem lowHLog_zero (p : ℕ) (c : K) : (lowHLog p c).coeff 0 = 0 := by
  rw [lowHLog, LP_scaled_coeff, if_neg (by omega)]

theorem lowHLog_degree (p : ℕ) (c : K) : (lowHLog p c).natDegree ≤ p - 1 := by
  have hx : (C c⁻¹ * (X : K[X])).natDegree ≤ 1 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul (LP_natDegree_le (K := K) p) hx)

/-- The general endpoint still carries c^(-p), before any rational endpoint reduction. -/
theorem lowHLog_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p) (c : K) (hc : c ≠ 0) :
    (lowHLog p c * R).coeff p = -(c⁻¹ ^ p) * originPrimitive p R c := by
  rw [mul_comm, lowHLog, lowH_full_log_diagonal p hp R hR c⁻¹ (inv_ne_zero hc), inv_inv]

/-- The complete coefficient at p-1 is the literal unit integral, with its origin retained. -/
theorem lowH_log_green_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c : K) (hc : c ≠ 0) :
    (lowHLog p c * R).coeff (p - 1) = -(c⁻¹ ^ p) * (lowHIntegralP p R).eval c := by
  have he := lowHLog_diagonal p hp (X * R) (lowH_X_mul_degree p hp R hR) c hc
  have hcoeff : (lowHLog p c * (X * R)).coeff p = (lowHLog p c * R).coeff (p - 1) := by
    rw [show lowHLog p c * (X * R) = X * (lowHLog p c * R) by ring]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using
      (coeff_X_mul (lowHLog p c * R) (p - 1))
  rw [hcoeff, ← lowHIntegralP_eval] at he
  exact he

private theorem lowH_LP_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (1 - X : K[X]) * (LP p).derivative = 1 - X ^ (p - 1) := by
  have hm : (1 - X : K[X]) ^ p = 1 - X ^ p := by rw [sub_pow_char (p := p), one_pow]
  have hmp : (1 - X : K[X]) ^ p = (1 - X) ^ (p - 1) * (1 - X) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hxp : (X : K[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  rw [LP_derivative_closed_eq]
  linear_combination hm - hmp + hxp

private theorem lowH_fixed_pred_power (p : ℕ) (hp : 19 ≤ p) (c : K)
    (hc : c ≠ 0) (hcp : c ^ p = c) : c ^ (p - 1) = 1 := by
  apply mul_right_cancel₀ hc
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  exact hcp

/-- The actual full-cutoff derivative is cleared before division by x or x-c. -/
theorem lowHLog_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c : K) (hc : c ≠ 0) (hcp : c ^ p = c) :
    (X - C c) * (lowHLog p c).derivative = X ^ (p - 1) - 1 := by
  let U : K[X] := C c⁻¹ * X
  have hs := congrArg (fun F : K[X] => F.comp U) (lowH_LP_cleared_source (K := K) p hp)
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp] at hs
  have hpower : (C c⁻¹ : K[X]) ^ (p - 1) = 1 := by
    rw [← map_pow, inv_pow, lowH_fixed_pred_power p hp c hc hcp, inv_one, map_one]
  dsimp only [U] at hs
  rw [mul_pow, hpower, one_mul] at hs
  have hunit : C c * C c⁻¹ = (1 : K[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hd : (lowHLog p c).derivative = (LP p).derivative.comp U * C c⁻¹ := by
    rw [lowHLog, derivative_comp]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X, mul_one]
    dsimp only [U]
    ring
  rw [hd]
  linear_combination -hs - ((LP p : K[X]).derivative.comp U) * hunit

/-- The original y*ell(x/c)*dell(x/d), with y=(x-d)R. -/
noncomputable def lowHGreenProduct (p : ℕ) (R : K[X]) (c d : K) : K[X] :=
  lowHLog p c * ((X - C d) * R) * (lowHLog p d).derivative

theorem lowHGreenProduct_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (c d : K) (hd : d ≠ 0) (hdp : d ^ p = d) :
    lowHGreenProduct p R c d = (X ^ (p - 1) - 1) * (lowHLog p c * R) := by
  unfold lowHGreenProduct
  calc
    _ = (lowHLog p c * R) * ((X - C d) * (lowHLog p d).derivative) := by ring
    _ = _ := by rw [lowHLog_cleared_source p hp d hd hdp]; ring

/-- All phases use the same original coefficients; no finite-log index is reset. -/
theorem lowHGreen_band (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (k : ℕ) (hk : 1 ≤ k) (R : K[X]) (c d : K)
    (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-((k * p : ℕ) : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) =
      (lowHLog p c * R).coeff ((k - 1) * p) - (lowHLog p c * R).coeff (k * p - 1) := by
  have hkp : k * p = (k - 1) * p + p := by
    calc
      _ = ((k - 1) + 1) * p := by rw [Nat.sub_add_cancel hk]
      _ = _ := by ring
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-((k * p : ℕ) : ℤ)) (-1)
    (lowHGreenProduct p R c d).toLaurent
  simp only [map_one, one_mul] at hs
  rw [hs, show (-1 : ℤ) - -((k * p : ℕ) : ℤ) = ((k * p - 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat, lowHGreenProduct_source p hp R c d hd hdp,
    sub_mul, one_mul, coeff_sub, coeff_X_pow_mul', if_pos (by omega : p - 1 ≤ k * p - 1),
    show k * p - 1 - (p - 1) = (k - 1) * p by omega]

private theorem lowH_log_product_origin (p : ℕ) (R : K[X]) (c : K) :
    (lowHLog p c * R).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_mul, ← coeff_zero_eq_eval_zero, lowHLog_zero, zero_mul]

/-- Every coefficient at and above 2p-1 is excluded by the full polynomial bound. -/
theorem lowH_log_product_upper_zero (p : ℕ) (hp : 19 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 1) (c : K) (n : ℕ) (hn : 2 * p - 1 ≤ n) :
    (lowHLog p c * R).coeff n = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have hmul : (lowHLog p c * R).natDegree ≤ (lowHLog p c).natDegree + R.natDegree :=
    natDegree_mul_le
  have hlog := lowHLog_degree p c
  omega

/-- The first original phase is the complete ordinary endpoint integral. -/
theorem lowH_log_green_first (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c d : K)
    (hc : c ≠ 0) (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-(p : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) =
      (c⁻¹ ^ p) * (lowHIntegralP p R).eval c := by
  have h := lowHGreen_band p hp 1 (by omega) R c d hd hdp
  simp only [Nat.one_mul, Nat.sub_self, Nat.zero_mul, lowH_log_product_origin, zero_sub] at h
  rw [h, lowH_log_green_coefficient p hp R hR c hc]
  ring

/-- The second phase keeps the entire origin-subtracted dx/x integral. -/
theorem lowH_log_green_second (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c d : K)
    (hc : c ≠ 0) (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-((2 * p : ℕ) : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) =
      -(c⁻¹ ^ p) * originPrimitive p R c := by
  rw [lowHGreen_band p hp 2 (by omega) R c d hd hdp]
  simp only [show 2 - 1 = (1 : ℕ) by omega, Nat.one_mul]
  rw [lowH_log_product_upper_zero p hp R hR c (2 * p - 1) le_rfl, sub_zero,
    lowHLog_diagonal p hp R (by omega) c hc]

/-- The third phase vanishes from the strict degree bound, without deleting a source band. -/
theorem lowH_log_green_third (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c d : K)
    (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-((3 * p : ℕ) : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) = 0 := by
  rw [lowHGreen_band p hp 3 (by omega) R c d hd hdp]
  simp only [show 3 - 1 = (2 : ℕ) by omega]
  rw [lowH_log_product_upper_zero p hp R hR c (2 * p) (by omega),
    lowH_log_product_upper_zero p hp R hR c (3 * p - 1) (by omega), sub_self]

theorem lowH_log_green_first_fixed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c d : K)
    (hc : c ≠ 0) (hcp : c ^ p = c) (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-(p : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) =
      c⁻¹ * (lowHIntegralP p R).eval c := by
  rw [lowH_log_green_first p hp R hR c d hc hd hdp, inv_pow, hcp]

theorem lowH_log_green_second_fixed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (R : K[X]) (hR : R.natDegree < p - 1) (c d : K)
    (hc : c ≠ 0) (hcp : c ^ p = c) (hd : d ≠ 0) (hdp : d ^ p = d) :
    (T (-((2 * p : ℕ) : ℤ)) * (lowHGreenProduct p R c d).toLaurent).coeff (-1) =
      -c⁻¹ * originPrimitive p R c := by
  rw [lowH_log_green_second p hp R hR c d hc hd hdp, inv_pow, hcp]

end WPFieldAssembly.ActualBpairContraction
