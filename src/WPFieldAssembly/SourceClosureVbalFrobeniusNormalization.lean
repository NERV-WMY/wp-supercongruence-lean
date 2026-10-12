import WPFiniteZSupport

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteAffineLog WPFiniteProductTail
  WPFiniteABSourceTail WPFiniteWSource WPFiniteJSource WPFiniteZSource WPFiniteZSupport

namespace WPFieldAssembly.SourceClosureVbalFrobeniusNormalization

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The original coefficient at p is the boundary omitted by the strict product tail. -/
theorem scaled_log_product_boundary (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0)
    (c : K) (hc : c ≠ 0) :
    (W * (LP p).comp (Polynomial.C c * X)).coeff p =
      -c^p * originPrimitive p W c⁻¹ := by
  conv_lhs => rw [W_full_cutoff p W hW h0]
  rw [Finset.sum_mul,finsetSum_coeff,originPrimitive,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_Ico.mp hi
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul',if_pos (by omega),LP_scaled_coeff,
    if_pos (by omega : 1 ≤ p-i ∧ p-i < p)]
  have hpow : c^(p-i)=c^p*(c⁻¹)^i := by
    rw [pow_sub₀ c hc (by omega),inv_pow]
  rw [hpow,div_eq_mul_inv,reversed_unit p i hi]
  simp only [div_eq_mul_inv]
  ring

/-- Both full logarithm rows contribute their actual coefficient-p endpoint window. -/
theorem original_logTrace_product_boundary (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (W : K[X]) (hW : W.natDegree < p) (h0 : W.coeff 0 = 0) :
    (W*logTrace p).coeff p = originPrimitive p W (1/4)-originPrimitive p W 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have he : W*logTrace p =
      Polynomial.C (-(1/4 : K))*(W*(LP p).comp (Polynomial.C 4*X))+
        Polynomial.C (4 : K)*(W*(LP p).comp (Polynomial.C (1/4)*X)) := by
    simp only [logTrace,map_neg]
    ring
  rw [he,coeff_add,coeff_C_mul,coeff_C_mul,
    scaled_log_product_boundary p W hW h0 4 h4,
    scaled_log_product_boundary p W hW h0 (1/4) (one_div_ne_zero h4),h4p,hap]
  simp only [one_div,inv_inv]
  field_simp [h4]
  ring

/-- The diagonal p row of A*B0 remains separate from its strict upper product tail. -/
theorem original_AB0_product_boundary (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (W : K[X]) (hW : W.natDegree ≤ (p-1)/2-1)
    (h0 : W.coeff 0=0) (u : K) :
    (A p W u*B0 p W u).coeff p =
      -4/(15*epsilon p)*(originPrimitive p W (1/4)-originPrimitive p W 4) := by
  have hWp : W.natDegree < p := by omega
  have hA : (A p W u).natDegree ≤ W.natDegree := by
    unfold A
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hB : (Bpoly p W u).natDegree ≤ W.natDegree := by
    unfold Bpoly
    exact (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hAB : (A p W u*Bpoly p W u).coeff p=0 :=
    coeff_eq_zero_of_natDegree_lt
      ((natDegree_mul_le.trans (Nat.add_le_add hA hB)).trans_lt (by omega))
  have hlog : (Polynomial.C (uSlot p u)*Polynomial.C (2/15 : K)*logTrace p).coeff p=0 := by
    rw [mul_assoc]
    apply coeff_eq_zero_of_natDegree_lt
    exact ((natDegree_C_mul_le _ _).trans
      ((natDegree_C_mul_le _ _).trans (logTrace_degree p))).trans_lt (by omega)
  have he : A p W u*B0 p W u = A p W u*Bpoly p W u+
      Polynomial.C (uSlot p u)*Polynomial.C (2/15 : K)*logTrace p-
        Polynomial.C (2/epsilon p)*Polynomial.C (2/15 : K)*(W*logTrace p) := by
    unfold A B0
    ring
  rw [he,coeff_sub,coeff_add,hAB,hlog,zero_add,zero_sub,
    mul_assoc,coeff_C_mul,coeff_C_mul,
    original_logTrace_product_boundary p hp W hWp h0]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The whole original two-Frobenius coefficient has its diagonal window and full J row. -/
theorem actual_finite_frobenius_boundary (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Z p u : K[T;T⁻¹]).coeff (2*(p : ℤ)) =
      -(uSlot p u)^2/2+
        4/(15*epsilon p)*(originPrimitive p (W p) (1/4)-originPrimitive p (W p) 4)-
          4*(HJP p : K[X]).coeff p/45 := by
  rw [actual_finite_original_2p p hp u,
    original_AB0_product_boundary p hp (W p) (W_degree p hp) (W_origin p) u]
  have hA0 : (A p (W p) u : K[X]).coeff 0=uSlot p u := by
    simp only [A,coeff_sub,coeff_C_zero,coeff_C_mul,W_origin,mul_zero,sub_zero]
  rw [hA0]
  ring

/-- The coefficient-p J row keeps every odd index through p-2. -/
theorem actual_J_full_odd_boundary (p : ℕ) :
    (HJP p : K[X]).coeff p =
      ∑ r ∈ Finset.range ((p-1)/2),
        (((WPFiniteNC122.q p+H r/2)/((2*r+1 : ℕ) : K))/(5 : K)^(2*r+1))*
          ((Polynomial.C (5 : K)⁻¹*(X+1))^((p-1)/2+r+1)*
            (4*X-11)^(2*r+1)).coeff p := by
  simp only [HJP,finsetSum_coeff,mul_assoc,coeff_C_mul]

end WPFieldAssembly.SourceClosureVbalFrobeniusNormalization
