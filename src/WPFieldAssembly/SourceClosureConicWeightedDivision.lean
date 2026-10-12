import WPFieldAssembly.ConicDivision

open scoped Polynomial
open Polynomial

namespace WPFieldAssembly.SourceClosureConicWeightedDivision

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- Proper Bezout division lowers a nonzero Wronskian weight by one. -/
theorem weighted_wronskian_division (A y m M : K[X]) (hy : y≠0)
    (k : K) (hk : k≠0)
    (hw : A*(y*m.derivative-y.derivative*m)=1-y^2)
    (hs : y*M.derivative-C k*y.derivative*M=0) :
    ∃ B : K[X], M=y*B ∧ y*B.derivative-C (k-1)*y.derivative*B=0 := by
  let B := M*(y+A*m.derivative)-C k⁻¹*A*m*M.derivative
  have hi : (C k⁻¹ : K[X])*C k=1 := by rw [←C_mul,inv_mul_cancel₀ hk,C_1]
  have hb : M=y*B := by
    dsimp only [B]
    linear_combination
      -M*hw+C k⁻¹*A*m*hs+M*A*y.derivative*m*hi
  refine ⟨B,hb,?_⟩
  apply mul_left_cancel₀ hy
  simp only [mul_zero]
  rw [hb] at hs
  simp only [derivative_mul] at hs
  rw [C_sub,C_1]
  linear_combination hs

/-- The actual squared low multiplier requires four proper divisions after conic pullback. -/
theorem fourth_power_wronskian_division (A y m M : K[X]) (hy : y≠0)
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h4 : (4 : K)≠0)
    (hw : A*(y*m.derivative-y.derivative*m)=1-y^2)
    (hs : y*M.derivative-C (4 : K)*y.derivative*M=0) :
    ∃ B : K[X], M=y^4*B ∧ B.derivative=0 := by
  obtain ⟨B3,hB3,hs3⟩ := weighted_wronskian_division A y m M hy 4 h4 hw hs
  norm_num only at hs3
  obtain ⟨B2,hB2,hs2⟩ := weighted_wronskian_division A y m B3 hy 3 h3 hw hs3
  norm_num only at hs2
  obtain ⟨B1,hB1,hs1⟩ := weighted_wronskian_division A y m B2 hy 2 h2 hw hs2
  norm_num only at hs1
  obtain ⟨B,hB,hs0⟩ := weighted_wronskian_division A y m B1 hy 1 one_ne_zero hw hs1
  norm_num only at hs0
  refine ⟨B,?_,?_⟩
  · rw [hB3,hB2,hB1,hB]
    ring
  · apply mul_left_cancel₀ hy
    simpa only [C_0,zero_mul,sub_zero,mul_zero] using hs0

theorem squared_multiplier_ratio_division (A y m M : K[X]) (hy : y≠0)
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h4 : (4 : K)≠0)
    (hw : A*(y*m.derivative-y.derivative*m)=1-y^2)
    (hs : y^2*M.derivative-2*M*(y^2).derivative=0) :
    ∃ B : K[X], M=y^4*B ∧ B.derivative=0 := by
  have hfirst : y*M.derivative-C (4 : K)*y.derivative*M=0 := by
    apply mul_left_cancel₀ hy
    simp only [mul_zero]
    simp only [derivative_sq,C_ofNat] at hs ⊢
    linear_combination hs
  exact fourth_power_wronskian_division A y m M hy h2 h3 h4 hw hfirst

end WPFieldAssembly.SourceClosureConicWeightedDivision
