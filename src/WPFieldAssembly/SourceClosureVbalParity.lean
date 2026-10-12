import WPFieldAssembly.NativeIR28
import WPFieldAssembly.NativeQuadraticInverse

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualRankTwoComparison WPActualGaussBottom WPFieldAssembly.NativeIR28

namespace WPFieldAssembly.SourceClosureVbalParity

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- Contract exactly the parity retained by the reflected native polynomial. -/
noncomputable def parityPolynomial (e : ℕ) (P : (ZMod p)[X]) : (ZMod p)[X] :=
  if e%2=0 then contract 2 P else contract 2 P.divX

theorem parity_polynomial_factor (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P) :
    P=X^(e%2)*(parityPolynomial p e P).comp (X^2) := by
  have hlt : e%2<2 := Nat.mod_lt e (by norm_num : 0<2)
  have hmod : e%2=0 ∨ e%2=1 := by omega
  rcases hmod with hzero | hone
  · have heven : Even e := ⟨e/2,by have := Nat.mod_add_div e 2; omega⟩
    have hP : P.comp (-X)=P := by
      rw [heven.neg_one_pow,C_1,one_mul] at hreflect
      exact hreflect
    have h := even_expand_contract_two p hp P hP
    rw [expand_eq_comp_X_pow] at h
    simp only [parityPolynomial,hzero,if_pos,pow_zero,one_mul]
    exact h.symm
  · have hodd : Odd e := ⟨e/2,by have := Nat.mod_add_div e 2; omega⟩
    have hP : P.comp (-X)= -P := by
      rw [hodd.neg_one_pow,C_neg,C_1,neg_one_mul] at hreflect
      exact hreflect
    have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
    have hc0 := congrArg (fun Q : (ZMod p)[X] => Q.coeff 0) hP
    rw [WPFieldAssembly.ConicKernel.coeff_comp_neg,coeff_neg,pow_zero,mul_one] at hc0
    have hz : (2 : ZMod p)*P.coeff 0=0 := by linear_combination hc0
    have h0 : P.coeff 0=0 := (mul_eq_zero.mp hz).resolve_left h2
    have hdiv : P.divX.comp (-X)=P.divX := by
      ext n
      rw [WPFieldAssembly.ConicKernel.coeff_comp_neg]
      simp only [coeff_divX]
      have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (n+1)) hP
      rw [WPFieldAssembly.ConicKernel.coeff_comp_neg,coeff_neg,pow_succ] at hc
      linear_combination -hc
    have h := even_expand_contract_two p hp P.divX hdiv
    rw [expand_eq_comp_X_pow] at h
    have hX : X*P.divX=P := by
      simpa only [h0,C_0,add_zero] using X_mul_divX_add P
    simp only [parityPolynomial,hone,if_neg (by norm_num : ¬(1 : ℕ)=0),pow_one]
    rw [h]
    exact hX.symm

theorem parity_square_contract (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P) :
    contract 2 (P^2)=X^(e%2)*(parityPolynomial p e P)^2 := by
  let Z := parityPolynomial p e P
  have hf : P=X^(e%2)*Z.comp (X^2) := parity_polynomial_factor p hp e P hreflect
  have he : P^2=expand (ZMod p) 2 (X^(e%2)*Z^2) := by
    rw [hf,mul_pow,expand_eq_comp_X_pow,mul_comp,pow_comp,X_comp,pow_comp]
    rw [←pow_mul,←pow_mul,Nat.mul_comm (e%2) 2]
  have h := congrArg (contract 2) he
  rw [contract_expand 2 (by norm_num : (2 : ℕ)≠0)] at h
  exact h

theorem parity_polynomial_one (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P) :
    (parityPolynomial p e P).eval 1=P.eval 1 := by
  have h := congrArg (fun Q : (ZMod p)[X] => Q.eval 1)
    (parity_polynomial_factor p hp e P hreflect)
  simpa only [eval_mul,eval_pow,eval_X,one_pow,one_mul,eval_comp] using h.symm

/-- The parity factor retains the exact degree shift, including the zero polynomial. -/
theorem parity_polynomial_degree (hp : 19≤p) (e D : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P)
    (hdegree : P.natDegree≤D) (hshift : e%2≤D) :
    2*(parityPolynomial p e P).natDegree+e%2≤D := by
  let Z := parityPolynomial p e P
  change 2*Z.natDegree+e%2≤D
  by_cases hZ : Z=0
  · simpa only [hZ,natDegree_zero,mul_zero,zero_add] using hshift
  · have hcomp : Z.comp (X^2)≠0 := by
      rw [←expand_eq_comp_X_pow]
      exact (expand_ne_zero (by norm_num : 0<(2 : ℕ))).2 hZ
    have hfactor : P=X^(e%2)*Z.comp (X^2) :=
      parity_polynomial_factor p hp e P hreflect
    rw [hfactor,natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
      natDegree_X_pow,natDegree_comp,natDegree_X_pow] at hdegree
    change 2*Z.natDegree+e%2≤D
    omega

/-- The original quadratic inverse is the same whole parity square. -/
theorem parity_square_quadratic_inverse (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P) :
    (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse (P^2)).comp (1-X)=
      X^(e%2)*(parityPolynomial p e P)^2 := by
  rw [WPFieldAssembly.NativeQuadraticInverse.quadraticInverse,comp_assoc]
  simp only [sub_comp,one_comp,X_comp,sub_sub_cancel,comp_X]
  exact parity_square_contract p hp e P hreflect

/-- The full parity carrier in the original conic coordinate, before sign selection. -/
noncomputable def parityConicPolynomial (e : ℕ) (P : (ZMod p)[X]) : (ZMod p)[X] :=
  (C (1/5 : ZMod p)*(4*X^2-11))^(e%2)*
    (parityPolynomial p e P).comp
      (C (1/5 : ZMod p)*(X^2+1)*(C (1/5 : ZMod p)*(4*X^2-11))^2)

theorem parity_conic_norm (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X])
    (hreflect : P.comp (-X)=C ((-1 : ZMod p)^e)*P) :
    (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse (P^2)).comp
        (1-C (1/5 : ZMod p)*(X^2+1)*(C (1/5 : ZMod p)*(4*X^2-11))^2)=
      (C (1/5 : ZMod p)*(X^2+1))^(e%2)*(parityConicPolynomial p e P)^2 := by
  let s : (ZMod p)[X] := C (1/5 : ZMod p)*(X^2+1)
  let c : (ZMod p)[X] := C (1/5 : ZMod p)*(4*X^2-11)
  let Z := parityPolynomial p e P
  have h := congrArg (fun Q : (ZMod p)[X] => Q.comp (s*c^2))
    (parity_square_quadratic_inverse p hp e P hreflect)
  simp only [comp_assoc,sub_comp,one_comp,X_comp,mul_comp,pow_comp] at h
  have hpow : (c^2)^(e%2)=(c^(e%2))^2 := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  change _=s^(e%2)*(c^(e%2)*Z.comp (s*c^2))^2
  rw [h,mul_pow,hpow]
  ring

/-- Both unit endpoints are values of the full parity polynomial. -/
theorem parity_conic_end_values (hp : 19≤p) (e : ℕ) (P : (ZMod p)[X]) :
    (parityConicPolynomial p e P).eval 2=(parityPolynomial p e P).eval 1 ∧
      (parityConicPolynomial p e P).eval (1/2)=
        (-2 : ZMod p)^(e%2)*(parityPolynomial p e P).eval 1 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hc2 : (1/5 : ZMod p)*(4*(2 : ZMod p)^2-11)=1 := by
    field_simp [h5]
    ring
  have hs2 : (1/5 : ZMod p)*((2 : ZMod p)^2+1)=1 := by
    field_simp [h5]
    ring
  have hchalf : (1/5 : ZMod p)*(4*(1/2 : ZMod p)^2-11)= -2 := by
    field_simp [h2,h5]
    ring
  have harg : (1/5 : ZMod p)*((1/2 : ZMod p)^2+1)*(-2 : ZMod p)^2=1 := by
    field_simp [h2,h5]
    ring
  constructor <;> simp only [parityConicPolynomial,eval_mul,eval_pow,eval_C,eval_sub,eval_add,
    eval_ofNat,eval_one,eval_X,eval_comp,hc2,hs2,hchalf,harg,one_pow,one_mul]

/-- The actual Y parity uses every retained Jacobi coefficient in both prime classes. -/
theorem actual_Y_parity (hp : 19≤p) :
    actualLegendreJacobi p=
      X^((p/6)%2)*(parityPolynomial p (p/6) (actualLegendreJacobi p)).comp (X^2) ∧
      (parityPolynomial p (p/6) (actualLegendreJacobi p)).eval 1=1 := by
  have hY : (actualLegendreJacobi p).comp (-X)=
      C ((-1 : ZMod p)^(p/6))*actualLegendreJacobi p :=
    legendreField_reflect p (p/6) (by omega)
  refine ⟨parity_polynomial_factor p hp _ _ hY,?_⟩
  rw [parity_polynomial_one p hp _ _ hY,actualLegendreJacobi_endpoint_one]

/-- The same contraction extracts the actual proper parity, without assigning its harmonic end. -/
theorem actual_n_parity (hp : 19≤p) :
    properLegendreJacobi p=
      X^((p/6+1)%2)*(parityPolynomial p (p/6+1) (properLegendreJacobi p)).comp (X^2) ∧
      (parityPolynomial p (p/6+1) (properLegendreJacobi p)).eval 1=
        -fieldHarmonic p (p/6) := by
  have hn : (properLegendreJacobi p).comp (-X)=
      C ((-1 : ZMod p)^(p/6+1))*properLegendreJacobi p := by
    simpa only [pow_succ,mul_neg_one,C_neg,neg_mul] using actual_proper_legendre_reflect p hp
  refine ⟨parity_polynomial_factor p hp _ _ hn,?_⟩
  rw [parity_polynomial_one p hp _ _ hn,properLegendreJacobi_endpoint_one]

theorem actual_Y_parity_degree (hp : 19≤p) :
    2*(parityPolynomial p (p/6) (actualLegendreJacobi p)).natDegree+
      (p/6)%2≤p/6 := by
  apply parity_polynomial_degree p hp
  · exact legendreField_reflect p (p/6) (by omega)
  · exact actualLegendreJacobi_degree p
  · exact Nat.mod_le _ _

theorem actual_n_parity_degree (hp : 19≤p) :
    2*(parityPolynomial p (p/6+1) (properLegendreJacobi p)).natDegree+
      (p/6+1)%2≤p/6-1 := by
  apply parity_polynomial_degree p hp
  · simpa only [pow_succ,mul_neg_one,C_neg,neg_mul] using
      actual_proper_legendre_reflect p hp
  · have h := properLegendreJacobi_degree p (by omega)
    omega
  · have h := Nat.mod_lt (p/6+1) (by norm_num : 0<2)
    omega

end WPFieldAssembly.SourceClosureVbalParity
