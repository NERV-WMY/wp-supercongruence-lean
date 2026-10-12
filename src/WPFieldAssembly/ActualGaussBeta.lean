import WPFinitePrimitiveTransport

open scoped Polynomial
open Polynomial WPFiniteProductTail WPFinitePrimitiveTransport

namespace WPFieldAssembly.ActualGaussHarmonic

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The exact unit-pivot integral of the full polynomial (1-X²)^n. -/
noncomputable def betaP (p n : ℕ) : K[X] :=
  unitPrimitiveP p (X*(1-X^2)^n) 0

noncomputable def betaEndpoint (p n : ℕ) : K := (betaP (K:=K) p n).eval 1

private theorem beta_source_degree (p n : ℕ) (hband : 2*n+1<p) :
    (X*(1-X^2)^n : K[X]).natDegree<p := by
  have hq : (1-X^2 : K[X]).natDegree≤2 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have hn : ((1-X^2 : K[X])^n).natDegree≤n*2 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left n hq)
  have hm : (X*(1-X^2)^n : K[X]).natDegree≤1+n*2 := by
    exact natDegree_mul_le_of_le (natDegree_X_le (R:=K)) hn
  omega

theorem betaP_derivative (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hband : 2*n+1<p) : (betaP (K:=K) p n).derivative=(1-X^2)^n := by
  apply mul_left_cancel₀ (X_ne_zero (R:=K))
  exact originPrimitiveP_source p (X*(1-X^2)^n)
    (beta_source_degree p n hband) (by simp)

theorem betaP_zero (p n : ℕ) : (betaP (K:=K) p n).eval 0=0 := by
  exact unitPrimitiveP_zero p _ 0

theorem betaP_degree (p n : ℕ) : (betaP (K:=K) p n).natDegree≤p-1 := by
  exact unitPrimitiveP_degree p _ 0

theorem betaEndpoint_zero_index (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 2≤p) : betaEndpoint (K:=K) p 0=1 := by
  have he : betaP (K:=K) p 0=(X : K[X]) := by
    have hd : ((betaP (K:=K) p 0)-X).derivative=0 := by
      rw [derivative_sub,betaP_derivative p 0 (by omega),pow_zero,derivative_X,sub_self]
    have hg : ((betaP (K:=K) p 0)-X).natDegree<p :=
      (natDegree_sub_le _ _).trans_lt (max_lt
        ((betaP_degree p 0).trans_lt (by omega)) (by simpa only [natDegree_X]))
    have hz : ((betaP (K:=K) p 0)-X).eval 0=0 := by
      rw [eval_sub,betaP_zero,eval_X,sub_self]
    exact sub_eq_zero.mp (zero_of_derivative_degree p _ hg hd hz)
  rw [betaEndpoint,he,eval_X]

/-- The literal beta recurrence follows from an entire polynomial derivative. -/
theorem betaEndpoint_recurrence (p n : ℕ) [Fact p.Prime] [CharP K p]
    (hband : 2*n+3<p) :
    ((2*n+3 : ℕ) : K)*betaEndpoint (K:=K) p (n+1)=
      ((2*n+2 : ℕ) : K)*betaEndpoint (K:=K) p n := by
  let Q : K[X] := X*(1-X^2)^(n+1)
  have hq : Q.natDegree<p := beta_source_degree p (n+1) (by omega)
  have hd : Q.derivative=
      C (((2*n+3 : ℕ) : K))*(1-X^2)^(n+1)-
        C (((2*n+2 : ℕ) : K))*(1-X^2)^n := by
    dsimp only [Q]
    rw [derivative_mul,derivative_X,derivative_pow_succ,
      derivative_sub,derivative_one,derivative_X_sq]
    simp only [one_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      map_add,map_mul,map_ofNat,map_one,pow_succ]
    ring
  have he : Q=
      C (((2*n+3 : ℕ) : K))*betaP (K:=K) p (n+1)-
        C (((2*n+2 : ℕ) : K))*betaP (K:=K) p n := by
    have hg : (Q-(C (((2*n+3 : ℕ) : K))*betaP (K:=K) p (n+1)-
        C (((2*n+2 : ℕ) : K))*betaP (K:=K) p n)).natDegree<p :=
      (natDegree_sub_le _ _).trans_lt (max_lt hq
        ((natDegree_sub_le _ _).trans_lt (max_lt
          ((natDegree_C_mul_le _ _).trans_lt
            ((betaP_degree p (n+1)).trans_lt (by omega)))
          ((natDegree_C_mul_le _ _).trans_lt
            ((betaP_degree p n).trans_lt (by omega))))))
    have hD : (Q-(C (((2*n+3 : ℕ) : K))*betaP (K:=K) p (n+1)-
        C (((2*n+2 : ℕ) : K))*betaP (K:=K) p n)).derivative=0 := by
      rw [derivative_sub,derivative_sub,derivative_C_mul,derivative_C_mul,
        betaP_derivative p (n+1) (by omega),betaP_derivative p n (by omega),hd,
        sub_self]
    have h0 : (Q-(C (((2*n+3 : ℕ) : K))*betaP (K:=K) p (n+1)-
        C (((2*n+2 : ℕ) : K))*betaP (K:=K) p n)).eval 0=0 := by
      simp only [eval_sub,eval_mul,eval_C,betaP_zero,mul_zero,sub_zero]
      simp only [Q,eval_mul,eval_X,zero_mul]
    exact sub_eq_zero.mp (zero_of_derivative_degree p _ hg hD h0)
  have hv := congrArg (fun R : K[X] => R.eval 1) he
  have hz : Q.eval 1=0 := by
    simp only [Q,eval_mul,eval_X,eval_pow,eval_sub,eval_one,one_pow,sub_self,
      zero_pow (by omega : n+1≠0),mul_zero]
  simp only [eval_sub,eval_mul,eval_C,hz] at hv
  change ((2*n+3 : ℕ) : K)*(betaP (K:=K) p (n+1)).eval 1 =
    ((2*n+2 : ℕ) : K)*(betaP (K:=K) p n).eval 1
  linear_combination -hv

end WPFieldAssembly.ActualGaussHarmonic
