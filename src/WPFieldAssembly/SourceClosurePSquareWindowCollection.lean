import WPFieldAssembly.SourceClosurePSquareEndpoint

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteProductTail WPFiniteABSourceTail
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.SourceClosurePSquareEndpoint

namespace WPFieldAssembly.SourceClosurePSquareWindowCollection

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: direct signed coefficient collection of the full
   five square phases. All three endpoint windows and the p diagonal remain.
   The degree hypotheses below are ordinary polynomial bounds; the actual
   P application proves them from its specified W and full finite logarithms.
   This generic leaf performs no reduction of the original source to a scalar. -/

noncomputable def phaseCarrier (p : ℕ) (A B C : K[X]) : K[T;T⁻¹] :=
  T (p : ℤ)*A.toLaurent+B.toLaurent+T (-(p : ℤ))*C.toLaurent

noncomputable def pairedTail (p : ℕ) (a b : K) (F : K[X]) : K :=
  (strictTail p F).eval a+2*(strictTail p F).eval b

theorem phaseCarrier_square (p : ℕ) (A B C : K[X]) :
    (phaseCarrier p A B C)^2=
      T (2*(p : ℤ))*(A^2).toLaurent+
      LaurentPolynomial.C (2 : K)*T (p : ℤ)*(A*B).toLaurent+
      (B^2+Polynomial.C (2 : K)*A*C).toLaurent+
      LaurentPolynomial.C (2 : K)*T (-(p : ℤ))*(B*C).toLaurent+
      T (-2*(p : ℤ))*(C^2).toLaurent := by
  have ht : (T (p : ℤ) : K[T;T⁻¹])^2=T (2*(p : ℤ)) := by
    rw [T_pow]
    congr 1
  have hi : (T (-(p : ℤ)) : K[T;T⁻¹])^2=T (-2*(p : ℤ)) := by
    rw [T_pow]
    congr 1
    omega
  have hu : (T (p : ℤ) : K[T;T⁻¹])*T (-(p : ℤ))=1 := by
    rw [←T_add,add_neg_cancel,T_zero]
  unfold phaseCarrier
  simp only [map_add,map_mul,map_pow,map_ofNat]
  linear_combination A.toLaurent^2*ht+C.toLaurent^2*hi+
    2*A.toLaurent*C.toLaurent*hu

theorem pairedTail_add (p : ℕ) (hp : 0<p) (a b : K) (F G : K[X]) :
    pairedTail p a b (F+G)=pairedTail p a b F+pairedTail p a b G := by
  simp only [pairedTail,strictTail_add p hp,eval_add]
  ring

theorem pairedTail_C_mul (p : ℕ) (hp : 0<p) (a b c : K) (F : K[X]) :
    pairedTail p a b (Polynomial.C c*F)=c*pairedTail p a b F := by
  simp only [pairedTail,strictTail_C_mul p hp,eval_mul,eval_C]
  ring

private theorem shifted_square (p : ℕ) (s : ℤ) (A B C : K[X]) :
    T s*(phaseCarrier p A B C)^2=
      T (s+2*(p : ℤ))*(A^2).toLaurent+
      LaurentPolynomial.C (2 : K)*T (s+(p : ℤ))*(A*B).toLaurent+
      T s*(B^2+Polynomial.C (2 : K)*A*C).toLaurent+
      LaurentPolynomial.C (2 : K)*T (s-(p : ℤ))*(B*C).toLaurent+
      T (s-2*(p : ℤ))*(C^2).toLaurent := by
  rw [phaseCarrier_square]
  simp only [mul_add]
  simp only [sub_eq_add_neg,T_add]
  ring

private theorem endpointTrace_C_mul_T (a b d : K) (n : ℤ) (F : K[T;T⁻¹]) :
    endpointTrace a b (LaurentPolynomial.C d*T n*F)=
      d*endpointTrace a b (T n*F) := by
  rw [mul_assoc,endpointTrace_C_mul]

/-- The p coefficient is kept by the constant correction in each polynomial window. -/
theorem phaseCarrier_square_windows (p : ℕ) (hp : 0<p) (a b : K) (A B C : K[X])
    (hA : 2*A.natDegree≤p) (hB : B.natDegree<p) (hC : C.natDegree<p) :
    endpointTrace a b ((phaseCarrier p A B C)^2)=
      -2*b^(2*p)*(A.eval b)^2-a^(2*p)*(A.eval a)^2-
      4*b^p*A.eval b*B.eval b-2*a^p*A.eval a*B.eval a-
      2*(B.eval b)^2-4*A.eval b*C.eval b-(B.eval a)^2-2*A.eval a*C.eval a+
      3*((B.eval 0)^2+2*A.eval 0*C.eval 0)-2*pairedTail p a b (B*C) ∧
    endpointTrace a b (T (-(p : ℤ))*(phaseCarrier p A B C)^2)=
      -2*b^p*(A.eval b)^2-a^p*(A.eval a)^2-
      4*A.eval b*B.eval b-2*A.eval a*B.eval a+6*A.eval 0*B.eval 0-
      pairedTail p a b (B^2)-2*pairedTail p a b (A*C) ∧
    endpointTrace a b (T (-2*(p : ℤ))*(phaseCarrier p A B C)^2)=
      -2*(A.eval b)^2-(A.eval a)^2+3*(A.eval 0)^2-
      2*pairedTail p a b (A*B) := by
  have hA2 : (A^2).natDegree≤p := (natDegree_pow_le (p:=A) (n:=2)).trans hA
  have hB2 : (B^2).natDegree<2*p :=
    (natDegree_pow_le (p:=B) (n:=2)).trans_lt (by omega)
  have hC2 : (C^2).natDegree<2*p :=
    (natDegree_pow_le (p:=C) (n:=2)).trans_lt (by omega)
  have hAB : (A*B).natDegree<2*p :=
    (natDegree_mul_le (p:=A) (q:=B)).trans_lt (by omega)
  have hAC : (A*C).natDegree<2*p :=
    (natDegree_mul_le (p:=A) (q:=C)).trans_lt (by omega)
  have hBC : (B*C).natDegree<2*p :=
    (natDegree_mul_le (p:=B) (q:=C)).trans_lt (by omega)
  have htwoAC : (Polynomial.C (2 : K)*A*C).natDegree<2*p := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le (2 : K) (A*C)).trans_lt hAC
  have hmiddle : (B^2+Polynomial.C (2 : K)*A*C).natDegree<2*p :=
    (natDegree_add_le _ _).trans_lt (max_lt hB2 htwoAC)
  have hn2 (F : K[X]) (hF : F.natDegree<2*p) :
      endpointTrace a b (T (-2*(p : ℤ))*F.toLaurent)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
      endpointTrace_shift_negative_low a b (2*p) (by omega) F (by omega)
  have hn3 (F : K[X]) (hF : F.natDegree<2*p) :
      endpointTrace a b (T (-3*(p : ℤ))*F.toLaurent)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
      endpointTrace_shift_negative_low a b (3*p) (by omega) F (by omega)
  have hn4 (F : K[X]) (hF : F.natDegree<2*p) :
      endpointTrace a b (T (-4*(p : ℤ))*F.toLaurent)=0 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul] using
      endpointTrace_shift_negative_low a b (4*p) (by omega) F (by omega)
  have hzero : endpointTrace a b ((phaseCarrier p A B C)^2)=
      -2*b^(2*p)*(A.eval b)^2-a^(2*p)*(A.eval a)^2-
      4*b^p*A.eval b*B.eval b-2*a^p*A.eval a*B.eval a-
      2*(B.eval b)^2-4*A.eval b*C.eval b-(B.eval a)^2-2*A.eval a*C.eval a+
      3*((B.eval 0)^2+2*A.eval 0*C.eval 0)-2*pairedTail p a b (B*C) := by
    rw [phaseCarrier_square]
    simp only [(endpointTrace a b).map_add,endpointTrace_C_mul_T]
    rw [show (2*(p : ℤ))=((2*p : ℕ) : ℤ) by omega,
      endpointTrace_shift_positive a b (2*p) (by omega),
      endpointTrace_shift_positive a b p hp,endpointTrace_polynomial,
      endpointTrace_shift_negative_strict a b p hp _ hBC,hn2 _ hC2]
    simp only [coeff_zero_eq_eval_zero,eval_add,eval_mul,eval_C,eval_pow,pairedTail]
    ring
  have hone : endpointTrace a b (T (-(p : ℤ))*(phaseCarrier p A B C)^2)=
      -2*b^p*(A.eval b)^2-a^p*(A.eval a)^2-
      4*A.eval b*B.eval b-2*A.eval a*B.eval a+6*A.eval 0*B.eval 0-
      pairedTail p a b (B^2)-2*pairedTail p a b (A*C) := by
    rw [shifted_square]
    rw [show -(p : ℤ)+2*(p : ℤ)=(p : ℤ) by ring,
      show -(p : ℤ)+(p : ℤ)=0 by ring,
      show -(p : ℤ)-(p : ℤ)= -2*(p : ℤ) by ring,
      show -(p : ℤ)-2*(p : ℤ)= -3*(p : ℤ) by ring,T_zero,mul_one]
    simp only [(endpointTrace a b).map_add,endpointTrace_C_mul_T,endpointTrace_C_mul]
    rw [endpointTrace_shift_positive a b p hp,endpointTrace_polynomial,
      endpointTrace_shift_negative_strict a b p hp _ hmiddle,hn2 _ hBC,hn3 _ hC2]
    simp only [strictTail_add p hp,mul_assoc,strictTail_C_mul p hp,
      coeff_zero_eq_eval_zero,eval_add,eval_mul,eval_C,eval_pow,pairedTail]
    ring
  refine ⟨hzero,hone,?_⟩
  rw [shifted_square]
  rw [show -2*(p : ℤ)+2*(p : ℤ)=0 by ring,
    show -2*(p : ℤ)+(p : ℤ)= -(p : ℤ) by ring,
    show -2*(p : ℤ)-(p : ℤ)= -3*(p : ℤ) by ring,
    show -2*(p : ℤ)-2*(p : ℤ)= -4*(p : ℤ) by ring,T_zero,one_mul]
  simp only [(endpointTrace a b).map_add,endpointTrace_C_mul_T]
  rw [endpointTrace_polynomial,endpointTrace_shift_negative_strict a b p hp _ hAB,
    hn2 _ hmiddle,hn3 _ hBC,hn4 _ hC2]
  simp only [coeff_zero_eq_eval_zero,eval_pow,pairedTail]
  ring

end WPFieldAssembly.SourceClosurePSquareWindowCollection
