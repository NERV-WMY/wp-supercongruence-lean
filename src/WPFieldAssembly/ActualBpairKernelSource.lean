import WPFieldAssembly.ActualBpairFiniteKernel
import WPFinitePSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The reciprocal log is cleared by the original two-pole polynomial. -/
theorem kernelLog_a_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (kernelLog p (1/4))=
      4*(T 1-LaurentPolynomial.C (1/4 : K))*(1-T ((p-1 : ℕ) : ℤ)) := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have ha := WPFinitePSource.LP_scaled_cleared_source p (1/4 : K) hap
  have hc : 4*Polynomial.C (1/4 : K)=(1 : K[X]) := by
    change Polynomial.C (4 : K)*Polynomial.C (1/4 : K)=1
    rw [←Polynomial.C_mul,mul_one_div_cancel h4,Polynomial.C_1]
  have he : (WPFiniteZSource.Abar : K[X]) *
      ((WPFiniteAffineLog.LP p).comp (Polynomial.C (1/4 : K)*X)).derivative=
      4*(X-Polynomial.C (1/4 : K))*(1-X^(p-1)) := by
    rw [WPFiniteZSource.Abar,WPFinitePSource.pole_product p hp]
    linear_combination -4*(1-4*X)*ha+4*X*(1-X^(p-1))*hc
  have ht := congrArg (fun Q : K[X] => Q.toLaurent) he
  simpa only [kernelLog,map_mul,map_sub,map_pow,map_one,map_ofNat,
    Polynomial.toLaurent_C,Polynomial.toLaurent_X,LaurentPolynomial.T_pow,
    ←D_toLaurent,one_mul,mul_one] using ht

/-- The direct log uses the same whole two-pole polynomial. -/
theorem kernelLog_b_cleared (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (kernelLog p 4)=
      4*(T 1-4)*(1-T ((p-1 : ℕ) : ℤ)) := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hb := WPFinitePSource.LP_scaled_cleared_source p (4 : K) h4p
  simp only [map_ofNat] at hb
  have hc : 4*Polynomial.C (1/4 : K)=(1 : K[X]) := by
    change Polynomial.C (4 : K)*Polynomial.C (1/4 : K)=1
    rw [←Polynomial.C_mul,mul_one_div_cancel h4,Polynomial.C_1]
  have he : (WPFiniteZSource.Abar : K[X]) *
      ((WPFiniteAffineLog.LP p).comp (Polynomial.C (4 : K)*X)).derivative=
      4*(X-4)*(1-X^(p-1)) := by
    rw [WPFiniteZSource.Abar,WPFinitePSource.pole_product p hp]
    simp only [map_ofNat]
    linear_combination -4*(1-Polynomial.C (1/4 : K)*X)*hb+
      4*X*(1-X^(p-1))*hc
  have ht := congrArg (fun Q : K[X] => Q.toLaurent) he
  simpa only [kernelLog,map_mul,map_sub,map_pow,map_one,map_ofNat,
    Polynomial.toLaurent_C,Polynomial.toLaurent_X,LaurentPolynomial.T_pow,
    ←D_toLaurent,one_mul,mul_one] using ht

/-- A whole Frobenius phase has zero literal characteristic-p derivative. -/
theorem D_negative_frobenius_phase (p t : ℕ) [CharP K p] :
    D (T (-(t : ℤ)*(p : ℤ)) : K[T;T⁻¹])=0 := by
  have hz : ((-(t : ℤ)*(p : ℤ) : ℤ) : K)=0 := by
    simp only [Int.cast_mul,Int.cast_neg,Int.cast_natCast,CharP.cast_eq_zero,
      mul_zero]
  have hd := D_monomial (1 : K) (-(t : ℤ)*(p : ℤ))
  simpa only [map_one,one_mul,hz,map_zero,zero_mul] using hd

/-- The full original three-band kernel, before any source-residue separation. -/
theorem literalKB_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * D (literalKB (K:=K) p)=
      (1-T ((p-1 : ℕ) : ℤ))*
        (20*T 1+LaurentPolynomial.C (15/2 : K)+
          (LaurentPolynomial.C (113/2 : K)*T 1+4)*T (-(p : ℤ))+
          (LaurentPolynomial.C (1953/8 : K)*T 1-
            LaurentPolynomial.C (113/2 : K))*T (-2*(p : ℤ))) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K)≠0 := by
    convert mul_ne_zero h2 h3 using 1
    norm_num
  have h8 : (8 : K)≠0 := by
    convert pow_ne_zero 3 h2 using 1
    norm_num
  have ha := kernelLog_a_cleared (K:=K) p hp
  have hb := kernelLog_b_cleared (K:=K) p hp
  have hT1 : D (T (-(p : ℤ)) : K[T;T⁻¹])=0 := by
    simpa only [Nat.cast_one,neg_mul,one_mul] using
      D_negative_frobenius_phase (K:=K) p 1
  have hT2 : D (T (-2*(p : ℤ)) : K[T;T⁻¹])=0 := by
    simpa only [Nat.cast_ofNat,neg_mul] using
      D_negative_frobenius_phase (K:=K) p 2
  simp only [literalKB,map_add,map_sub,D_mul,D_C,hT1,hT2,mul_zero,zero_mul,zero_add]
  have he :
      (WPFiniteZSource.Abar : K[X]).toLaurent *
        (LaurentPolynomial.C (1/6 : K)*
          (LaurentPolynomial.C (35 : K)*D (kernelLog p (1/4))+
            LaurentPolynomial.C (23*4 : K)*T (-(p : ℤ))*D (kernelLog p (1/4))+
            LaurentPolynomial.C (23*4^2 : K)*T (-2*(p : ℤ))*D (kernelLog p (1/4))-
            LaurentPolynomial.C (5 : K)*D (kernelLog p 4)-
            LaurentPolynomial.C (29*(1/4) : K)*T (-(p : ℤ))*D (kernelLog p 4)-
            LaurentPolynomial.C (29*(1/4)^2 : K)*T (-2*(p : ℤ))*D (kernelLog p 4)))=
        LaurentPolynomial.C (1/6 : K)*
          (LaurentPolynomial.C (35 : K)*(4*(T 1-LaurentPolynomial.C (1/4 : K))*(1-T ((p-1 : ℕ) : ℤ)))+
            LaurentPolynomial.C (23*4 : K)*T (-(p : ℤ))*(4*(T 1-LaurentPolynomial.C (1/4 : K))*(1-T ((p-1 : ℕ) : ℤ)))+
            LaurentPolynomial.C (23*4^2 : K)*T (-2*(p : ℤ))*(4*(T 1-LaurentPolynomial.C (1/4 : K))*(1-T ((p-1 : ℕ) : ℤ)))-
            LaurentPolynomial.C (5 : K)*(4*(T 1-4)*(1-T ((p-1 : ℕ) : ℤ)))-
            LaurentPolynomial.C (29*(1/4) : K)*T (-(p : ℤ))*(4*(T 1-4)*(1-T ((p-1 : ℕ) : ℤ)))-
            LaurentPolynomial.C (29*(1/4)^2 : K)*T (-2*(p : ℤ))*(4*(T 1-4)*(1-T ((p-1 : ℕ) : ℤ)))) := by
    linear_combination LaurentPolynomial.C (1/6 : K)*
      (LaurentPolynomial.C (35 : K)+LaurentPolynomial.C (23*4 : K)*T (-(p : ℤ))+
        LaurentPolynomial.C (23*4^2 : K)*T (-2*(p : ℤ)))*ha-
      LaurentPolynomial.C (1/6 : K)*
        (LaurentPolynomial.C (5 : K)+LaurentPolynomial.C (29*(1/4) : K)*T (-(p : ℤ))+
          LaurentPolynomial.C (29*(1/4)^2 : K)*T (-2*(p : ℤ)))*hb
  rw [he]
  have hc0x : (1/6 : K)*(35*4-5*4)=20 := by
    field_simp [h6]; ring
  have hc0c : (1/6 : K)*(-35*4*(1/4)+5*4*4)=15/2 := by
    field_simp [h2,h4,h6]; ring
  have hc1x : (1/6 : K)*(23*4*4-29*(1/4)*4)=113/2 := by
    field_simp [h2,h4,h6]; ring
  have hc1c : (1/6 : K)*(-23*4*4*(1/4)+29*(1/4)*4*4)=4 := by
    field_simp [h4,h6]; ring
  have hc2x : (1/6 : K)*(23*4^2*4-29*(1/4)^2*4)=1953/8 := by
    field_simp [h4,h6,h8]; ring
  have hc2c : (1/6 : K)*(-23*4^2*4*(1/4)+29*(1/4)^2*4*4)=-(113/2) := by
    field_simp [h2,h4,h6]; ring
  have h0x := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc0x
  have h0c := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc0c
  have h1x := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc1x
  have h1c := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc1c
  have h2x := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc2x
  have h2c := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc2c
  simp only [map_mul,map_sub,map_add,map_neg,map_pow,map_ofNat] at h0x h0c h1x h1c h2x h2c ⊢
  linear_combination (1-T ((p-1 : ℕ) : ℤ))*T 1*h0x+
    (1-T ((p-1 : ℕ) : ℤ))*h0c+
    (1-T ((p-1 : ℕ) : ℤ))*T 1*T (-(p : ℤ))*h1x+
    (1-T ((p-1 : ℕ) : ℤ))*T (-(p : ℤ))*h1c+
    (1-T ((p-1 : ℕ) : ℤ))*T 1*T (-2*(p : ℤ))*h2x+
    (1-T ((p-1 : ℕ) : ℤ))*T (-2*(p : ℤ))*h2c

end WPFieldAssembly.ActualBpairContraction
