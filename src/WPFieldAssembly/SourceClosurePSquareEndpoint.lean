import WPFieldAssembly.ActualKwWeightedTrace
import WPFiniteABSourceTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteJCarrier WPFiniteJWeightedResidue
  WPFiniteProductTail WPFiniteABSourceTail WPFieldAssembly.ActualKwWeightedTrace

namespace WPFieldAssembly.SourceClosurePSquareEndpoint

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: the signed endpoint windows in corrected NC118.
   These generic coefficient identities use the original endpointTrace;
   the strict shifted band is p < j < 2p and requires degree < 2p.
   No field division by p, generated input, endpoint assumption or
   actual scalar assignment occurs. The actual P application is separate. -/

theorem endpointTrace_trunc (a b : K) (F : K[T;T⁻¹]) :
    endpointTrace a b F=-2*(LaurentPolynomial.trunc F).eval b-
      (LaurentPolynomial.trunc F).eval a+3*(LaurentPolynomial.trunc F).coeff 0 := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add,hF,hG,eval_add,coeff_add]
    ring
  | C_mul_T n c =>
    rw [endpointTrace_monomial,LaurentPolynomial.trunc_C_mul_T]
    by_cases hn : 0<n
    · rw [if_pos (by omega),endpointWeight,if_pos hn]
      simp only [eval_monomial,coeff_monomial,if_neg (show n.toNat≠0 by omega)]
      ring
    · rw [endpointWeight_nonpositive a b n (by omega)]
      by_cases hz : n=0
      · subst n
        simp only [le_refl,if_true,Int.toNat_zero,monomial_zero_left,eval_C,coeff_C_zero]
        ring
      · rw [if_neg (by omega)]
        simp

theorem endpointTrace_shift_positive (a b : K) (n : ℕ) (hn : 0<n) (F : K[X]) :
    endpointTrace a b (T (n : ℤ)*F.toLaurent)=
      -2*b^n*F.eval b-a^n*F.eval a := by
  have hpoly : (T (n : ℤ) : K[T;T⁻¹])*F.toLaurent=(X^n*F).toLaurent := by
    rw [map_mul,Polynomial.toLaurent_X_pow]
  rw [hpoly,endpointTrace_polynomial,coeff_zero_eq_eval_zero]
  simp only [eval_mul,eval_pow,eval_X,zero_pow (by omega : n≠0),zero_mul,mul_zero,add_zero]
  ring

theorem trunc_shift_negative_strict (p : ℕ) (hp : 0<p) (F : K[X]) (hF : F.natDegree<2*p) :
    LaurentPolynomial.trunc (T (-(p : ℤ))*F.toLaurent)=
      Polynomial.C (F.coeff p)+strictTail p F := by
  ext j
  have hs := shifted_coeff (1 : K) (-(p : ℤ)) (j : ℤ) F.toLaurent
  simp only [map_one,one_mul] at hs
  rw [trunc_coeff,hs,show (j : ℤ)-(-(p : ℤ))=((p+j : ℕ) : ℤ) by omega,
    toLaurent_coeff_nat,coeff_add,coeff_C,strictTail_coeff p hp]
  by_cases hj0 : j=0
  · subst j
    simp only [if_true,add_zero]
  · simp only [if_neg hj0]
    by_cases hjp : j<p
    · rw [if_pos hjp,zero_add]
    · rw [if_neg hjp,add_zero]
      exact coeff_eq_zero_of_natDegree_lt (hF.trans_le (by omega))

theorem endpointTrace_shift_negative_strict (a b : K) (p : ℕ) (hp : 0<p)
    (F : K[X]) (hF : F.natDegree<2*p) :
    endpointTrace a b (T (-(p : ℤ))*F.toLaurent)=
      -2*(strictTail p F).eval b-(strictTail p F).eval a := by
  rw [endpointTrace_trunc,trunc_shift_negative_strict p hp F hF]
  simp only [eval_add,eval_C,coeff_add,coeff_C_zero,
    strictTail_coeff p hp,if_true,add_zero]
  ring

theorem endpointTrace_shift_negative_low (a b : K) (p : ℕ) (hp : 0<p)
    (F : K[X]) (hF : F.natDegree≤p) :
    endpointTrace a b (T (-(p : ℤ))*F.toLaurent)=0 := by
  rw [endpointTrace_shift_negative_strict a b p hp F (hF.trans_lt (by omega)),
    strictTail_low p hp F hF]
  simp

end WPFieldAssembly.SourceClosurePSquareEndpoint
