import WPFieldAssembly.ActualCubicNativeSource
import WPFieldAssembly.ActualBpairTriangles

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPFiniteAffineLog WPFiniteABSourceTail
open LaurentPolynomial (T invert invert_C invert_T)

namespace WPFieldAssembly.ActualBpairNativeTail

open ActualBpairContraction ActualCubicNativeSource

variable {K : Type*} [Field K]

set_option maxHeartbeats 2200000

private theorem native_smooth_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (a b c : ℕ) : ((2 : K)^a * 3^b * 5^c) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero a h2) (pow_ne_zero b h3))
    (pow_ne_zero c h5)

/- The native polynomial is always the original actualAK. The full strict
projection has no upper cutoff: its origin is removed exactly once. -/

theorem fullStrictPositive_Xphase (p : ℕ) (P : K[X]) :
    fullStrictPositive p 1 (X^p*P).toLaurent=fullStrictPositive p 0 P.toLaurent := by
  simpa only [map_mul,Polynomial.toLaurent_X_pow,one_mul,Nat.sub_self] using
    fullStrictPositive_phase_shift p 1 1 (by omega) P.toLaurent

theorem fullStrictPositive_upper_square (p : ℕ) (hp : 0<p) (B : K[X]) :
    fullStrictPositive p 1 (X^(2*p)*B^2).toLaurent=X^p*B^2 := by
  have he : (X : K[X])^(2*p)*B^2=X^p*(X^p*B^2) := by
    rw [show 2*p=p+p by omega,pow_add]
    ring
  rw [he,fullStrictPositive_Xphase]
  simpa only [map_mul,Polynomial.toLaurent_X_pow] using
    fullStrictPositive_upper_polynomial p hp (B^2)

/-- The entire upper square survives; the only excluded slot is the strict diagonal. -/
theorem fullStrictPositive_two_band_square (p : ℕ) (hp : 0<p) (B L : K[X]) :
    fullStrictPositive p 1 ((X^p*B+L)^2).toLaurent=
      X^p*B^2+2*fullStrictPositive p 0 (B*L).toLaurent+
        fullStrictPositive p 1 (L^2).toLaurent := by
  have he : (X^p*B+L)^2=X^(2*p)*B^2+C (2 : K)*(X^p*(B*L))+L^2 := by
    rw [show 2*p=p+p by omega,pow_add]
    simp only [map_ofNat]
    ring
  rw [he,map_add,map_add,fullStrictPositive_add,fullStrictPositive_add,
    fullStrictPositive_upper_square p hp,map_mul,Polynomial.toLaurent_C,
    fullStrictPositive_C_mul,fullStrictPositive_Xphase]
  simp only [map_ofNat]

theorem fullStrictTail_add (p k : ℕ) (F G : K[T;T⁻¹]) :
    fullStrictTail p k (F+G)=fullStrictTail p k F+fullStrictTail p k G := by
  rw [fullStrictTail,fullStrictPositive_add]
  simp only [eval_add,fullStrictTail]
  ring

theorem fullStrictTail_sub (p k : ℕ) (F G : K[T;T⁻¹]) :
    fullStrictTail p k (F-G)=fullStrictTail p k F-fullStrictTail p k G := by
  rw [fullStrictTail,fullStrictPositive_sub]
  simp only [eval_sub,fullStrictTail]
  ring

theorem fullStrictTail_C_mul (p k : ℕ) (c : K) (F : K[T;T⁻¹]) :
    fullStrictTail p k (LaurentPolynomial.C c*F)=c*fullStrictTail p k F := by
  rw [fullStrictTail,fullStrictPositive_C_mul]
  simp only [eval_mul,eval_C,fullStrictTail]
  ring

theorem fullStrictPositive_zero_polynomial (p : ℕ) (P : K[X]) :
    fullStrictPositive p 0 P.toLaurent=P-C (P.coeff 0) := by
  rw [fullStrictPositive]
  simp only [zero_mul,Nat.cast_zero,neg_zero,LaurentPolynomial.T_zero,one_mul,
    trunc_toLaurent]
  have h0 : P.toLaurent.coeff 0 = P.coeff 0 := by
    simpa only [Nat.cast_zero] using WPFiniteJCarrier.toLaurent_coeff_nat P 0
  rw [h0]

/-- The whole polynomial source retains its genuine origin in the zero-phase weight. -/
theorem fullStrictTail_zero_polynomial (p : ℕ) (P : K[X]) :
    fullStrictTail p 0 P.toLaurent=2*P.eval 4+P.eval (1/4)-3*P.coeff 0 := by
  rw [fullStrictTail,fullStrictPositive_zero_polynomial]
  simp only [eval_sub,eval_C]
  ring

theorem fullStrictTail_two_band_square (p : ℕ) (hp : 0<p) (B L : K[X]) :
    fullStrictTail p 1 ((X^p*B+L)^2).toLaurent=
      2*(4 : K)^p*(B.eval 4)^2+(1/4 : K)^p*(B.eval (1/4))^2+
        2*fullStrictTail p 0 (B*L).toLaurent+fullStrictTail p 1 (L^2).toLaurent := by
  rw [fullStrictTail,fullStrictPositive_two_band_square p hp]
  simp only [eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,fullStrictTail]
  ring

noncomputable def nativeB (p : ℕ) : K[X] :=
  C (12/5 : K)*Dstar p-C (4*WPFiniteNC122.q p/5)

noncomputable def nativeL (p : ℕ) : K[X] :=
  C (nativeConstant p)-C (33/5 : K)*Dstar p+C (2/5 : K)*logTrace p

theorem nativeL_mixed_source (p : ℕ) :
    (nativeL p : K[X])=C (nativeConstant p)-C (33/5 : K)*Dstar p+finiteMixedLog p := rfl

/-- This identification consumes the actual native source, rather than choosing a polynomial. -/
theorem actual_AK_phase_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (actualAK p : K[X])=X^p*nativeB p+nativeL p := by
  rw [actual_AK_two_band p hp]
  unfold nativeB nativeL
  ring

theorem actual_AK_square_strict_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullStrictPositive p 1 ((actualAK p : K[X])^2).toLaurent=
      X^p*(nativeB p)^2+2*fullStrictPositive p 0 ((nativeB p)*(nativeL p)).toLaurent+
        fullStrictPositive p 1 ((nativeL p)^2).toLaurent := by
  rw [actual_AK_phase_source p hp,fullStrictPositive_two_band_square p (by omega)]

/-- Every coefficient above p is retained, with no finite-window substitution. -/
theorem actual_AK_square_strict_coeff (p : ℕ) [Fact p.Prime] [CharP K p]
    (_hp : 19≤p) (j : ℕ) :
    (fullStrictPositive p 1 ((actualAK p : K[X])^2).toLaurent).coeff j=
      if j=0 then 0 else ((actualAK p : K[X])^2).coeff (p+j) := by
  rw [fullStrictPositive_polynomial_coeff,one_mul]

theorem actual_AK_square_strict_weight (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullStrictTail p 1 ((actualAK p : K[X])^2).toLaurent=
      8*((nativeB p : K[X]).eval 4)^2+(1/4 : K)*((nativeB p : K[X]).eval (1/4))^2+
        2*fullStrictTail p 0 ((nativeB p)*(nativeL p)).toLaurent+
          fullStrictTail p 1 ((nativeL p)^2).toLaurent := by
  have h4p : (4 : K)^p=4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K:=K) p 4
  have hap : (1/4 : K)^p=1/4 := by rw [one_div,inv_pow,h4p]
  rw [actual_AK_phase_source p hp,fullStrictTail_two_band_square p (by omega),h4p,hap]
  ring

private theorem nativeBase_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (C (nativeConstant p)-C (33/5 : K)*Dstar p : K[X]).natDegree≤(p-1)/2-1 := by
  apply (natDegree_sub_le _ _).trans
  exact max_le (by simp) ((natDegree_C_mul_le _ _).trans (Dstar_degree p hp))

/-- The low square discards only proved low degrees; both complete high products remain. -/
theorem nativeL_square_strict_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullStrictPositive p 1 ((nativeL p : K[X])^2).toLaurent=
      -C (66/5 : K)*fullStrictPositive p 1 ((finiteMixedLog p)*Dstar p).toLaurent+
        fullStrictPositive p 1 ((finiteMixedLog p)^2).toLaurent := by
  have hbase := nativeBase_degree (K:=K) p hp
  have hsmall : fullStrictPositive p 1
      (((C (nativeConstant p)-C (33/5 : K)*Dstar p : K[X])^2+
        C (2*nativeConstant p)*finiteMixedLog p).toLaurent)=0 := by
    apply fullStrictPositive_small
    rw [one_mul]
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [pow_two]
      exact natDegree_mul_le.trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans ((finiteMixedLog_degree p).trans (by omega))
  have he : (nativeL p : K[X])^2=
      ((C (nativeConstant p)-C (33/5 : K)*Dstar p)^2+
        C (2*nativeConstant p)*finiteMixedLog p)-
          C (66/5 : K)*(finiteMixedLog p*Dstar p)+(finiteMixedLog p)^2 := by
    rw [nativeL_mixed_source]
    rw [show C (66/5 : K) = C (2 : K)*C (33/5 : K) by
      rw [← map_mul]; congr 1; ring]
    simp only [map_mul,map_ofNat]
    ring
  rw [he,map_add,map_sub,fullStrictPositive_add,fullStrictPositive_sub,hsmall,
    zero_sub,map_mul,Polynomial.toLaurent_C,fullStrictPositive_C_mul]
  ring

theorem nativeL_square_strict_weight (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    fullStrictTail p 1 ((nativeL p : K[X])^2).toLaurent=
      -(66/5 : K)*fullStrictTail p 1 ((finiteMixedLog p)*Dstar p).toLaurent-
        (6/25 : K)*WPFiniteField.R p 16 := by
  rw [fullStrictTail,nativeL_square_strict_source p hp]
  simp only [eval_add,eval_mul,eval_neg,eval_C,fullStrictTail]
  have hf := finiteMixedLog_square_strict_tail (K:=K) p hp
  dsimp only [fullStrictTail] at hf
  linear_combination hf

theorem actual_AK_square_strict_weight_low_products (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictTail p 1 ((actualAK p : K[X])^2).toLaurent=
      8*((nativeB p : K[X]).eval 4)^2+(1/4 : K)*((nativeB p : K[X]).eval (1/4))^2+
        2*fullStrictTail p 0 ((nativeB p)*(nativeL p)).toLaurent-
          (66/5 : K)*fullStrictTail p 1 ((finiteMixedLog p)*Dstar p).toLaurent-
            (6/25 : K)*WPFiniteField.R p 16 := by
  rw [actual_AK_square_strict_weight p hp,nativeL_square_strict_weight p hp]
  ring

private theorem polynomial_reciprocal_strict_small (p k : ℕ) (P Q : K[X])
    (hP : P.natDegree≤k*p) : fullStrictPositive p k (P.toLaurent*invert Q.toLaurent)=0 := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
    rw [map_add,map_add,mul_add,fullStrictPositive_add,hQ,hR,zero_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul,Polynomial.toLaurent_C,Polynomial.toLaurent_X_pow,
      invert_C,invert_T]
    rw [show P.toLaurent*(LaurentPolynomial.C c*T (-(n : ℤ)))=
      LaurentPolynomial.C c*T (-(n : ℤ))*P.toLaurent by ring]
    ext j
    rw [fullStrictPositive_coeff,coeff_zero]
    by_cases hj : j=0
    · rw [if_pos hj]
    · rw [if_neg hj]
      have hs := WPFiniteJCarrier.shifted_coeff c (-(n : ℤ)) (((k*p+j : ℕ) : ℤ)) P.toLaurent
      rw [hs,show ((k*p+j : ℕ) : ℤ)- -(n : ℤ)=((k*p+j+n : ℕ) : ℤ) by omega,
        WPFiniteJCarrier.toLaurent_coeff_nat,coeff_eq_zero_of_natDegree_lt (by omega),mul_zero]

private theorem reciprocal_shift_trunc_small (p : ℕ) (P Q : K[X]) (hQ : Q.natDegree<p) :
    LaurentPolynomial.trunc (T (-(p : ℤ))*(Q.toLaurent*invert P.toLaurent))=0 := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
    rw [map_add,map_add,mul_add,mul_add,map_add,hP,hR,zero_add]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul,Polynomial.toLaurent_C,Polynomial.toLaurent_X_pow,
      invert_C,invert_T]
    rw [show T (-(p : ℤ))*(Q.toLaurent*(LaurentPolynomial.C c*T (-(n : ℤ))))=
      LaurentPolynomial.C c*T (-((p+n : ℕ) : ℤ))*Q.toLaurent by
        rw [show ((p+n : ℕ) : ℤ)=(p : ℤ)+(n : ℤ) by omega,neg_add,
          LaurentPolynomial.T_add]
        ring]
    ext j
    rw [WPFiniteJWeightedResidue.trunc_coeff,coeff_zero,
      WPFiniteJCarrier.shifted_coeff,
      show (j : ℤ)- -((p+n : ℕ) : ℤ)=((j+p+n : ℕ) : ℤ) by omega,
      WPFiniteJCarrier.toLaurent_coeff_nat,coeff_eq_zero_of_natDegree_lt (by omega),mul_zero]

theorem nativeL_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (nativeL p : K[X]).natDegree≤p-1 := by
  rw [nativeL_mixed_source]
  apply (natDegree_add_le _ _).trans
  exact max_le ((nativeBase_degree p hp).trans (by omega)) (finiteMixedLog_degree p)

theorem actual_AK_Dstar_inverse_strict_one_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictPositive p 1 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      C (12/5 : K)*fullStrictPositive p 0 ((Dstar p).toLaurent*invert (Dstar p).toLaurent) := by
  rw [actual_AK_phase_source p hp,map_add,map_mul,Polynomial.toLaurent_X_pow,add_mul,
    fullStrictPositive_add,mul_assoc]
  have he := fullStrictPositive_phase_shift p 1 1 (by omega)
    ((nativeB p : K[X]).toLaurent*invert (Dstar p).toLaurent)
  simp only [one_mul,Nat.sub_self] at he
  rw [he,polynomial_reciprocal_strict_small p 1 _ _ ((nativeL_degree p hp).trans (by omega)),add_zero]
  have hb : (nativeB p : K[X]).toLaurent*invert (Dstar p).toLaurent=
      LaurentPolynomial.C (12/5 : K)*((Dstar p).toLaurent*invert (Dstar p).toLaurent)-
        (C (4*WPFiniteNC122.q p/5) : K[X]).toLaurent*invert (Dstar p).toLaurent := by
    simp only [nativeB,map_sub,map_mul,Polynomial.toLaurent_C]
    ring
  have hconst := polynomial_reciprocal_strict_small p 0
    (C (4*WPFiniteNC122.q p/5) : K[X]) (Dstar p) (by simp)
  rw [hb,fullStrictPositive_sub,fullStrictPositive_C_mul,hconst,sub_zero]

theorem actual_AK_Dstar_inverse_strict_one_weight (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictTail p 1 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      (12/5 : K)*((9/10 : K)*((Dstar p : K[X]).eval (1/4)+(Dstar p : K[X]).eval 4)^2-
        ((Dstar p : K[X]).eval (1/4))^2/2-((Dstar p : K[X]).eval 4)^2+
          3*((Dstar p : K[X]).coeff 0)^2/2) := by
  rw [fullStrictTail,actual_AK_Dstar_inverse_strict_one_source p hp]
  simp only [eval_mul,eval_C]
  have ht := Dstar_reciprocal_product_strict_weighted (K:=K) p hp
  dsimp only [fullStrictTail] at ht
  linear_combination (12/5 : K)*ht

theorem actual_AK_Dstar_strict_zero_weight (p : ℕ) [Fact p.Prime] [CharP K p] :
    fullStrictTail p 0 ((actualAK p : K[X])*Dstar p).toLaurent=
      2*(actualAK p : K[X]).eval 4*(Dstar p).eval 4+
        (actualAK p : K[X]).eval (1/4)*(Dstar p).eval (1/4)-
          3*(actualAK p : K[X]).coeff 0*(Dstar p).coeff 0 := by
  rw [fullStrictTail_zero_polynomial]
  simp only [eval_mul,mul_coeff_zero]
  ring

/-- The original complete nonpositive projection contains both full triangles. -/
theorem actual_AK_Dstar_inverse_nonpositive_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    LaurentPolynomial.trunc (invert ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent))=
      C (nativeConstant p)*Dstar p-C (33/5 : K)*nonpositiveDstarTriangle p+
        nonpositiveMixedTriangle p := by
  have hD : (Dstar p : K[X]).natDegree<p := (Dstar_degree p hp).trans_lt (by omega)
  have he : invert ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      T (-(p : ℤ))*((Dstar p).toLaurent*invert (nativeB p).toLaurent)+
        (LaurentPolynomial.C (nativeConstant p)*(Dstar p).toLaurent-
          LaurentPolynomial.C (33/5 : K)*invert ((Dstar p).toLaurent*invert (Dstar p).toLaurent))+
            invert ((finiteMixedLog p).toLaurent*invert (Dstar p).toLaurent) := by
    rw [actual_AK_phase_source p hp,nativeL_mixed_source]
    simp only [map_mul,map_add,map_sub,Polynomial.toLaurent_X_pow,Polynomial.toLaurent_C,
      invert_C,invert_T,LaurentPolynomial.involutive_invert (Dstar p : K[X]).toLaurent]
    ring
  rw [he,map_add,map_add,reciprocal_shift_trunc_small p _ _ hD,zero_add,map_sub,
    WPFiniteJWeightedResidue.trunc_C_mul,trunc_toLaurent,
    WPFiniteJWeightedResidue.trunc_C_mul]
  rfl

theorem actual_AK_Dstar_inverse_strict_zero_weight (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictTail p 0 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      2*(actualAK p : K[X]).eval 4*(Dstar p).eval (1/4)+
        (actualAK p : K[X]).eval (1/4)*(Dstar p).eval 4-
          nativeConstant p*(2*(Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4)+
      (33/5 : K)*((3/5 : K)*((Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4)^2-
        ((Dstar p : K[X]).eval (1/4))^2-((Dstar p : K[X]).eval 4)^2/2-
          3*((Dstar p : K[X]).coeff 0)^2/2)-
      (2/15 : K)*((1/4 : K)*(2*branchH p (1/4) 4+branchH p 4 4)-
        4*(2*branchH p (1/4) (1/4)+branchH p 4 (1/4))) := by
  have h4 : (4 : K)≠0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K)=4 := rfl
  rw [fullStrictTail_zero_projection p _ v hv]
  rw [actual_AK_Dstar_inverse_nonpositive_source p hp]
  simp only [map_mul,WPFiniteJWeightedResidue.inversion_eval,
    LaurentPolynomial.eval₂_toLaurent,eval₂_id]
  simp only [one_div,Units.val_inv_eq_inv_val,hv,inv_inv]
  simp only [eval_add,eval_sub,eval_mul,eval_C]
  have hd := nonpositiveDstarTriangle_weighted (K:=K) p hp
  have hf := nonpositiveMixedTriangle_weighted (K:=K) p hp
  simp only [one_div] at hd hf
  linear_combination (33/5 : K)*hd-hf

private theorem LPsrc_proper_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (WPFiniteKSource.LPsrc p : K[X]).eval 1=0 ∧ (WPFiniteKSource.LPsrc p : K[X]).eval (-1)=0 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hE : WPFiniteField.E p (1 : K)=-WPFiniteNC122.q p := by
    have h := (WPFiniteLoop.L_rational_ends (K:=K) p hp).1
    have he := WPFiniteLoop.L_square_eq_twice_E (K:=K) p hp 1
    rw [one_pow] at he
    rw [he] at h
    apply mul_left_cancel₀ h2
    simpa only [WPFiniteNC122.q,mul_neg,neg_mul] using h
  have heven : WPFiniteField.E p (-1 : K)=WPFiniteField.E p 1 := by
    simp only [WPFiniteField.E,neg_neg]
    ring
  rw [WPFiniteKSource.LPsrc_eval,WPFiniteKSource.LPsrc_eval]
  simp only [WPFiniteNC122.L,heven,hE,add_neg_cancel]
  constructor <;> trivial

/-- Both native proper ends follow from the unchanged LV conic and actual harmonic source. -/
theorem actual_AK_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (actualAK p : K[X]).eval (1/4)=-WPFiniteNC122.h p ∧
      (actualAK p : K[X]).eval 4=-WPFiniteNC122.h p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  obtain ⟨hl,hln⟩ := LPsrc_proper_ends (K:=K) p hp
  have hc : (WPFiniteJHighCoefficient.conic : K[X]).eval (1/2)=1/4 := by
    simp only [WPFiniteJHighCoefficient.conic,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    field_simp [h2,h4]
    ring
  have ht : (WPFiniteCubicLog.Tc : K[X]).eval (1/2)=-1 := by
    simp only [WPFiniteCubicLog.Tc,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X]
    field_simp [h2]
    ring
  have ha := congrArg (fun P : K[X] => P.eval (1/2)) (WPFiniteLVSource.LV_conic p hp)
  rw [eval_comp,hc,eval_comp,ht,hln] at ha
  have hb := congrArg (fun P : K[X] => P.eval 1) (WPFiniteLVSource.LV_conic p hp)
  simp only [eval_comp,WPFiniteJHighCoefficient.conic,WPFiniteCubicLog.Tc,
    eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one,one_pow] at hb
  norm_num only [show (5*1-1 : K)=4 by ring,show (4*1-3*1 : K)=1 by ring] at hb
  rw [hl] at hb
  rw [actual_AK_source p hp,actual_harmonic_map p hp]
  simp only [eval_sub,eval_C,ha,hb,zero_sub]
  constructor <;> trivial

/-- D0 is obtained from the original finite entropy polynomial at the actual fifth root. -/
theorem Dstar_origin_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) : (Dstar p : K[X]).coeff 0=-WPFifthEntropy.C p u/3 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).eval 0=1/5 := by
    simp only [WPFiniteWSource.squaredCoordinate,eval_mul,eval_C,eval_add,eval_X,
      eval_one,zero_add,one_div,mul_one]
  rw [coeff_zero_eq_eval_zero,Dstar,eval_mul,eval_neg,eval_C,eval_comp,hs,
    WPFiniteWSource.deltaE_fifth p hp u hu]
  ring

/-- The actual origin retains D0 before any specialization to the fifth carrier. -/
theorem actual_AK_origin_retained (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (actualAK p : K[X]).coeff 0=nativeConstant p-(33/5 : K)*(Dstar p : K[X]).coeff 0 := by
  have hLP : (LP p : K[X]).eval 0 = 0 := by
    rw [LP, eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
    simp only [eval_mul, eval_C, eval_pow, eval_X, zero_pow hj0, mul_zero]
  have hz : (finiteMixedLog p : K[X]).eval 0=0 := by
    simp only [finiteMixedLog,eval_mul,eval_C,eval_add,eval_neg,eval_comp,eval_X,
      mul_zero,hLP,zero_add]
  rw [coeff_zero_eq_eval_zero,actual_AK_phase_source p hp,nativeL_mixed_source]
  simp only [eval_add,eval_mul,eval_pow,eval_X,zero_pow (by omega : p≠0),zero_mul,
    eval_C,eval_sub,hz,add_zero,zero_add,coeff_zero_eq_eval_zero]

noncomputable def nativeTau (p : ℕ) : K :=
  (4*WPFiniteNC122.q p-3*(WPFiniteInversion.integerFermatQuotient p 3 : K))/5

theorem nativeB_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (nativeB p : K[X]).eval (1/4)=nativeTau p ∧
      (nativeB p : K[X]).eval 4=-2*nativeTau p := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K)≠0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  simp only [nativeB,eval_sub,eval_mul,eval_C,ha,hb,nativeTau,WPFiniteNC122.h]
  constructor <;> field_simp [h2,h3,h5,h6] <;> ring

theorem nativeB_origin_fifth (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    (nativeB p : K[X]).coeff 0=-4*(WPFifthEntropy.C p u+WPFiniteNC122.q p)/5 := by
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  rw [nativeB,coeff_sub,coeff_C_mul,coeff_C_zero,Dstar_origin_fifth p hp u hu]
  field_simp [h3,h5]
  ring

theorem nativeL_endpoints (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (nativeL p : K[X]).eval (1/4)=-WPFiniteNC122.h p-nativeTau p/4 ∧
      (nativeL p : K[X]).eval 4=-WPFiniteNC122.h p+8*nativeTau p := by
  have h4p : (4 : K)^p=4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K:=K) p 4
  have hap : (1/4 : K)^p=1/4 := by rw [one_div,inv_pow,h4p]
  obtain ⟨ha,hb⟩ := actual_AK_endpoints (K:=K) p hp
  obtain ⟨hba,hbb⟩ := nativeB_endpoints (K:=K) p hp
  rw [actual_AK_phase_source p hp] at ha hb
  simp only [eval_add,eval_mul,eval_pow,eval_X,h4p,hap,hba,hbb] at ha hb
  constructor
  · linear_combination ha
  · linear_combination hb

theorem nativeL_origin_actual (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (nativeL p : K[X]).coeff 0=(actualAK p : K[X]).coeff 0 := by
  have he := congrArg (fun P : K[X] => P.eval 0) (actual_AK_phase_source p hp)
  simp only [eval_add,eval_mul,eval_pow,eval_X,zero_pow (by omega : p≠0),zero_mul,zero_add] at he
  simpa only [coeff_zero_eq_eval_zero] using he.symm

/-- The weighted complete square is NC126's actual source, retaining the original a0. -/
theorem actual_AK_square_NC126 (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    fullStrictTail p 1 ((actualAK p : K[X])^2).toLaurent=
      6*WPFiniteNC122.h p*nativeTau p-129*(nativeTau p)^2/4+
        24*(WPFifthEntropy.C p u+WPFiniteNC122.q p)*WPFiniteNC122.a0 p u/5-
          (66/5 : K)*fullStrictTail p 1 ((finiteMixedLog p)*Dstar p).toLaurent-
            (6/25 : K)*WPFiniteField.R p 16 := by
  have h4 : (4 : K)≠0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hba,hbb⟩ := nativeB_endpoints (K:=K) p hp
  obtain ⟨hla,hlb⟩ := nativeL_endpoints (K:=K) p hp
  rw [actual_AK_square_strict_weight_low_products p hp,fullStrictTail_zero_polynomial]
  simp only [eval_mul,mul_coeff_zero,hba,hbb,hla,hlb]
  rw [nativeB_origin_fifth p hp u hu,nativeL_origin_actual p hp,coeff_zero_eq_eval_zero,
    actual_AK_origin p hp u hu]
  field_simp [h4,h5]
  ring

theorem actual_AK_Dstar_strict_one_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictPositive p 1 ((actualAK p : K[X])*Dstar p).toLaurent=
      fullStrictPositive p 0 ((nativeB p)*Dstar p).toLaurent+
        fullStrictPositive p 1 ((finiteMixedLog p)*Dstar p).toLaurent := by
  have hD := Dstar_degree (K:=K) p hp
  have hsmall : fullStrictPositive p 1
      (C (nativeConstant p)*Dstar p-C (33/5 : K)*(Dstar p)^2).toLaurent=0 := by
    apply fullStrictPositive_small
    rw [one_mul]
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_C_mul_le _ _).trans (hD.trans (by omega))
    · rw [pow_two]
      exact (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans (by omega))
  have he : (actualAK p : K[X])*Dstar p=X^p*(nativeB p*Dstar p)+
      (C (nativeConstant p)*Dstar p-C (33/5 : K)*(Dstar p)^2)+finiteMixedLog p*Dstar p := by
    rw [actual_AK_phase_source p hp,nativeL_mixed_source]
    ring
  rw [he,map_add,map_add,fullStrictPositive_add,fullStrictPositive_add,
    fullStrictPositive_Xphase,hsmall,add_zero]

theorem actual_AK_Dstar_strict_one_weight (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    fullStrictTail p 1 ((actualAK p : K[X])*Dstar p).toLaurent=
      2*(nativeB p : K[X]).eval 4*(Dstar p).eval 4+
        (nativeB p : K[X]).eval (1/4)*(Dstar p).eval (1/4)-
          3*(nativeB p : K[X]).coeff 0*(Dstar p).coeff 0+
            fullStrictTail p 1 ((finiteMixedLog p)*Dstar p).toLaurent := by
  rw [fullStrictTail,actual_AK_Dstar_strict_one_source p hp]
  simp only [eval_add]
  have hz := fullStrictTail_zero_polynomial p ((nativeB p : K[X])*Dstar p)
  dsimp only [fullStrictTail] at hz
  simp only [eval_mul,mul_coeff_zero] at hz
  dsimp only [fullStrictTail]
  linear_combination hz

/-- NC126d's polynomial mixed tail contains the genuine original a0*C contribution. -/
theorem actual_AK_Dstar_NC126d (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (u : K) (hu : u^2=1/5) :
    fullStrictTail p 0 ((actualAK p : K[X])*Dstar p).toLaurent=
      -3*WPFiniteNC122.h p*(WPFiniteInversion.integerFermatQuotient p 3 : K)/4+
        WPFiniteNC122.a0 p u*WPFifthEntropy.C p u := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  obtain ⟨ha,hb⟩ := actual_AK_endpoints (K:=K) p hp
  obtain ⟨hda,hdb⟩ := Dstar_endpoints (K:=K) p hp
  rw [actual_AK_Dstar_strict_zero_weight,ha,hb,hda,hdb,
    Dstar_origin_fifth p hp u hu,coeff_zero_eq_eval_zero,actual_AK_origin p hp u hu]
  unfold WPFiniteNC122.h
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h8 : (8 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 3 0 0 using 1; norm_num
  have h12 : (12 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 1 0 using 1; norm_num
  field_simp [h2,h3,h4,h6,h8,h12]
  ring

/-- The strict reciprocal p-tail is derived from the whole cross-product and literal D0. -/
theorem actual_AK_Dstar_inverse_NC126d (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    fullStrictTail p 1 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      -(14/25 : K)*(WPFiniteNC122.q p)^2+
        (39/25 : K)*WPFiniteNC122.q p*(WPFiniteInversion.integerFermatQuotient p 3 : K)-
          (27/50 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2+
            (2/5 : K)*(WPFifthEntropy.C p u)^2 := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  obtain ⟨ha,hb⟩ := Dstar_endpoints (K:=K) p hp
  rw [actual_AK_Dstar_inverse_strict_one_weight p hp,ha,hb,Dstar_origin_fifth p hp u hu]
  unfold WPFiniteNC122.h
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h6 : (6 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h10 : (10 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 0 1 using 1; norm_num
  have h12 : (12 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 1 0 using 1; norm_num
  have h25 : (25 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 0 0 2 using 1; norm_num
  have h50 : (50 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 0 2 using 1; norm_num
  field_simp [h2,h3,h5,h6,h10,h12,h25,h50]
  ring

/-- Both complete NC126d triangles retain the original additive constant and its -h. -/
theorem actual_AK_Dstar_inverse_zero_NC126d (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    fullStrictTail p 0 ((actualAK p : K[X]).toLaurent*invert (Dstar p).toLaurent)=
      (33/5 : K)*((3/5 : K)*((Dstar p : K[X]).eval (1/4)+(Dstar p).eval 4)^2-
        ((Dstar p : K[X]).eval (1/4))^2-((Dstar p : K[X]).eval 4)^2/2-
          (WPFifthEntropy.C p u)^2/6)+
        (11*WPFiniteNC122.q p/5-3*(WPFiniteInversion.integerFermatQuotient p 5 : K)/2)*
          WPFiniteNC122.q p-
      (2/15 : K)*((1/4 : K)*(2*branchH p (1/4) 4+branchH p 4 4)-
        4*(2*branchH p (1/4) (1/4)+branchH p 4 (1/4))) := by
  have hn (n : ℕ) (hpos : 0<n) (hlt : n<p) : (n : K)≠0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos,hlt⟩)
  obtain ⟨ha,hb⟩ := actual_AK_endpoints (K:=K) p hp
  obtain ⟨hda,hdb⟩ := Dstar_endpoints (K:=K) p hp
  rw [actual_AK_Dstar_inverse_strict_zero_weight p hp,ha,hb,
    Dstar_origin_fifth p hp u hu]
  rw [hda,hdb]
  unfold nativeConstant
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 0 0 using 1; norm_num
  have h6 : (6 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 1 1 0 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 0 1 1 using 1; norm_num
  have h60 : (60 : K) ≠ 0 := by
    convert native_smooth_ne_zero (K:=K) p hp 2 1 1 using 1; norm_num
  field_simp [h2,h3,h5,h4,h6,h15,h60]
  ring

end WPFieldAssembly.ActualBpairNativeTail
