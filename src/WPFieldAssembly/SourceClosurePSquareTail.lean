import WPFieldAssembly.SourceClosurePSquarePhases
import WPFiniteABSourceTail
import WPFieldAssembly.SourceClosureVbalFullLogTail

open scoped Polynomial
open Polynomial WPFiniteAffineLog WPFiniteProductTail WPFiniteABSourceTail
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosurePSquarePhases

namespace WPFieldAssembly.SourceClosurePSquareTail

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: the W part of corrected NC118f, with its
   original endpoint orientation. strictTail retains exactly p < j < 2p
   and shifts by p; the actual products have no higher coefficients.
   The degree-p coefficient is retained elsewhere.
   Both full logarithms, the W origin and all primitive diagonals are
   used. The log-square value is imported from its full finite proof.
   No generated input or normalized scalar assignment occurs here. -/

noncomputable def originalLogDifference (p : ℕ) : K[X] :=
  (LP p).comp (Polynomial.C 4*X)-(LP p).comp (Polynomial.C (1/4)*X)

noncomputable def originalPSquareHRow (p : ℕ) : K :=
  -4*((originalHa p).eval (1/4)+2*(originalHb p).eval (1/4)-3*(originalHx p).eval (1/4))+
    (1/4 : K)*((originalHa p).eval 4+2*(originalHb p).eval 4-3*(originalHx p).eval 4)

theorem original_log_difference_degree (p : ℕ) :
    (originalLogDifference p : K[X]).natDegree≤p-1 := by
  have hscale (c : K) : ((LP p : K[X]).comp (Polynomial.C c*X)).natDegree≤p-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [LP_scaled_coeff,if_neg (by omega)]
  exact (natDegree_sub_le _ _).trans (max_le (hscale 4) (hscale (1/4)))

theorem actual_W_log_difference_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    strictTail p ((WPFiniteWSource.W p : K[X])*originalLogDifference p)=
      Polynomial.C (-4 : K)*primitiveDifferenceP p (WPFiniteWSource.W p) (1/4)+
        Polynomial.C (1/4 : K)*primitiveDifferenceP p (WPFiniteWSource.W p) 4 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1/4 : K)≠0 := one_div_ne_zero h4
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : K)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have hW : (WPFiniteWSource.W p : K[X]).natDegree<p := by
    have hd := WPFiniteWSource.W_degree (K:=K) p hp
    omega
  rw [originalLogDifference,mul_sub,strictTail_sub p (by omega),
    strict_product_tail p _ hW (WPFiniteWSource.W_origin p) 4 h4,
    strict_product_tail p _ hW (WPFiniteWSource.W_origin p) (1/4) ha,h4p,hap]
  simp only [one_div,inv_inv,map_neg]
  ring

/-- The endpoint weights are a+2b, with the primitive arguments in their original order. -/
theorem actual_W_log_difference_tail_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p ((WPFiniteWSource.W p : K[X])*originalLogDifference p)).eval (1/4)+
      2*(strictTail p ((WPFiniteWSource.W p : K[X])*originalLogDifference p)).eval 4=
      originalPSquareHRow p := by
  rw [actual_W_log_difference_tail p hp]
  simp only [eval_add,eval_mul,eval_C,primitiveDifference_eval]
  unfold originalPSquareHRow originalHa originalHb originalHx
  simp only [unitPrimitiveP_eval,unitPrimitive_origin]
  ring

/-- Only the complete logarithm-square tail remains after the actual W contribution is removed. -/
theorem actual_original_Pminus_square_tail (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    strictTail p ((originalPMinus p : K[X])^2)=
      Polynomial.C (-8/(15*epsilon p) : K)*
        strictTail p (WPFiniteWSource.W p*originalLogDifference p)+
      Polynomial.C (4/225 : K)*strictTail p ((originalLogDifference p)^2) := by
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by
    rw [show (15 : K)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h225 : (225 : K)≠0 := by
    rw [show (225 : K)=15*15 by ring]
    exact mul_ne_zero h15 h15
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  let w : K := 4*(WPFiniteNC122.q p-descendedC p)/15
  let B : K[X] := Polynomial.C w-Polynomial.C (2/epsilon p)*WPFiniteWSource.W p
  have hB : B.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree := by
    dsimp only [B]
    exact (natDegree_sub_le _ _).trans
      (max_le (by simp) (natDegree_C_mul_le _ _))
  have hB2 : (B^2).natDegree≤p := by
    have hd := WPFiniteWSource.W_degree (K:=K) p hp
    have hh := (natDegree_pow_le (p:=B) (n:=2)).trans (Nat.mul_le_mul_left 2 hB)
    omega
  have hlog : (Polynomial.C (2*w*(2/15 : K))*originalLogDifference p).natDegree≤p :=
    (natDegree_C_mul_le _ _).trans ((original_log_difference_degree p).trans (by omega))
  have hrow : (originalPMinus p : K[X])^2=B^2+
      Polynomial.C (2*w*(2/15 : K))*originalLogDifference p+
      Polynomial.C (-8/(15*epsilon p) : K)*(WPFiniteWSource.W p*originalLogDifference p)+
      Polynomial.C (4/225 : K)*(originalLogDifference p)^2 := by
    dsimp only [B,w]
    unfold originalPMinus originalLogDifference
    have hcross : -(2*(2/epsilon p)*(2/15 : K))= -8/(15*epsilon p) := by
      field_simp [heps,h15]
      ring
    have hsquare : (2/15 : K)^2=4/225 := by
      field_simp [h15,h225]
      ring
    rw [←hsquare,←hcross]
    simp only [map_mul,map_pow,map_neg,map_ofNat]
    ring
  rw [hrow,strictTail_add p (by omega),strictTail_add p (by omega),
    strictTail_add p (by omega),strictTail_low p (by omega) _ hB2,
    strictTail_low p (by omega) _ hlog,zero_add,zero_add,
    strictTail_C_mul p (by omega),strictTail_C_mul p (by omega)]

theorem actual_original_Pminus_square_tail_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p ((originalPMinus p : K[X])^2)).eval (1/4)+
      2*(strictTail p ((originalPMinus p : K[X])^2)).eval 4=
      (-8/(15*epsilon p) : K)*originalPSquareHRow p+
        (4/225 : K)*((strictTail p ((originalLogDifference p : K[X])^2)).eval (1/4)+
          2*(strictTail p ((originalLogDifference p : K[X])^2)).eval 4) := by
  rw [actual_original_Pminus_square_tail p hp]
  simp only [eval_add,eval_mul,eval_C]
  have h := actual_W_log_difference_tail_ends (K:=K) p hp
  linear_combination (-8/(15*epsilon p) : K)*h

/-- Corrected NC118f is the original minus-square tail, with both ends and its full cutoff. -/
theorem actual_original_Pminus_square_tail_finite (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (strictTail p ((originalPMinus p : K[X])^2)).eval (1/4)+
      2*(strictTail p ((originalPMinus p : K[X])^2)).eval 4=
      (-8/(15*epsilon p) : K)*originalPSquareHRow p+
        11*WPFiniteField.ell p (16 : K)^2/1200 := by
  have hlog : (strictTail p ((originalLogDifference p : K[X])^2)).eval (1/4)+
      2*(strictTail p ((originalLogDifference p : K[X])^2)).eval 4=
      33*WPFiniteField.ell p (16 : K)^2/64 := by
    simpa only [originalLogDifference] using
      SourceClosureVbalFullLogTail.actual_full_log_difference_square_tail (K:=K) p hp
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h64 : (64 : K)≠0 := by
    rw [show (64 : K)=2^6 by ring]
    exact pow_ne_zero _ h2
  have h225 : (225 : K)≠0 := by
    rw [show (225 : K)=3^2*5^2 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h5)
  have h1200 : (1200 : K)≠0 := by
    rw [show (1200 : K)=2^4*3*5^2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) (pow_ne_zero _ h5)
  have hc : (4/225 : K)*(33/64)=11/1200 := by
    field_simp [h225,h64,h1200]
    ring
  rw [actual_original_Pminus_square_tail_ends p hp,hlog]
  calc
    _ = (-8/(15*epsilon p) : K)*originalPSquareHRow p+
        ((4/225 : K)*(33/64))*WPFiniteField.ell p (16 : K)^2 := by ring
    _ = _ := by rw [hc]; ring

end WPFieldAssembly.SourceClosurePSquareTail
