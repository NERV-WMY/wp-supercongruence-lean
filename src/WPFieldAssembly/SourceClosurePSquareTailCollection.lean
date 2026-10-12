import WPFieldAssembly.SourceClosurePSquareTail
import WPFieldAssembly.SourceClosurePSquareWindowCollection
import WPFieldAssembly.SourceClosureVbalFullLogReflection

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteAffineLog WPFiniteProductTail WPFiniteABSourceTail
  WPFieldAssembly.ActualUVSourceIdentification WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosurePSquarePhases WPFieldAssembly.SourceClosurePSquareTail
  WPFieldAssembly.SourceClosurePSquareWindowCollection
  WPFieldAssembly.SourceClosureVbalFullLogReflection

namespace WPFieldAssembly.SourceClosurePSquareTailCollection

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: the tail combination is that of the full three
   original weighted windows, not a low-degree replacement of P squared.
   Its W*logTrace coefficient cancels as an exact polynomial identity.
   Every finite log and strict tail has its specified full cutoff.
   The actual J_H source is retained and no NC77 scalar is assigned. -/

private theorem pairedTail_low (p : ℕ) (hp : 0<p) (a b : K) (F : K[X])
    (hF : F.natDegree≤p) : pairedTail p a b F=0 := by
  rw [pairedTail,strictTail_low p hp F hF]
  simp

/-- Only the original W/log-difference row survives among the mixed W/log tails. -/
theorem actual_original_P_square_tail_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    6*pairedTail p (1/4 : K) 4 (originalPMiddle p*originalPMinus p)+
      (9/2 : K)*pairedTail p (1/4 : K) 4 ((originalPMiddle p)^2)+
      9*pairedTail p (1/4 : K) 4 (originalPPlus p*originalPMinus p)+
      (129/4 : K)*pairedTail p (1/4 : K) 4 (originalPPlus p*originalPMiddle p)=
      (22/(5*epsilon p) : K)*originalPSquareHRow p+
        WPFiniteField.R p (16 : K)/10-WPFiniteField.ell p (16 : K)^2/100 := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by rw [show (15 : K)=3*5 by ring]; exact mul_ne_zero h3 h5
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  have h600 : (600 : K)≠0 := by
    rw [show (600 : K)=2^3*3*5^2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) h3) (pow_ne_zero _ h5)
  have h75 : (75 : K)≠0 := by
    rw [show (75 : K)=3*5^2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  let u : K := -4*(WPFiniteNC122.q p+descendedC p)/15
  let v : K := 17*descendedC p/15
  let w : K := 4*(WPFiniteNC122.q p-descendedC p)/15
  let A : K[X] := Polynomial.C u-Polynomial.C (2/epsilon p)*WPFiniteWSource.W p
  let B : K[X] := Polynomial.C v+Polynomial.C (17/(2*epsilon p))*WPFiniteWSource.W p
  let C : K[X] := Polynomial.C w-Polynomial.C (2/epsilon p)*WPFiniteWSource.W p
  let La : K[X] := (LP p).comp (Polynomial.C (1/4 : K)*X)
  let Lb : K[X] := (LP p).comp (Polynomial.C (4 : K)*X)
  let L0 : K[X] := Polynomial.C 6*(B*C)+Polynomial.C (9/2 : K)*B^2+
    Polynomial.C 9*(A*C)+Polynomial.C (129/4 : K)*(A*B)
  let L1 : K[X] := Polynomial.C ((2/15 : K)*(6*v+9*u))*originalLogDifference p+
    Polynomial.C ((2/15 : K)*(6*w+9*v+129*u/4))*logTrace p
  have hW := WPFiniteWSource.W_degree (K:=K) p hp
  have hbase (x y : K) :
      (Polynomial.C x+Polynomial.C y*WPFiniteWSource.W p).natDegree≤
        (WPFiniteWSource.W p : K[X]).natDegree :=
    (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hA : A.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree := by
    dsimp only [A]
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hB : B.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree := hbase _ _
  have hC : C.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree := by
    dsimp only [C]
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hprod (F G : K[X]) (hF : F.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree)
      (hG : G.natDegree≤(WPFiniteWSource.W p : K[X]).natDegree) :
      (F*G).natDegree≤p :=
    (natDegree_mul_le (p:=F) (q:=G)).trans (by omega)
  have hB2 : (B^2).natDegree≤p := by
    rw [pow_two]
    exact hprod B B hB hB
  have hL0 : L0.natDegree≤p := by
    dsimp only [L0]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le
          ((natDegree_C_mul_le _ _).trans (hprod B C hB hC))
          ((natDegree_C_mul_le _ _).trans hB2)))
        ((natDegree_C_mul_le _ _).trans (hprod A C hA hC))))
      ((natDegree_C_mul_le _ _).trans (hprod A B hA hB)))
  have hL1 : L1.natDegree≤p := by
    dsimp only [L1]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans ((original_log_difference_degree p).trans (by omega)))
      ((natDegree_C_mul_le _ _).trans ((logTrace_degree p).trans (by omega))))
  have hrow :
      Polynomial.C 6*(originalPMiddle p*originalPMinus p)+
        Polynomial.C (9/2 : K)*(originalPMiddle p)^2+
        Polynomial.C 9*(originalPPlus p*originalPMinus p)+
        Polynomial.C (129/4 : K)*(originalPPlus p*originalPMiddle p)=
      L0+L1+Polynomial.C (22/(5*epsilon p) : K)*(WPFiniteWSource.W p*originalLogDifference p)+
        Polynomial.C (-13/600 : K)*Lb^2+Polynomial.C (64/75 : K)*La^2+
        Polynomial.C (22/75 : K)*(Lb*La) := by
    have hwl : 6*(-(2/epsilon p))*(2/15 : K)+
        (9/2)*(2*(17/(2*epsilon p))*(2/15))+
        (129/4)*(-(2/epsilon p)*(2/15))=0 := by
      field_simp [heps,h2,h4,h15]
      ring
    have hwd : 6*(17/(2*epsilon p))*(2/15 : K)+
        9*(-(2/epsilon p)*(2/15))=22/(5*epsilon p) := by
      field_simp [heps,h2,h5,h15]
      ring
    have hbb : (2/15 : K)^2*(6*(-(1/4))+(9/2)*(-(1/4))^2)= -13/600 := by
      field_simp [h2,h3,h4,h5,h15,h600]
      ring
    have haa : (2/15 : K)^2*(6*4*(-1)+(9/2)*4^2)=64/75 := by
      field_simp [h2,h3,h5,h15,h75]
      ring
    have hab : (2/15 : K)^2*(6*((-(1/4))*(-1)+4)+(9/2)*(2*(-(1/4))*4))=22/75 := by
      field_simp [h2,h3,h4,h5,h15,h75]
      ring
    have hlinT : 6*w+2*(9/2 : K)*v+(129/4 : K)*u=
        6*w+9*v+129*u/4 := by
      field_simp [h2,h4]
    have hexpand :
        Polynomial.C 6*((B+Polynomial.C (2/15 : K)*logTrace p)*
          (C+Polynomial.C (2/15 : K)*originalLogDifference p))+
          Polynomial.C (9/2 : K)*(B+Polynomial.C (2/15 : K)*logTrace p)^2+
          Polynomial.C 9*(A*(C+Polynomial.C (2/15 : K)*originalLogDifference p))+
          Polynomial.C (129/4 : K)*(A*(B+Polynomial.C (2/15 : K)*logTrace p))=
        L0+Polynomial.C ((2/15 : K)*(6*v+9*u))*originalLogDifference p+
          Polynomial.C ((2/15 : K)*(6*w+2*(9/2 : K)*v+(129/4 : K)*u))*logTrace p+
          Polynomial.C (6*(17/(2*epsilon p))*(2/15 : K)+
            9*(-(2/epsilon p)*(2/15 : K)))*
              (WPFiniteWSource.W p*originalLogDifference p)+
          Polynomial.C (6*(-(2/epsilon p))*(2/15 : K)+
            (9/2 : K)*(2*(17/(2*epsilon p))*(2/15 : K))+
            (129/4 : K)*(-(2/epsilon p)*(2/15 : K)))*
              (WPFiniteWSource.W p*logTrace p)+
          Polynomial.C ((2/15 : K)^2)*
            (6*(logTrace p*originalLogDifference p)+
              Polynomial.C (9/2 : K)*(logTrace p)^2) := by
      dsimp only [L0,A,B,C]
      simp only [map_add,map_mul,map_pow,map_neg,map_ofNat]
      ring
    rw [hlinT,hwd,hwl,map_zero,zero_mul,add_zero] at hexpand
    have hlogsquare : Polynomial.C ((2/15 : K)^2)*
        (6*(logTrace p*originalLogDifference p)+
          Polynomial.C (9/2 : K)*(logTrace p)^2)=
        Polynomial.C (-13/600 : K)*Lb^2+Polynomial.C (64/75 : K)*La^2+
          Polynomial.C (22/75 : K)*(Lb*La) := by
      have he : Polynomial.C ((2/15 : K)^2)*
          (6*((-Polynomial.C (1/4 : K)*Lb+Polynomial.C 4*La)*(Lb-La))+
            Polynomial.C (9/2 : K)*(-Polynomial.C (1/4 : K)*Lb+Polynomial.C 4*La)^2)=
          Polynomial.C ((2/15 : K)^2*
            (6*(-(1/4 : K))+(9/2 : K)*(-(1/4 : K))^2))*Lb^2+
          Polynomial.C ((2/15 : K)^2*
            (6*4*(-1)+(9/2 : K)*4^2))*La^2+
          Polynomial.C ((2/15 : K)^2*
            (6*((-(1/4 : K))*(-1)+4)+(9/2 : K)*(2*(-(1/4 : K))*4)))*(Lb*La) := by
        simp only [map_add,map_mul,map_pow,map_neg,map_ofNat,map_one]
        ring
      rw [hbb,haa,hab] at he
      exact he
    rw [hlogsquare] at hexpand
    change Polynomial.C 6*((B+Polynomial.C (2/15 : K)*logTrace p)*
        (C+Polynomial.C (2/15 : K)*originalLogDifference p))+
        Polynomial.C (9/2 : K)*(B+Polynomial.C (2/15 : K)*logTrace p)^2+
        Polynomial.C 9*(A*(C+Polynomial.C (2/15 : K)*originalLogDifference p))+
        Polynomial.C (129/4 : K)*(A*(B+Polynomial.C (2/15 : K)*logTrace p))=_
    dsimp only [L1]
    linear_combination hexpand
  have ht := congrArg (pairedTail p (1/4 : K) 4) hrow
  simp only [pairedTail_add p (by omega),pairedTail_C_mul p (by omega)] at ht
  rw [pairedTail_low p (by omega) _ _ L0 hL0,
    pairedTail_low p (by omega) _ _ L1 hL1,zero_add,zero_add] at ht
  have hWtail : pairedTail p (1/4 : K) 4
      (WPFiniteWSource.W p*originalLogDifference p)=originalPSquareHRow p := by
    exact actual_W_log_difference_tail_ends (K:=K) p hp
  rw [hWtail] at ht
  have hlogs := actual_full_log_weighted_tail_collection (K:=K) p hp
  dsimp only [La,Lb,pairedTail] at ht ⊢
  simp only [div_eq_mul_inv] at ht hlogs ⊢
  linear_combination ht+hlogs

end WPFieldAssembly.SourceClosurePSquareTailCollection
