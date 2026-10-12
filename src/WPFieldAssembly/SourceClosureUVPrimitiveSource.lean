import WPFieldAssembly.ActualUVSourceIdentification

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualUVSourceIdentification

namespace WPFieldAssembly.SourceClosureUVPrimitiveSource

set_option maxHeartbeats 1600000

/- STATEMENT_FIDELITY: literal cleared derivatives of UW17's four
   original finite primitives and their inverses. Ordinary residues
   are retained. No derivative premise is used to identify Ucan or VS. -/

variable {K : Type*} [Field K]

noncomputable def poleProduct : K[T;T⁻¹] :=
  T 1*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)

noncomputable def poleProductOverX : K[T;T⁻¹] :=
  (T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)

theorem inverse_primitive_source (H W : K[T;T⁻¹]) (c d v : K)
    (hcd : c*d=1)
    (hsource : (T 1-LaurentPolynomial.C c)*D H=W-LaurentPolynomial.C v) :
    T 1*(T 1-LaurentPolynomial.C d)*D (invert H)=
      LaurentPolynomial.C d*(invert W-LaurentPolynomial.C v) := by
  have hi := congrArg invert hsource
  simp only [map_mul,map_sub,invert_T,invert_C] at hi
  have hconst : LaurentPolynomial.C d*LaurentPolynomial.C c=1 := by
    rw [←map_mul,mul_comm d c,hcd,map_one]
  have ht2 : (T 1*T (-2) : K[T;T⁻¹])=T (-1) := by rw [←T_add]; norm_num
  have ht20 : (T 1^2*T (-2) : K[T;T⁻¹])=1 := by
    rw [T_pow,←T_add]
    norm_num
  rw [D_invert]
  linear_combination
    LaurentPolynomial.C d*hi+invert (D H)*hconst-invert (D H)*ht20+
      LaurentPolynomial.C d*invert (D H)*ht2

theorem originalHx_laurent_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    T 1*D (originalHx p : K[X]).toLaurent=(WPFiniteWSource.W p).toLaurent := by
  have h := congrArg (fun P : K[X] => P.toLaurent) (originalHx_source p hp)
  simpa only [map_mul,Polynomial.toLaurent_X,D_toLaurent] using h

theorem originalH_laurent_sources (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (T 1-LaurentPolynomial.C (1/4 : K))*D (originalHa p).toLaurent=
        (WPFiniteWSource.W p).toLaurent-
          LaurentPolynomial.C ((WPFiniteWSource.W p).eval (1/4 : K)) ∧
      (T 1-4)*D (originalHb p).toLaurent=
        (WPFiniteWSource.W p).toLaurent-
          LaurentPolynomial.C ((WPFiniteWSource.W p).eval (4 : K)) ∧
      (T 1+1)*D (originalHm p).toLaurent=
        (WPFiniteWSource.W p).toLaurent-
          LaurentPolynomial.C ((WPFiniteWSource.W p).eval (-1 : K)) := by
  have ha := congrArg (fun P : K[X] => P.toLaurent) (originalHa_source (K:=K) p hp)
  have hb := congrArg (fun P : K[X] => P.toLaurent) (originalHb_source (K:=K) p hp)
  have hm := congrArg (fun P : K[X] => P.toLaurent) (originalHm_source (K:=K) p hp)
  simp only [map_mul,map_sub,map_add,Polynomial.toLaurent_X,
    Polynomial.toLaurent_C,map_one,map_ofNat,←D_toLaurent] at ha hb hm
  exact ⟨ha,hb,hm⟩

/-- Complete pole-cleared Hsym derivative before collecting any endpoint residue. -/
theorem originalHsym_source_expanded (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    let x : K[T;T⁻¹] := T 1
    let a : K[T;T⁻¹] := LaurentPolynomial.C (1/4 : K)
    let W := (WPFiniteWSource.W p : K[X]).toLaurent
    let wa := LaurentPolynomial.C ((WPFiniteWSource.W p).eval (1/4 : K))
    let wb := LaurentPolynomial.C ((WPFiniteWSource.W p).eval (4 : K))
    let wm := LaurentPolynomial.C ((WPFiniteWSource.W p).eval (-1 : K))
    2*poleProduct*D (originalHsym p)=
      2*poleProductOverX*(W-invert W)-
      2*x*(x+1)*(x-4)*(W-wa)-2*x*(x+1)*(x-a)*(W-wb)-
      8*(x+1)*(x-a)*(invert W-wa)-
      2*a*(x+1)*(x-4)*(invert W-wb)-
      x*(x-a)*(x-4)*(W-wm)+(x-a)*(x-4)*(invert W-wm) := by
  dsimp only
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hhalf : (2 : K[T;T⁻¹])*LaurentPolynomial.C (1/2 : K)=1 := by
    change LaurentPolynomial.C (2 : K)*LaurentPolynomial.C (1/2 : K)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  have hx := originalHx_laurent_source (K:=K) p hp
  have hs := originalH_laurent_sources (K:=K) p hp
  have hi := congrArg invert hx
  simp only [map_mul,invert_T] at hi
  have hxv : T 1*D (invert (originalHx p).toLaurent)=
      -invert (WPFiniteWSource.W p : K[X]).toLaurent := by
    have ht : (T 1*T (-2) : K[T;T⁻¹])=T (-1) := by rw [←T_add]; norm_num
    rw [D_invert]
    linear_combination -hi-invert (D (originalHx p).toLaurent)*ht
  have hav := inverse_primitive_source (K:=K) (originalHa p).toLaurent
    (WPFiniteWSource.W p).toLaurent (1/4) 4 _ (one_div_mul_cancel h4) hs.1
  have hbv := inverse_primitive_source (K:=K) (originalHb p).toLaurent
    (WPFiniteWSource.W p).toLaurent 4 (1/4) _ (mul_one_div_cancel h4) hs.2.1
  have hmv := inverse_primitive_source (K:=K) (originalHm p).toLaurent
    (WPFiniteWSource.W p).toLaurent (-1) (-1) _ (by ring) (by
      simpa only [map_neg,map_one,sub_neg_eq_add] using hs.2.2)
  simp only [map_ofNat,map_neg,map_one,sub_neg_eq_add] at hav hbv hmv
  have hd : 2*D (originalHsym p : K[T;T⁻¹])=
      2*D (originalHx p).toLaurent+2*D (invert (originalHx p).toLaurent)-
      2*D (originalHa p).toLaurent-2*D (originalHb p).toLaurent-
      2*D (invert (originalHa p).toLaurent)-2*D (invert (originalHb p).toLaurent)-
      D (originalHm p).toLaurent-D (invert (originalHm p).toLaurent) := by
    simp only [originalHsym,map_add,map_sub,D_C_mul]
    linear_combination
      -(D (originalHm p).toLaurent+D (invert (originalHm p).toLaurent))*hhalf
  rw [show 2*poleProduct*D (originalHsym p : K[T;T⁻¹])=
      poleProduct*(2*D (originalHsym p)) by ring,hd]
  unfold poleProduct poleProductOverX
  linear_combination
    2*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*hx+
    2*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*hxv-
    2*T 1*(T 1+1)*(T 1-4)*hs.1-
    2*T 1*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*hs.2.1-
    2*(T 1+1)*(T 1-LaurentPolynomial.C (1/4 : K))*hav-
    2*(T 1+1)*(T 1-4)*hbv-
    T 1*(T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*hs.2.2-
    (T 1-LaurentPolynomial.C (1/4 : K))*(T 1-4)*hmv

end WPFieldAssembly.SourceClosureUVPrimitiveSource
