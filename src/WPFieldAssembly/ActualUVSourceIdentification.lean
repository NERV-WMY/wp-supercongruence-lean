import WPFieldAssembly.SourceClosureUniversalLog
import WPFinitePrimitiveTransport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.SourceClosureUniversalLog

namespace WPFieldAssembly.ActualUVSourceIdentification

/- STATEMENT_FIDELITY: the original UW17b--e carrier is Ucan-u0-VS.
   P is WPFiniteZSource.P with its original three phases. W and all four
   finite primitives use the whole original cutoff. The full u0 below
   keeps the six-H2 expression and R(-4)/6. No finite manifest is used.
   Identifying the actual rational VS and proving the common-trace value
   remain required; definitions and the early P identity alone do not
   establish those conclusions. -/

variable {K : Type*} [Field K]

noncomputable def originalK0 (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (17/(2*WPFiniteABSourceTail.epsilon p) : K) -
    LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
      (T (p : ℤ)+T (-(p : ℤ)))

noncomputable def originalInvisibleP (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  LaurentPolynomial.C (WPFiniteABSourceTail.uSlot p u)*T (p : ℤ) +
    LaurentPolynomial.C (17*WPFifthEntropy.C p u/15) +
    LaurentPolynomial.C (4*(WPFiniteNC122.q p-WPFifthEntropy.C p u)/15)*T (-(p : ℤ))

/-- The entire original P, including every derivative-invisible phase. -/
theorem originalP_decomposition (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    WPFiniteZSource.P p u =
      originalK0 p*(WPFiniteWSource.W p : K[X]).toLaurent +
        originalJlog p+originalInvisibleP p u := by
  simp only [WPFiniteZSource.P,WPFiniteABSourceTail.A,
    WPFiniteABSourceTail.B0,WPFiniteABSourceTail.Bpoly,
    WPFiniteABSourceTail.logTrace,WPFinitePSource.Cminus,
    WPFinitePSource.logDifference,originalK0,originalJlog,
    originalInvisibleP,scaledLog,map_add,map_sub,map_mul,map_neg,
    Polynomial.toLaurent_C]
  ring

noncomputable def originalHx (p : ℕ) : K[X] :=
  WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) 0

noncomputable def originalHa (p : ℕ) : K[X] :=
  WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) (1/4)

noncomputable def originalHb (p : ℕ) : K[X] :=
  WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) 4

noncomputable def originalHm (p : ℕ) : K[X] :=
  WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) (-1)

theorem unitPrimitive_degree_le_source (p : ℕ) (W : K[X]) (z : K) :
    (WPFiniteProductTail.unitPrimitiveP p W z).natDegree≤W.natDegree := by
  unfold WPFiniteProductTail.unitPrimitiveP
  apply natDegree_sum_le_of_forall_le
  intro i _
  by_cases hi : i≤W.natDegree
  · apply (natDegree_C_mul_le _ _).trans
    unfold WPFiniteProductTail.integratedGeometric
    apply natDegree_sum_le_of_forall_le
    intro k hk
    have hki := (Finset.mem_Ico.mp hk).2
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : W.natDegree < i),C_0,zero_mul]
    simp

/-- All four actual primitives lie below N; no degree-p kernel is inferred away. -/
theorem originalH_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (originalHx p : K[X]).natDegree≤(p-1)/2-1 ∧
      (originalHa p : K[X]).natDegree≤(p-1)/2-1 ∧
      (originalHb p : K[X]).natDegree≤(p-1)/2-1 ∧
      (originalHm p : K[X]).natDegree≤(p-1)/2-1 := by
  have h (z : K) : (WPFiniteProductTail.unitPrimitiveP p (WPFiniteWSource.W p) z).natDegree≤(p-1)/2-1 :=
    (unitPrimitive_degree_le_source p _ z).trans (WPFiniteWSource.W_degree p hp)
  exact ⟨h 0,h (1/4),h 4,h (-1)⟩

theorem originalHx_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    X*(originalHx p : K[X]).derivative = WPFiniteWSource.W p := by
  exact WPFiniteProductTail.originPrimitiveP_source p _
    ((WPFiniteWSource.W_degree p hp).trans_lt (by omega))
    (WPFiniteWSource.W_origin p)

theorem originalHa_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (X-Polynomial.C (1/4 : K))*(originalHa p).derivative =
      WPFiniteWSource.W p-Polynomial.C ((WPFiniteWSource.W p).eval (1/4 : K)) := by
  exact WPFiniteProductTail.unitPrimitiveP_source p _
    ((WPFiniteWSource.W_degree p hp).trans_lt (by omega))
    (WPFiniteWSource.W_origin p) _

theorem originalHb_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (X-Polynomial.C (4 : K))*(originalHb p).derivative =
      WPFiniteWSource.W p-Polynomial.C ((WPFiniteWSource.W p).eval (4 : K)) := by
  exact WPFiniteProductTail.unitPrimitiveP_source p _
    ((WPFiniteWSource.W_degree p hp).trans_lt (by omega))
    (WPFiniteWSource.W_origin p) _

theorem originalHm_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (X+1)*(originalHm p : K[X]).derivative =
      WPFiniteWSource.W p-Polynomial.C ((WPFiniteWSource.W p).eval (-1 : K)) := by
  simpa only [originalHm,Polynomial.C_neg,Polynomial.C_1,sub_neg_eq_add] using
    WPFiniteProductTail.unitPrimitiveP_source p (WPFiniteWSource.W p)
      ((WPFiniteWSource.W_degree p hp).trans_lt (by omega))
      (WPFiniteWSource.W_origin p) (-1 : K)

noncomputable def originalHsym (p : ℕ) : K[T;T⁻¹] :=
  (originalHx p).toLaurent+invert (originalHx p).toLaurent-
    (originalHa p).toLaurent-(originalHb p).toLaurent-
    invert (originalHa p).toLaurent-invert (originalHb p).toLaurent-
    LaurentPolynomial.C (1/2 : K)*
      ((originalHm p).toLaurent+invert (originalHm p).toLaurent)

theorem originalHsym_symmetric (p : ℕ) :
    invert (originalHsym p : K[T;T⁻¹])=originalHsym p := by
  have hi (L : K[T;T⁻¹]) : invert (invert L)=L :=
    LaurentPolynomial.involutive_invert L
  simp only [originalHsym,map_add,map_sub,map_mul,invert_C,
    hi]
  ring

noncomputable def originalJa (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
    (T (-(p : ℤ))-LaurentPolynomial.C (1/4 : K))*scaledLog p 4

noncomputable def originalJb (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : K)*
    (T (-(p : ℤ))-LaurentPolynomial.C (4 : K))*scaledLog p (1/4)

noncomputable def originalZE (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  (WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4+
    4*WPFiniteABSourceTail.epsilon p*WPFifthEntropy.C p u/15

noncomputable def originalUcan (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  originalK0 p*originalHsym p-
    LaurentPolynomial.C (originalZE p u)*(originalJa p+originalJb p)-
    LaurentPolynomial.C (1/2 : K)*originalJ2log p

noncomputable def originalU0 (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  (5/3 : K)*
    (WPFiniteLoop.S p (2*u) 1+WPFiniteLoop.S p (2*u) 2-
      WPFiniteLoop.S p u (1/2)-WPFiniteLoop.S p u 1-
      WPFiniteLoop.S p (2*u) (2*u)+WPFiniteLoop.S p u u+
      (WPFiniteLoop.S p (2*u) 0-WPFiniteLoop.S p u 0)/2)-
    (2*WPFiniteNC122.q p/3+
      (WPFiniteInversion.integerFermatQuotient p 3 : K)/2)*WPFiniteField.ell p (-4)+
      WPFiniteField.R p (-4)/6

noncomputable def originalU (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) :
    K[T;T⁻¹] :=
  originalUcan p u-LaurentPolynomial.C (originalU0 p u)

/-- Only the three UW17 integration holes are removed; 2p is retained. -/
noncomputable def originalCan (p : ℕ) (P : K[T;T⁻¹]) : K[T;T⁻¹] :=
  P-LaurentPolynomial.C (P.coeff 0)-
    LaurentPolynomial.C (P.coeff (p : ℤ))*T (p : ℤ)-
    LaurentPolynomial.C (P.coeff (-(p : ℤ)))*T (-(p : ℤ))

theorem originalCan_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : K[T;T⁻¹]) : D (originalCan p P)=D P := by
  have hp0 : ((p : ℤ) : K)=0 := by
    simpa only [Int.cast_natCast] using (CharP.cast_eq_zero K p)
  simp only [originalCan,map_sub,D_C,D_monomial,Int.cast_neg,hp0,
    neg_zero,mul_zero,map_zero,zero_mul,sub_zero]

theorem original_coeff_C (a : K) (j : ℤ) :
    (LaurentPolynomial.C a).coeff j=if (0 : ℤ)=j then a else 0 := by
  have h : LaurentPolynomial.C a=LaurentPolynomial.C a*T (0 : ℤ) := by simp
  rw [h,←single_eq_C_mul_T]
  exact Finsupp.single_apply

theorem originalCan_holes (p : ℕ) [Fact p.Prime] (P : K[T;T⁻¹]) :
    (originalCan p P).coeff 0=0 ∧
      (originalCan p P).coeff (p : ℤ)=0 ∧
      (originalCan p P).coeff (-(p : ℤ))=0 := by
  have hp : 0<(p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [originalCan,←single_eq_C_mul_T,original_coeff_C,
    AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  simp only [if_true,if_neg (by omega : (p : ℤ)≠0),
    if_neg (by omega : -(p : ℤ)≠0),if_neg (by omega : (0 : ℤ)≠p),
    if_neg (by omega : (0 : ℤ)≠-(p : ℤ)),
    if_neg (by omega : (p : ℤ)≠-(p : ℤ)),
    if_neg (by omega : -(p : ℤ)≠(p : ℤ)),sub_zero,sub_self]
  exact ⟨True.intro,True.intro,True.intro⟩

/-- A nonunit higher carry is unchanged by the original three-hole projection. -/
theorem originalCan_retains_two_p (p : ℕ) [Fact p.Prime]
    (P : K[T;T⁻¹]) : (originalCan p P).coeff (2*(p : ℤ))=P.coeff (2*(p : ℤ)) := by
  have hp : 0<(p : ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [originalCan,←single_eq_C_mul_T,original_coeff_C,
    AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply,
    if_neg (by omega : (0 : ℤ)≠2*(p : ℤ)),
    if_neg (by omega : (p : ℤ)≠2*(p : ℤ)),
    if_neg (by omega : -(p : ℤ)≠2*(p : ℤ)),sub_zero]

end WPFieldAssembly.ActualUVSourceIdentification
