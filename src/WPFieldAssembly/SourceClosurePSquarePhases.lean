import WPFieldAssembly.SourceClosureUVFieldTransport
import WPFieldAssembly.BalancedVbalSuccessorPSquareEnds
import WPFieldAssembly.SourceClosurePSquareWindowCollection

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteAffineLog WPFiniteABSourceTail
  WPFieldAssembly.SourceClosureUniversalLog WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.BalancedVbalSuccessorPSquareEnds

namespace WPFieldAssembly.SourceClosurePSquarePhases

/- STATEMENT_FIDELITY: corrected NC118a/f in the retained
   universal_actual_trace_review/ROOT_NC115_NC119.md. These are the
   specified root-free P and its full five square phases, over every
   field of characteristic p with p prime and p >= 19 for endpoint
   values. The finite logarithm is LP with the entire 1..p-1 cutoff,
   W and descendedC are the original objects. No generated input is
   used. This unit supplies neither the square-tail value nor NC77. -/

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

noncomputable def originalPPlus (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  Polynomial.C (-4*(WPFiniteNC122.q p+descendedC p)/15)-
    Polynomial.C (2/epsilon p)*(WPFiniteWSource.W p)

noncomputable def originalPMiddle (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  Polynomial.C (17*descendedC p/15)+
    Polynomial.C (17/(2*epsilon p))*(WPFiniteWSource.W p)+
      Polynomial.C (2/15 : K)*logTrace p

noncomputable def originalPMinus (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  Polynomial.C (4*(WPFiniteNC122.q p-descendedC p)/15)-
    Polynomial.C (2/epsilon p)*(WPFiniteWSource.W p)+
      Polynomial.C (2/15 : K)*((LP p).comp (Polynomial.C 4*X)-
        (LP p).comp (Polynomial.C (1/4)*X))

private theorem scaled_LP_degree (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (Polynomial.C c*X)).natDegree≤p-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [WPFiniteProductTail.LP_scaled_coeff,if_neg (by omega)]

theorem actual_original_P_phase_degrees (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (originalPPlus p : K[X]).natDegree≤(p-1)/2-1 ∧
      (originalPMiddle p : K[X]).natDegree≤p-1 ∧
      (originalPMinus p : K[X]).natDegree≤p-1 := by
  have hW := WPFiniteWSource.W_degree (K:=K) p hp
  have hWp : (WPFiniteWSource.W p : K[X]).natDegree≤p-1 := hW.trans (by omega)
  have hb (a b : K) : (Polynomial.C a-Polynomial.C b*WPFiniteWSource.W p).natDegree≤
      (WPFiniteWSource.W p : K[X]).natDegree :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  have hm (a b : K) : (Polynomial.C a+Polynomial.C b*WPFiniteWSource.W p).natDegree≤
      (WPFiniteWSource.W p : K[X]).natDegree :=
    (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_C_mul_le _ _))
  refine ⟨(hb _ _).trans hW,?_,?_⟩
  · exact (natDegree_add_le _ _).trans (max_le ((hm _ _).trans hWp)
      ((natDegree_C_mul_le _ _).trans (logTrace_degree p)))
  · exact (natDegree_add_le _ _).trans (max_le ((hb _ _).trans hWp)
      ((natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
        (max_le (scaled_LP_degree p 4) (scaled_LP_degree p (1/4))))))

/-- These are the three phases of the specified original P, including all invisible slots. -/
theorem actual_original_P_three_phases (p : ℕ) [Fact p.Prime] [CharP K p] :
    descendedP p=T (p : ℤ)*(originalPPlus p : K[X]).toLaurent+
      (originalPMiddle p).toLaurent+T (-(p : ℤ))*(originalPMinus p).toLaurent := by
  simp only [descendedP,descendedInvisibleP,originalK0,originalJlog,
    originalPPlus,originalPMiddle,originalPMinus,logTrace,scaledLog,
    map_add,map_sub,map_mul,map_neg,Polynomial.toLaurent_C]
  ring

/-- All five square phases remain before the original trace takes any window. -/
theorem actual_original_P_five_square_phases (p : ℕ) [Fact p.Prime] [CharP K p] :
    (descendedP p)^2=
      T (2*(p : ℤ))*((originalPPlus p : K[X])^2).toLaurent+
      LaurentPolynomial.C (2 : K)*T (p : ℤ)*
        (originalPPlus p*originalPMiddle p).toLaurent+
      ((originalPMiddle p)^2+Polynomial.C (2 : K)*originalPPlus p*originalPMinus p).toLaurent+
      LaurentPolynomial.C (2 : K)*T (-(p : ℤ))*
        (originalPMiddle p*originalPMinus p).toLaurent+
      T (-2*(p : ℤ))*((originalPMinus p)^2).toLaurent := by
  rw [actual_original_P_three_phases]
  exact SourceClosurePSquareWindowCollection.phaseCarrier_square p
    (originalPPlus p) (originalPMiddle p) (originalPMinus p)

/-- Both original minus-phase endpoints are evaluated using the full finite logarithm. -/
theorem actual_original_Pminus_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (originalPMinus p : K[X]).eval (1/4)=
      (4/5 : K)*WPFiniteNC122.q p-(1/5 : K)*WPFiniteJNormalization.r p+
        WPFiniteField.ell p 16/120 ∧
    (originalPMinus p : K[X]).eval 4=
      (2/5 : K)*WPFiniteJNormalization.r p+(2/15 : K)*WPFiniteField.ell p 16 := by
  have heps : (epsilon p : K)≠0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := by
    rw [show (15 : K)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h16 : (16 : K)≠0 := by
    rw [show (16 : K)=4*4 by ring]
    exact mul_ne_zero h4 h4
  have h120 : (120 : K)≠0 := by
    rw [show (120 : K)=2*3*4*5 by ring]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h3) h4) h5
  have ha : (1/4 : K)*(1/4)=1/16 := by field_simp [h4,h16]; ring
  have hab : (4 : K)*(1/4)=1 := by field_simp [h4]
  have hba : (1/4 : K)*4=1 := by field_simp [h4]
  have hb : (4 : K)*4=16 := by ring
  have hL1 : WPFiniteField.ell p (1 : K)=0 := by
    have h := congrArg (ZMod.castHom (dvd_refl p) K)
      (WPFiniteInversion.ell_one_eq_zero p (by omega))
    simpa only [←WPFiniteField.ell_castHom,map_one,map_zero] using h
  have hLa := WPFiniteField.ell_inversion p (16 : K) h16
  have h16p : (16 : K)^p=16 := WPFiniteField.natCast_pow_char p 16
  rw [h16p] at hLa
  obtain ⟨hWa,hWb⟩ := actual_Psquare_W_ends (K:=K) p hp
  simp only [one_div] at ha hab hba hWa hWb
  simp only [originalPMinus,eval_add,eval_sub,eval_mul,eval_C,eval_comp,
    eval_X,LP_eval_eq,ha,hab,hba,hb,hWa,hWb,hL1,one_div,hLa]
  change _ ∧ _
  unfold WPFiniteNC122.q WPFiniteJNormalization.r
  constructor <;> field_simp [heps,h2,h3,h4,h5,h15,h16,h120] <;> ring

end WPFieldAssembly.SourceClosurePSquarePhases
