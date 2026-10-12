import WPFieldAssembly.SourceClosureUVFiniteEnds
import WPFieldAssembly.SourceClosureUVFieldTransport
import WPFieldAssembly.SourceClosureBalancedFirstSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUVDescent WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWholeContraction
  WPFieldAssembly.SourceClosureUVTprodWeight WPFieldAssembly.SourceClosureUVJointEndpoint
  WPFieldAssembly.SourceClosureUVFiniteEnds WPFieldAssembly.SourceClosureUVOrderedH
  WPFieldAssembly.SourceClosureUVFieldTransport WPFieldAssembly.ActualKwOrderedEndpoints
  WPPIntegralReduction WPFieldAssembly.SourceClosureBalancedFirstSource

namespace WPFieldAssembly.SourceClosureUVFiniteCollection

set_option maxHeartbeats 1600000

variable {K L : Type*} [Field K] [Field L]

/- The original UV trace and its same branch correction are collected
   together. The native two-Frobenius coefficient stays unassigned. -/

theorem finite_entropy_sixteen (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteField.ell p (16 : K)=
      -64*(WPFiniteInversion.integerFermatQuotient p 2 : K)+
        15*(WPFiniteInversion.integerFermatQuotient p 3 : K)+
        15*(WPFiniteInversion.integerFermatQuotient p 5 : K) := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h4 := WPFiniteField.ell_quadratic_distribution p hodd (2 : K)
  have h16 := WPFiniteField.ell_quadratic_distribution p hodd (4 : K)
  have h2p : (2 : K)^p=2 := WPFiniteField.natCast_pow_char p 2
  have h4p : (4 : K)^p=4 := WPFiniteField.natCast_pow_char p 4
  rw [show (2 : K)^2=4 by ring,h2p,
    WPFiniteLoop.ell_two p hp,WPFiniteLoop.ell_neg_two p hp] at h4
  rw [show (4 : K)^2=16 by ring,h4p,
    h4,WPFiniteField.ell_neg_four_eq_fermat p hp] at h16
  linear_combination h16

theorem finite_real_rows (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    WPFiniteField.R p (4 : K)=
      -6*(WPFiniteInversion.integerFermatQuotient p 2 : K)^2-
        2*WPFiniteField.R p (-2) ∧
    WPFiniteField.R p (16 : K)=10*WPFiniteField.R p 4-6*WPFiniteField.R p (-4) := by
  have h4 := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_four_eq_fermat p hp)
  have h16 := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_sixteen_distribution p hp)
  constructor
  · simpa only [←WPFiniteField.R_castHom,map_ofNat,map_neg,map_sub,map_mul,
      map_pow,map_intCast] using h4
  · simpa only [←WPFiniteField.R_castHom,map_ofNat,map_neg,map_sub,map_mul] using h16

theorem evenSquared_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteLVSource.evenSquared p : K[X]).map f=WPFiniteLVSource.evenSquared p := by
  simp only [WPFiniteLVSource.evenSquared,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_div₀,map_one,
    map_mul,map_ofNat,map_natCast]

/-- The complete prime-field consumer after cancelling its actual p-hole. -/
theorem actualUV_joint_finite_ordered (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp)-
      (66/25 : ZMod p)*
        (-2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
          (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
            (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)+actualMu p hp)=
      (2/3 : ZMod p)*
        ((-90*(originalHx p).eval (1/4)+45*(originalHx p).eval 4-
          66*(originalHa p).eval (1/4)-21*(originalHa p).eval 4+
          12*(originalHb p).eval (1/4)-33*(originalHb p).eval 4)/
            (2*WPFiniteABSourceTail.epsilon p))+
      (22/15 : ZMod p)*WPFiniteField.R p (-2)+WPFiniteField.R p 16/30+
      (11/25 : ZMod p)*WPFiniteField.R p (-4)+
      (11/10 : ZMod p)*(WPFiniteLoop.D ((p-1)/2) (4/5) 0-
        WPFiniteLoop.D ((p-1)/2) (1/5) 0)+
      (91/75 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
      (73/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)-
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2+
      (51/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)-
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)+
      ((104/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
        (44/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))*descendedC p-
      (22/5 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteLVSource.evenSquared p).eval (4/5) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h30 : (30 : ZMod p)≠0 := by
    rw [show (30 : ZMod p)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have h60 : (60 : ZMod p)≠0 := by
    rw [show (60 : ZMod p)=4*15 by ring]
    exact mul_ne_zero h4 h15
  have h75 : (75 : ZMod p)≠0 := by
    rw [show (75 : ZMod p)=3*25 by ring]
    exact mul_ne_zero h3 h25
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  obtain ⟨hWa,hWb⟩ := actual_W_ends_finite (K:=ZMod p) p hp
  obtain ⟨hW1a,hW1b⟩ := actual_W1_ends_finite p hp
  have h := actualUV_whole_weight_branch p hp
  rw [originalTprod_entropy_evaluated p hp,actual_Hm_ends_finite p hp,
    jointUncanonicalMu_finite_alphabet p hp] at h
  simp only [hWa,hWb,hW1a,hW1b,finite_entropy_sixteen p hp,
    WPFiniteField.ell_neg_four_eq_fermat p hp] at h
  linear_combination (norm := (field_simp [h2,h3,h4,h5,h6,h10,h15,h25,h30,h60,h75,heps]; ring)) h

/-- UW18f for this same actual UV in either root branch; beta is retained. -/
theorem actualUV_joint_finite_alphabet (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u beta : K) (hu : u^2=1/5) :
    f ((2/3 : ZMod p)*originalWeightedFieldTrace p (actualUV p hp)-
      (66/25 : ZMod p)*
        (residueHom p (nativeComparisonBranchCarryIntegral p)+actualMu p hp))-
      (207/4 : K)*beta=
      originalT5 p u+(7/15 : K)*originalG p (1/5)+
      (17/15 : K)*WPFiniteField.R p 4-WPFiniteField.R p 16/25+
      (11/10 : K)*(WPFiniteLoop.D ((p-1)/2) (4/5) 0-
        WPFiniteLoop.D ((p-1)/2) (1/5) 0)+
      (451/75 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)^2+
      (31/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteInversion.integerFermatQuotient p 3 : K)+
      (9/10 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)^2+
      (51/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteInversion.integerFermatQuotient p 5 : K)-
      (3/2 : K)*(WPFiniteInversion.integerFermatQuotient p 3 : K)*
        (WPFiniteInversion.integerFermatQuotient p 5 : K)+
      ((104/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)-
        (44/5 : K)*(WPFiniteInversion.integerFermatQuotient p 5 : K))*descendedC p-
      (22/5 : K)*(WPFiniteInversion.integerFermatQuotient p 2 : K)*
        (WPFiniteLVSource.evenSquared p).eval (4/5)-(207/4 : K)*beta := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K)≠0 := by
    rw [show (25 : K)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have h50 : (50 : K)≠0 := by
    rw [show (50 : K)=2*25 by ring]
    exact mul_ne_zero h2 h25
  have h75 : (75 : K)≠0 := by
    rw [show (75 : K)=3*25 by ring]
    exact mul_ne_zero h3 h25
  have h150 : (150 : K)≠0 := by
    rw [show (150 : K)=2*75 by ring]
    exact mul_ne_zero h2 h75
  rw [actual_comparison_branch_carry_field p hp]
  have h := congrArg f (actualUV_joint_finite_ordered p hp)
  simp only [map_sub,map_add,map_mul,map_div₀,map_neg,map_pow,map_ofNat,map_intCast,
    originalHx,originalHa,originalHb,polynomial_eval_transport,unitPrimitive_transport,
    W_transport,map_zero,map_one,epsilon_transport,finiteDilog_transport,loopD_transport,
    descendedC_transport,evenSquared_transport] at h
  have hH := original_ordered_H_weight p hp u hu
  simp only [originalHx,originalHa,originalHb] at hH
  rw [hH] at h
  obtain ⟨hR4,hR16⟩ := finite_real_rows (K:=K) p hp
  simp only [map_sub,map_add,map_mul,map_div₀,map_neg,map_pow,map_ofNat,map_intCast]
  linear_combination (norm := (field_simp [h2,h3,h4,h5,h10,h15,h25,h30,h50,h75,h150]; ring))
    h-(2/5 : K)*hR4+(11/150 : K)*hR16

end WPFieldAssembly.SourceClosureUVFiniteCollection
