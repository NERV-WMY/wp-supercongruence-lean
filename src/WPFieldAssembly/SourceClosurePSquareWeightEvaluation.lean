import WPFieldAssembly.SourceClosurePSquareTrace
import WPFieldAssembly.SourceClosurePSquareTailCollection

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteAffineLog WPFiniteABSourceTail
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.BalancedVbalSuccessorPSquareEnds
  WPFieldAssembly.SourceClosurePSquarePhases WPFieldAssembly.SourceClosurePSquareTrace
  WPFieldAssembly.SourceClosurePSquareTail WPFieldAssembly.SourceClosurePSquareTailCollection
  WPFieldAssembly.SourceClosurePSquareWindowCollection

namespace WPFieldAssembly.SourceClosurePSquareWeightEvaluation

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/- STATEMENT_FIDELITY: evaluate the specified root-free original P square
   through all three original weighted windows, with its degree-p row
   retained by the endpoint constant corrections. The finite value below
   consists of actual original J_H, full finite R/ell, Fermat quotients and
   descended entropy. It is not a definition of the NC77 target scalar.
   The beta-P normalization uses its original finite Frobenius coefficient. -/

noncomputable def originalPSquareFiniteValue (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  22*originalPSquareHRow p/(5*epsilon p)+WPFiniteField.R p (16 : K)/10+
    599*(WPFiniteNC122.q p)^2/25-
    339*WPFiniteNC122.q p*WPFiniteJNormalization.r p/25+
    99*(WPFiniteJNormalization.r p)^2/50+
    6*WPFiniteNC122.q p*WPFiniteField.ell p (16 : K)/25+
    33*WPFiniteJNormalization.r p*WPFiniteField.ell p (16 : K)/100-
    203*(descendedC p)^2/25+32*WPFiniteNC122.q p*descendedC p/25

private theorem full_log_phase_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    ((LP p : K[X]).comp (Polynomial.C 4*X)).eval (1/4)=0 ∧
    ((LP p : K[X]).comp (Polynomial.C 4*X)).eval 4=WPFiniteField.ell p (16 : K) ∧
    ((LP p : K[X]).comp (Polynomial.C (1/4)*X)).eval (1/4)=
      -WPFiniteField.ell p (16 : K)/16 ∧
    ((LP p : K[X]).comp (Polynomial.C (1/4)*X)).eval 4=0 := by
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : K)≠0 := by
    rw [show (16 : K)=4*4 by ring]
    exact mul_ne_zero h4 h4
  have ha : (1/4 : K)*(1/4)=(16 : K)⁻¹ := by field_simp [h4,h16]; ring
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
  refine ⟨?_,?_,?_,?_⟩
  · rw [eval_comp,eval_mul,eval_C,eval_X,hab,LP_eval_eq,hL1]
  · rw [eval_comp,eval_mul,eval_C,eval_X,hb,LP_eval_eq]
  · rw [eval_comp,eval_mul,eval_C,eval_X,ha,LP_eval_eq,hLa]
    ring
  · rw [eval_comp,eval_mul,eval_C,eval_X,hba,LP_eval_eq,hL1]

private theorem original_phase_end_values (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (originalPPlus p : K[X]).eval (1/4)=(4*WPFiniteNC122.q p-3*WPFiniteJNormalization.r p)/15 ∧
    (originalPPlus p : K[X]).eval 4= -2*(4*WPFiniteNC122.q p-3*WPFiniteJNormalization.r p)/15 ∧
    (originalPMiddle p : K[X]).eval (1/4)=
      -34*WPFiniteNC122.q p/15+17*WPFiniteJNormalization.r p/20-
        WPFiniteField.ell p (16 : K)/30 ∧
    (originalPMiddle p : K[X]).eval 4=
      17*WPFiniteNC122.q p/15-17*WPFiniteJNormalization.r p/10-
        WPFiniteField.ell p (16 : K)/30 := by
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
  have h16 : (16 : K)≠0 := WPFiniteField.denominator_ne_zero p 16
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : K)≠0 := by
    rw [show (20 : K)=4*5 by ring]
    exact mul_ne_zero h4 h5
  have h30 : (30 : K)≠0 := by
    rw [show (30 : K)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  obtain ⟨hWa,hWb⟩ := actual_Psquare_W_ends (K:=K) p hp
  obtain ⟨hLbA,hLbB,hLaA,hLaB⟩ := full_log_phase_ends (K:=K) p hp
  simp only [originalPPlus,originalPMiddle,logTrace,eval_add,eval_sub,
    eval_mul,eval_neg,eval_C,hWa,hWb,hLbA,hLbB,hLaA,hLaB]
  unfold WPFiniteNC122.q WPFiniteJNormalization.r
  constructor
  · field_simp [heps,h2,h3,h4,h5,h10,h15,h16,h20,h30]
    ring
  constructor
  · field_simp [heps,h2,h3,h4,h5,h10,h15,h16,h20,h30]
    ring
  constructor <;> field_simp [heps,h2,h3,h4,h5,h10,h15,h16,h20,h30] <;> ring

private theorem original_phase_origins (p : ℕ) [Fact p.Prime] [CharP K p] :
    (originalPPlus p : K[X]).eval 0= -4*(WPFiniteNC122.q p+descendedC p)/15 ∧
    (originalPMiddle p : K[X]).eval 0=17*descendedC p/15 ∧
    (originalPMinus p : K[X]).eval 0=4*(WPFiniteNC122.q p-descendedC p)/15 := by
  have hW0 : (WPFiniteWSource.W p : K[X]).eval 0=0 := by
    simpa only [coeff_zero_eq_eval_zero] using WPFiniteWSource.W_origin (K:=K) p
  have hLP0 (c : K) : ((LP p : K[X]).comp (Polynomial.C c*X)).eval 0=0 := by
    rw [←coeff_zero_eq_eval_zero,WPFiniteProductTail.LP_scaled_coeff,if_neg (by omega)]
  simp only [originalPPlus,originalPMiddle,originalPMinus,logTrace,eval_add,eval_sub,
    eval_mul,eval_C,eval_neg,hW0,hLP0,mul_zero,add_zero,sub_zero]
  trivial

/-- Corrected NC118 is obtained directly from the actual full coefficient windows. -/
theorem actual_original_Psquare_weight_finite (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p ((descendedP p)^2)=
      (originalPSquareFiniteValue p : ZMod p) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : ZMod p)≠0 := by
    rw [show (20 : ZMod p)=4*5 by ring]
    exact mul_ne_zero h4 h5
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h30 : (30 : ZMod p)≠0 := by
    rw [show (30 : ZMod p)=2*15 by ring]
    exact mul_ne_zero h2 h15
  have h50 : (50 : ZMod p)≠0 := by
    rw [show (50 : ZMod p)=2*25 by ring]
    exact mul_ne_zero h2 h25
  have h100 : (100 : ZMod p)≠0 := by
    rw [show (100 : ZMod p)=4*25 by ring]
    exact mul_ne_zero h4 h25
  have h120 : (120 : ZMod p)≠0 := by
    rw [show (120 : ZMod p)=8*15 by ring]
    exact mul_ne_zero h8 h15
  have heps : (epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  have h4p : (4 : ZMod p)^p=4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1/4 : ZMod p)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have h4two : (4 : ZMod p)^(2*p)=4^2 := by rw [Nat.mul_comm,pow_mul,h4p]
  have hatwo : (1/4 : ZMod p)^(2*p)=(1/4)^2 := by rw [Nat.mul_comm,pow_mul,hap]
  obtain ⟨hdA,hdB,hdC⟩ := actual_original_P_phase_degrees (K:=ZMod p) p hp
  have hPC : phaseCarrier p (originalPPlus p : (ZMod p)[X])
      (originalPMiddle p) (originalPMinus p)=descendedP p :=
    (actual_original_P_three_phases p).symm
  have hwin := phaseCarrier_square_windows p (by omega) (1/4 : ZMod p) 4
    (originalPPlus p) (originalPMiddle p) (originalPMinus p)
    (by omega) (by omega) (by omega)
  rw [hPC] at hwin
  obtain ⟨hAa,hAb,hBa,hBb⟩ := original_phase_end_values (K:=ZMod p) p hp
  obtain ⟨hCa,hCb⟩ := actual_original_Pminus_ends (K:=ZMod p) p hp
  obtain ⟨hA0,hB0,hC0⟩ := original_phase_origins (K:=ZMod p) p
  have htail := actual_original_P_square_tail_collection (K:=ZMod p) p hp
  rw [actual_Psquare_three_windows p hp,hwin.1,hwin.2.1,hwin.2.2]
  simp only [hAa,hAb,hBa,hBb,hCa,hCb,hA0,hB0,hC0,h4p,hap,h4two,hatwo]
  unfold originalPSquareFiniteValue
  linear_combination (norm := (field_simp
    [heps,h2,h3,h4,h5,h8,h10,h15,h20,h25,h30,h50,h100,h120]; ring)) htail

/-- This is the original beta-P normalized consumer, including rational p-division ancestry. -/
theorem actual_original_normalized_Psquare_finite (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    f (-(1/3 : ZMod p)*originalWeightedFieldTrace p ((descendedP p)^2)-
      (207/4 : ZMod p)*actualOriginalBetaP p)=
      -(1/3 : K)*f (originalPSquareFiniteValue p : ZMod p)+
      (207/8 : K)*(uSlot p u)^2-
      (69/(5*epsilon p) : K)*(WPFiniteProductTail.originPrimitive p (WPFiniteWSource.W p) (1/4)-
        WPFiniteProductTail.originPrimitive p (WPFiniteWSource.W p) 4) := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : K)≠0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K)≠0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have heps : (epsilon p : K)≠0 := pow_ne_zero _ h5
  simp only [map_sub,map_mul,map_neg,map_div₀,map_one,map_ofNat,
    actual_original_Psquare_weight_finite p hp,actual_original_betaP_finite p hp f u hu]
  field_simp [heps,h2,h3,h4,h5,h8,h15]
  ring

end WPFieldAssembly.SourceClosurePSquareWeightEvaluation
