import WPFiniteLaurentDifferential

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.SourceClosureLaurentBranchJets

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

noncomputable abbrev branchEval : K[T;T⁻¹] →+* K :=
  LaurentPolynomial.eval₂ (RingHom.id K) (-1 : Kˣ)

def ThreeBranchJets (L : K[T;T⁻¹]) : Prop :=
  branchEval L=0 ∧ branchEval (D L)=0 ∧ branchEval (D (D L))=0

theorem laurent_inversion_eval (u : Kˣ) (L : K[T;T⁻¹]) :
    LaurentPolynomial.eval₂ (RingHom.id K) u (invert L)=
      LaurentPolynomial.eval₂ (RingHom.id K) u⁻¹ L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add,hL,hM]
  | C_mul_T n a =>
    simp only [map_mul,invert_C,invert_T,LaurentPolynomial.eval₂_C,LaurentPolynomial.eval₂_T,
      RingHom.id_apply,zpow_neg,inv_zpow]

theorem branch_eval_invert (L : K[T;T⁻¹]) : branchEval (invert L)=branchEval L := by
  rw [branchEval,laurent_inversion_eval]
  simp only [inv_neg,inv_one]

theorem branch_eval_toLaurent (P : K[X]) : branchEval P.toLaurent=P.eval (-1) := by
  simp only [branchEval,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,
    Units.val_neg,Units.val_one]

theorem three_branch_jets_toLaurent (P : K[X])
    (hP : P.eval (-1)=0 ∧ P.derivative.eval (-1)=0 ∧
      P.derivative.derivative.eval (-1)=0) : ThreeBranchJets P.toLaurent := by
  simpa only [ThreeBranchJets,D_toLaurent,branch_eval_toLaurent] using hP

/-- Multiplication preserves all three vanishing jets, with every factor retained. -/
theorem three_branch_jets_mul (Z L : K[T;T⁻¹]) (hL : ThreeBranchJets L) :
    ThreeBranchJets (Z*L) := by
  rcases hL with ⟨h0,h1,h2⟩
  refine ⟨?_,?_,?_⟩
  · rw [map_mul,h0,mul_zero]
  · rw [D_mul,map_add,map_mul,map_mul,h0,h1,mul_zero,mul_zero,add_zero]
  · rw [D_mul,map_add,D_mul,D_mul]
    simp only [map_add,map_mul,h0,h1,h2,mul_zero,add_zero]

theorem three_branch_jets_add (L M : K[T;T⁻¹])
    (hL : ThreeBranchJets L) (hM : ThreeBranchJets M) : ThreeBranchJets (L+M) := by
  rcases hL with ⟨hL0,hL1,hL2⟩
  rcases hM with ⟨hM0,hM1,hM2⟩
  refine ⟨?_,?_,?_⟩
  · rw [map_add,hL0,hM0,add_zero]
  · rw [map_add,map_add,hL1,hM1,add_zero]
  · rw [map_add,map_add,map_add,hL2,hM2,add_zero]

theorem three_branch_jets_invert (L : K[T;T⁻¹]) (hL : ThreeBranchJets L) :
    ThreeBranchJets (invert L) := by
  rcases hL with ⟨h0,h1,h2⟩
  refine ⟨?_,?_,?_⟩
  · rw [branch_eval_invert,h0]
  · rw [D_invert]
    simp only [map_neg,map_mul,branch_eval_invert,h1,mul_zero,neg_zero]
  · rw [D_invert,map_neg,D_mul,D_invert]
    simp only [map_neg,map_add,map_mul,branch_eval_invert,h1,h2,mul_zero,
      neg_zero,add_zero]

/-- Value or first multiplier jet suffices for the same branch normalization.
The original P branch value is explicit and has not been assigned a number. -/
theorem native_ratio_branch_value (f G P delta T0 Tproper E R : K[T;T⁻¹])
    (b : K) (h2 : (2 : K)≠0) (hf : branchEval f≠0 ∨ branchEval (D f)≠0)
    (hG : ThreeBranchJets G) (hT : branchEval Tproper=0 ∧ branchEval (D Tproper)=0)
    (hT0 : branchEval T0=0)
    (hE : branchEval E=branchEval f*b ∧ branchEval (D E)=branchEval (D f)*b)
    (hfactor : 6*f^2*T0-3*f^2*P^2-3*G^2-6*f*G*P+6*G*delta+
      2*f*Tproper-6*f*E=f^2*R) :
    branchEval R=-3*(branchEval P)^2-6*b := by
  by_cases hv : branchEval f=0
  · have hd : branchEval (D f)≠0 := hf.resolve_left (not_ne_iff.mpr hv)
    have hs := congrArg (fun L : K[T;T⁻¹] => branchEval (D (D L))) hfactor
    simp only [pow_two,map_add,map_sub,D_mul] at hs
    /- The full product rule retains G''*delta+2*G'*delta'+G*delta''
    and f''*Tproper+2*f'*Tproper'+f*Tproper''. The supplied G jets
    and proper value/first jet kill these terms; f=0 kills the unsupplied
    second jets of E, Tproper and R. Only the value of T0 is required. -/
    simp only [map_add,map_mul,map_ofNat,hv,hG.1,hG.2.1,hG.2.2,
      hT.1,hT.2,hT0,hE.1,hE.2,mul_zero,zero_mul,add_zero,zero_add,sub_zero] at hs
    have hsecond :
        2*(branchEval (D f))^2*(-3*(branchEval P)^2-6*b)=
          2*(branchEval (D f))^2*branchEval R := by
      linear_combination hs
    have hz : 2*(branchEval (D f))^2*(branchEval R+3*(branchEval P)^2+6*b)=0 := by
      linear_combination -hsecond
    have he := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero h2 (pow_ne_zero 2 hd))
    linear_combination he
  · have hs := congrArg (branchEval (K:=K)) hfactor
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,hG.1,hT.1,hT0,hE.1,
      mul_zero,zero_mul,add_zero,sub_zero] at hs
    have hz : (branchEval f)^2*(branchEval R+3*(branchEval P)^2+6*b)=0 := by
      linear_combination -hs
    have he := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hv)
    linear_combination he

end WPFieldAssembly.SourceClosureLaurentBranchJets
