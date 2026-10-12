import WPFieldAssembly.ActualNormCrossAttachment

open scoped Polynomial
open Polynomial WPFiniteAffineLog WPFiniteKSource
  WPActualRankTwoLegendreField WPActualRankTwoProper
  WPFieldAssembly.NativeIR28 WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualNormCrossAttachment

namespace WPFieldAssembly.SourceClosureVbalProperSource

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The original proper source retains both the full odd log and its even Frobenius half. -/
noncomputable def originalProperProduct : (ZMod p)[X] :=
  actualLegendreJacobi p*properLegendreJacobi p*(OP p+X^p*EP p)

private theorem odd_log_reflect : (OP p : (ZMod p)[X]).comp (-X)= -OP p := by
  have hi : (-X : (ZMod p)[X]).comp (-X)=X := by simp
  simp only [OP,mul_comp,C_comp,sub_comp,comp_assoc,hi,comp_X]
  ring

private theorem even_log_reflect : (EP p : (ZMod p)[X]).comp (-X)=EP p := by
  have hi : (-X : (ZMod p)[X]).comp (-X)=X := by simp
  simp only [EP,mul_comp,C_comp,add_comp,comp_assoc,hi,comp_X]
  ring

/-- Every term of the original proper source has the required whole even parity. -/
theorem original_proper_product_even (hp : 19≤p) :
    (originalProperProduct p).comp (-X)=originalProperProduct p := by
  have hY := legendreField_reflect p (p/6) (by omega : 7≤p)
  change (actualLegendreJacobi p).comp (-X)=C ((-1 : ZMod p)^(p/6))*
    actualLegendreJacobi p at hY
  have hn := actual_proper_legendre_reflect p hp
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpow : (-X : (ZMod p)[X])^p= -X^p := hodd.neg_pow X
  have hs : (C ((-1 : ZMod p)^(p/6)) : (ZMod p)[X])^2=1 := by
    rw [←C_pow,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  unfold originalProperProduct
  rw [mul_comp,mul_comp,hY,hn,add_comp,odd_log_reflect,mul_comp,pow_comp,
    X_comp,hpow,even_log_reflect]
  linear_combination
    (actualLegendreJacobi p*properLegendreJacobi p*(OP p+X^p*EP p))*hs

/-- The two actual ends vanish by the full log's end, without assigning either log half. -/
theorem original_proper_product_ends (hp : 19≤p) :
    (originalProperProduct p).eval 1=0 ∧ (originalProperProduct p).eval (-1)=0 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hhalf : (C ((2 : ZMod p)⁻¹) : (ZMod p)[X])*2=1 := by
    change C ((2 : ZMod p)⁻¹)*C (2 : ZMod p)=1
    rw [←C_mul,inv_mul_cancel₀ h2,C_1]
  have hsplit : (OP p : (ZMod p)[X])+EP p=LP p := by
    simp only [OP,EP]
    linear_combination (LP p)*hhalf
  have hLP : (LP p : (ZMod p)[X]).eval 1=0 := by
    rw [LP_eval_eq]
    exact WPFiniteInversion.ell_one_eq_zero p (by omega)
  have hinside : (OP p+X^p*EP p : (ZMod p)[X]).eval 1=0 := by
    simp only [eval_add,eval_mul,eval_pow,eval_X,one_pow,one_mul]
    rw [←eval_add,hsplit,hLP]
  have he : (originalProperProduct p).eval 1=0 := by
    simp only [originalProperProduct,eval_mul,hinside,mul_zero]
  have hm := congrArg (fun Q : (ZMod p)[X] => Q.eval 1)
    (original_proper_product_even p hp)
  simp only [eval_comp,eval_neg,eval_X,he] at hm
  exact ⟨he,hm⟩

/-- The actual quadratic inverse has zero constant; reciprocal divX preserves the full source. -/
theorem original_proper_product_native (hp : 19≤p) :
    (quadraticInverse (originalProperProduct p)).comp (1-X^2)=originalProperProduct p ∧
      (quadraticInverse (originalProperProduct p)).coeff 0=0 := by
  have h := even_native_attachment p hp (originalProperProduct p)
    (original_proper_product_even p hp)
  have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) h
  simp only [eval_comp,eval_sub,eval_one,eval_pow,eval_X,one_pow,sub_self,
    (original_proper_product_ends p hp).1] at he
  exact ⟨h,by simpa only [coeff_zero_eq_eval_zero] using he⟩

end WPFieldAssembly.SourceClosureVbalProperSource
