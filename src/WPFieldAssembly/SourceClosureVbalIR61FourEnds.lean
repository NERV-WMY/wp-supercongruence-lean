import WPFieldAssembly.NativeIR28
import WPFiniteWSource

open scoped Polynomial
open Polynomial WPActualRankTwoProper WPActualRankTwoLegendreField
  WPActualGaussBottom WPFieldAssembly.NativeIR28

namespace WPFieldAssembly.SourceClosureVbalIR61FourEnds

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- This Hasse sign is separate from the original arithmetic epsilon. -/
noncomputable def actualCrossHasseSign : ZMod p :=
  (-1)^(p/6)*2^((p-1)/2)

/-- The literal proper n product on the conic, before its four pole residues. -/
noncomputable def actualCrossConicValue (w t : ZMod p) : ZMod p :=
  6*actualCrossHasseSign p*(w⁻¹)^((p-1)/2+1)*(4-11*w^2)*
    (properLegendreJacobi p).eval (t*(4*w^2-11)/5)*
    (properLegendreJacobi p).eval (t*(4-11*w^2)/(5*w^3))

noncomputable def actualCrossPolePolynomial : (ZMod p)[X] :=
  (4-X^2)*(4*X^2-1)

private theorem proper_negative_end (hp : 19≤p) :
    (properLegendreJacobi p).eval (-1)=
      (-1 : ZMod p)^(p/6)*fieldHarmonic p (p/6) := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 1)
    (actual_proper_legendre_reflect p hp)
  rw [eval_comp,eval_neg,eval_X,eval_mul,eval_neg,eval_C,
    properLegendreJacobi_endpoint_one p] at he
  linear_combination he

private theorem proper_reflected_value (hp : 19≤p) (z : ZMod p) :
    (properLegendreJacobi p).eval (-z)=
      -((-1 : ZMod p)^(p/6))*(properLegendreJacobi p).eval z := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval z)
    (actual_proper_legendre_reflect p hp)
  simpa only [eval_comp,eval_neg,eval_X,eval_mul,eval_C] using he

private theorem half_proper_parity (hp : 19≤p) : Even ((p-1)/2+p/6) := by
  rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5
  · exact ⟨2*(p/6),by omega⟩
  · exact ⟨2*(p/6)+1,by omega⟩

private theorem proper_sign_square : ((-1 : ZMod p)^(p/6))^2=1 := by
  calc
    _ = ((-1 : ZMod p)^2)^(p/6) := by
      rw [←pow_mul,←pow_mul,Nat.mul_comm]
    _ = _ := by norm_num

/-- Reflection is derived from the actual proper Jacobi polynomial, including both classes. -/
theorem actual_cross_conic_reflection (hp : 19≤p) (w t : ZMod p) :
    actualCrossConicValue p (-w) t=actualCrossConicValue p w t := by
  have hw2 : (-w)^2=w^2 := by ring
  have hw3 : (-w)^3= -(w^3) := by ring
  have hsg : (-1 : ZMod p)^((p-1)/2+1)*(-((-1 : ZMod p)^(p/6)))=1 := by
    calc
      _ = -((-1 : ZMod p)^((p-1)/2+1)*(-1 : ZMod p)^(p/6)) := by ring
      _ = -((-1 : ZMod p)^((p-1)/2+p/6+1)) := by
        rw [←pow_add,show (p-1)/2+1+p/6=(p-1)/2+p/6+1 by omega]
      _ = _ := by rw [pow_succ,(half_proper_parity p hp).neg_one_pow]; ring
  have hw : (-w⁻¹)^((p-1)/2+1)=
      (-1 : ZMod p)^((p-1)/2+1)*(w⁻¹)^((p-1)/2+1) := by
    rw [←neg_one_mul,mul_pow]
  have hv : t*(4-11*w^2)/(5*(-(w^3)))= -(t*(4-11*w^2)/(5*w^3)) := by
    rw [mul_neg,div_neg]
  dsimp only [actualCrossConicValue]
  rw [hw2,hw3,←neg_inv,hw,hv,proper_reflected_value p hp]
  linear_combination
    (6*actualCrossHasseSign p*(w⁻¹)^((p-1)/2+1)*(4-11*w^2)*
      (properLegendreJacobi p).eval (t*(4*w^2-11)/5)*
      (properLegendreJacobi p).eval (t*(4-11*w^2)/(5*w^3)))*hsg

private theorem half_end_scale (hp : 19≤p) :
    6*actualCrossHasseSign p*((1/2 : ZMod p)⁻¹)^((p-1)/2+1)*
      (4-11*(1/2 : ZMod p)^2)=15*(-1 : ZMod p)^(p/6) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hhalf : ((2 : ZMod p)^((p-1)/2))^2=1 := by
    calc
      _ = (4 : ZMod p)^((p-1)/2) := by
        rw [←pow_mul,Nat.mul_comm,pow_mul]
        norm_num
      _ = _ := WPFiniteWSource.four_half_power p hp
  have hw : (1/2 : ZMod p)⁻¹=2 := by rw [one_div,inv_inv]
  unfold actualCrossHasseSign
  rw [hw,pow_succ]
  calc
    _ = 15*(-1 : ZMod p)^(p/6)*((2 : ZMod p)^((p-1)/2))^2 := by
      field_simp [h2,h4]
      ring
    _ = _ := by rw [hhalf,mul_one]

private theorem double_end_scale (hp : 19≤p) :
    6*actualCrossHasseSign p*((2 : ZMod p)⁻¹)^((p-1)/2+1)*
      (4-11*(2 : ZMod p)^2)= -120*(-1 : ZMod p)^(p/6) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hhalf : (2 : ZMod p)^((p-1)/2)≠0 := pow_ne_zero _ h2
  unfold actualCrossHasseSign
  rw [pow_succ,inv_pow]
  field_simp [h2,hhalf]
  ring

/-- All four original conic pole numerators are values of the same actual n carrier. -/
theorem actual_cross_conic_four_end_values (hp : 19≤p) :
    actualCrossConicValue p (1/2) (1/2)= -15*fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p (-1/2) (1/2)= -15*fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p 2 1=120*fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p (-2) 1=120*fieldHarmonic p (p/6)^2 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have ha1 : (1/2 : ZMod p)*(4*(1/2 : ZMod p)^2-11)/5= -1 := by
    field_simp [h2,h5]
    ring
  have ha2 : (1/2 : ZMod p)*(4-11*(1/2 : ZMod p)^2)/(5*(1/2 : ZMod p)^3)=1 := by
    field_simp [h2,h5]
    ring
  have hb1 : (1 : ZMod p)*(4*(2 : ZMod p)^2-11)/5=1 := by
    field_simp [h5]
    ring
  have hb2 : (1 : ZMod p)*(4-11*(2 : ZMod p)^2)/(5*(2 : ZMod p)^3)= -1 := by
    field_simp [h2,h5]
    ring
  have ha : actualCrossConicValue p (1/2) (1/2)= -15*fieldHarmonic p (p/6)^2 := by
    unfold actualCrossConicValue
    rw [half_end_scale p hp,ha1,ha2,proper_negative_end p hp,
      properLegendreJacobi_endpoint_one p]
    calc
      _ = -15*((-1 : ZMod p)^(p/6))^2*fieldHarmonic p (p/6)^2 := by ring
      _ = _ := by rw [proper_sign_square p, mul_one]
  have hb : actualCrossConicValue p 2 1=120*fieldHarmonic p (p/6)^2 := by
    unfold actualCrossConicValue
    rw [double_end_scale p hp,hb1,hb2,proper_negative_end p hp,
      properLegendreJacobi_endpoint_one p]
    calc
      _ = 120*((-1 : ZMod p)^(p/6))^2*fieldHarmonic p (p/6)^2 := by ring
      _ = _ := by rw [proper_sign_square p,mul_one]
  refine ⟨ha,?_,hb,?_⟩
  · rw [neg_div,actual_cross_conic_reflection p hp]
    exact ha
  · rw [actual_cross_conic_reflection p hp]
    exact hb

/-- The four original roots and their signed derivatives belong to Abar(w squared). -/
theorem actual_cross_pole_four_end_data (hp : 19≤p) :
    (actualCrossPolePolynomial p).eval (1/2)=0 ∧
    (actualCrossPolePolynomial p).eval (-1/2)=0 ∧
    (actualCrossPolePolynomial p).eval 2=0 ∧
    (actualCrossPolePolynomial p).eval (-2)=0 ∧
    (actualCrossPolePolynomial p).derivative.eval (1/2)=15 ∧
    (actualCrossPolePolynomial p).derivative.eval (-1/2)= -15 ∧
    (actualCrossPolePolynomial p).derivative.eval 2= -60 ∧
    (actualCrossPolePolynomial p).derivative.eval (-2)=60 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hD : (actualCrossPolePolynomial p).derivative= -16*X^3+34*X := by
    norm_num [actualCrossPolePolynomial,derivative_sub,derivative_mul,derivative_pow,C_ofNat]
    ring
  rw [hD]
  simp only [actualCrossPolePolynomial,eval_mul,eval_sub,eval_add,eval_neg,
    eval_pow,eval_ofNat,eval_one,eval_X]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> field_simp [h2] <;> ring

/-- The actual four simple-pole denominators retain their signed 15 and 60 derivatives. -/
theorem actual_cross_conic_four_end_residue_rows (hp : 19≤p) :
    actualCrossConicValue p (1/2) (1/2)/(actualCrossPolePolynomial p).derivative.eval (1/2)=
      -fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p (-1/2) (1/2)/(actualCrossPolePolynomial p).derivative.eval (-1/2)=
      fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p 2 1/(actualCrossPolePolynomial p).derivative.eval 2=
      -2*fieldHarmonic p (p/6)^2 ∧
    actualCrossConicValue p (-2) 1/(actualCrossPolePolynomial p).derivative.eval (-2)=
      2*fieldHarmonic p (p/6)^2 := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h15 : (15 : ZMod p)≠0 := by rw [show (15 : ZMod p)=3*5 by ring]; exact mul_ne_zero h3 h5
  have h60 : (60 : ZMod p)≠0 := by
    rw [show (60 : ZMod p)=2^2*15 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) h15
  obtain ⟨ha,han,hb,hbn⟩ := actual_cross_conic_four_end_values p hp
  obtain ⟨_,_,_,_,hda,hdan,hdb,hdbn⟩ := actual_cross_pole_four_end_data p hp
  rw [ha,han,hb,hbn,hda,hdan,hdb,hdbn]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [h15,h60] <;> ring

end WPFieldAssembly.SourceClosureVbalIR61FourEnds
