import WPFieldAssembly.NativeIR28
import WPActualPositivePair
import Mathlib.Algebra.Polynomial.FieldDivision

open scoped Polynomial
open Polynomial WPActualRankTwoProper WPActualRankTwoResidueSource
  WPFieldAssembly.NativeIR28 WPActualPositivePair

namespace WPFieldAssembly.SourceClosureVbalIR61ExactPart

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The whole native n times Re polynomial, before the exact IR61 component is removed. -/
noncomputable def actualNRPolynomial (hp : 19≤p) : (ZMod p)[X] :=
  properLegendreJacobi p*actualRankDividedField p (by omega)

noncomputable def actualNRQuotient (hp : 19≤p) : (ZMod p)[X] :=
  actualNRPolynomial p hp /ₘ (X^2-1)

/-- Its original zero-origin primitive retains every unit integration index. -/
noncomputable def actualNRPrimitive (hp : 19≤p) : (ZMod p)[X] :=
  eulerPrimitive p (2*X^2*actualNRQuotient p hp)

theorem actual_NR_degree_odd_ends (hp : 19≤p) :
    (actualNRPolynomial p hp).natDegree≤p-2 ∧
      (actualNRPolynomial p hp).comp (-X)= -actualNRPolynomial p hp ∧
      (actualNRPolynomial p hp).eval 1=0 ∧
      (actualNRPolynomial p hp).eval (-1)=0 := by
  have hn := properLegendreJacobi_degree p (by omega : 7≤p)
  have hR := actualRankDividedField_degree p (by omega : 7≤p)
  have hd : (actualNRPolynomial p hp).natDegree≤p-2 := by
    have hmul := natDegree_mul_le_of_le (Nat.le_sub_one_of_lt hn) hR
    unfold actualNRPolynomial
    exact hmul.trans (by have := Nat.div_mul_le_self p 6; omega)
  have hs : (C ((-1 : ZMod p)^(p/6)) : (ZMod p)[X])^2=1 := by
    rw [←C_pow,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  have ho : (actualNRPolynomial p hp).comp (-X)= -actualNRPolynomial p hp := by
    unfold actualNRPolynomial
    rw [mul_comp,actual_proper_legendre_reflect p hp,actual_rank_divided_reflect p hp]
    linear_combination -(properLegendreJacobi p*actualRankDividedField p (by omega))*hs
  have he : (actualNRPolynomial p hp).eval 1=0 := by
    simp only [actualNRPolynomial,eval_mul,actualRankDividedField_endpoint_one,mul_zero]
  have hem := congrArg (fun P : (ZMod p)[X] => P.eval 1) ho
  simp only [eval_comp,eval_neg,eval_X,he,neg_zero] at hem
  exact ⟨hd,ho,he,hem⟩

theorem actual_NR_quotient_identity_degree_odd (hp : 19≤p) :
    (X^2-1)*actualNRQuotient p hp=actualNRPolynomial p hp ∧
      (actualNRQuotient p hp).natDegree≤p-4 ∧
      (actualNRQuotient p hp).comp (-X)= -actualNRQuotient p hp := by
  obtain ⟨hdeg,ho,he,hem⟩ := actual_NR_degree_odd_ends p hp
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hroot : (X-1 : (ZMod p)[X])∣actualNRPolynomial p hp := by
    apply dvd_iff_isRoot.mpr
    exact he
  obtain ⟨Q,hQ⟩ := hroot
  have hQm : Q.eval (-1)=0 := by
    have hv := congrArg (fun P : (ZMod p)[X] => P.eval (-1)) hQ
    simp only [eval_mul,eval_sub,eval_X,eval_one,hem] at hv
    have hz : (2 : ZMod p)*Q.eval (-1)=0 := by linear_combination hv
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hrootQ : (X+1 : (ZMod p)[X])∣Q := by
    have hh : (X-C (-1 : ZMod p) : (ZMod p)[X])∣Q := dvd_iff_isRoot.mpr hQm
    simpa only [map_neg,map_one,sub_neg_eq_add] using hh
  obtain ⟨R,hR⟩ := hrootQ
  have hroot2 : (X^2-1 : (ZMod p)[X])∣actualNRPolynomial p hp := by
    refine ⟨R,?_⟩
    rw [hQ,hR]
    ring
  have hmonic : (X^2-1 : (ZMod p)[X]).Monic := by
    exact monic_X_pow_sub_C (1 : ZMod p) (by norm_num : (2 : ℕ)≠0)
  have hi : (X^2-1)*actualNRQuotient p hp=actualNRPolynomial p hp := by
    have h := modByMonic_add_div (actualNRPolynomial p hp) (X^2-1)
    rw [(modByMonic_eq_zero_iff_dvd hmonic).mpr hroot2,zero_add] at h
    exact h
  have hd : (actualNRQuotient p hp).natDegree≤p-4 := by
    unfold actualNRQuotient
    rw [natDegree_divByMonic _ hmonic]
    have htwo : (X^2-1 : (ZMod p)[X]).natDegree=2 := by
      exact natDegree_X_pow_sub_C
    rw [htwo]
    omega
  have hsame : (X^2-1 : (ZMod p)[X]).comp (-X)=X^2-1 := by
    simp only [sub_comp,pow_comp,X_comp,one_comp]
    ring
  have hcomp := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hi
  rw [mul_comp,hsame,ho] at hcomp
  have hnonzero : (X^2-1 : (ZMod p)[X])≠0 := hmonic.ne_zero
  have hodd : (actualNRQuotient p hp).comp (-X)= -actualNRQuotient p hp := by
    apply mul_left_cancel₀ hnonzero
    rw [hcomp,←hi]
    ring
  exact ⟨hi,hd,hodd⟩

/-- The exact component has a genuine full odd primitive of degree at most p-2. -/
theorem actual_NR_primitive_source_degree_odd (hp : 19≤p) :
    (1-X^2)*(actualNRPrimitive p hp).derivative= -2*X*actualNRPolynomial p hp ∧
      (actualNRPrimitive p hp).natDegree≤p-2 ∧
      (actualNRPrimitive p hp).eval 0=0 ∧
      (actualNRPrimitive p hp).comp (-X)= -actualNRPrimitive p hp := by
  obtain ⟨hQ,hdeg,hodd⟩ := actual_NR_quotient_identity_degree_odd p hp
  let W : (ZMod p)[X] := 2*X^2*actualNRQuotient p hp
  have hWdeg : W.natDegree≤p-2 := by
    have hleft : (2*X^2 : (ZMod p)[X]).natDegree≤2 := by compute_degree
    exact (natDegree_mul_le_of_le hleft hdeg).trans (by omega)
  have hW0 : W.coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [W,eval_mul,eval_ofNat,eval_pow,eval_X,zero_pow (by norm_num : (2 : ℕ)≠0),
      mul_zero,zero_mul]
  have hWodd : W.comp (-X)= -W := by
    simp only [W,mul_comp,ofNat_comp,pow_comp,X_comp,hodd]
    ring
  have hD : X*(actualNRPrimitive p hp).derivative=W :=
    eulerPrimitive_derivative p W (by omega) hW0
  have hsource : (1-X^2)*(actualNRPrimitive p hp).derivative=
      -2*X*actualNRPolynomial p hp := by
    apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X])≠0)
    rw [show X*((1-X^2)*(actualNRPrimitive p hp).derivative)=
      (1-X^2)*(X*(actualNRPrimitive p hp).derivative) by ring,hD,←hQ]
    dsimp only [W]
    ring
  have hd : (actualNRPrimitive p hp).natDegree≤p-2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [actualNRPrimitive,eulerPrimitive_coeff,coeff_eq_zero_of_natDegree_lt
      (hWdeg.trans_lt hn),zero_div]
  have hz : (actualNRPrimitive p hp).eval 0=0 := by
    rw [←coeff_zero_eq_eval_zero,actualNRPrimitive,eulerPrimitive_coeff,Nat.cast_zero,div_zero]
  have ho : (actualNRPrimitive p hp).comp (-X)= -actualNRPrimitive p hp := by
    ext n
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff n) hWodd
    rw [WPFieldAssembly.ConicKernel.coeff_comp_neg,coeff_neg] at hc
    rw [WPFieldAssembly.ConicKernel.coeff_comp_neg,coeff_neg,actualNRPrimitive,eulerPrimitive_coeff]
    linear_combination ((n : ZMod p)⁻¹)*hc
  exact ⟨hsource,hd,hz,ho⟩

end WPFieldAssembly.SourceClosureVbalIR61ExactPart
