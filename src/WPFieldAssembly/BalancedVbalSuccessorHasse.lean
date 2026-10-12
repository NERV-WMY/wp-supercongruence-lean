import WPFieldAssembly.SourceClosureVbalParity
import WPFieldAssembly.SourceClosureVbalHasseSign
import WPFieldAssembly.ActualNormCrossAttachment
import WPActualHasseReciprocal

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualRankTwoLegendreField WPActualGaussBottom
  WPFiniteWSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPActualNativeJacobiJet WPFieldAssembly.ConicKernel
  WPFieldAssembly.NativeIR28 WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.ActualNormCrossAttachment
  WPFieldAssembly.SourceClosureVbalParity
  WPFieldAssembly.SourceClosureVbalHasseSign

namespace WPFieldAssembly.BalancedVbalSuccessorHasse

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- The original conic coordinate in the native x polynomial ring. -/
noncomputable def nativeS : (ZMod p)[X] := Polynomial.C (1/5 : ZMod p)*(X+1)

/-- This is the whole original parity polynomial, before any Hasse cancellation. -/
noncomputable def actualHasseParity : (ZMod p)[X] :=
  (Polynomial.C (1/5 : ZMod p)*(4*X-11))^((p/6)%2)*
    (parityPolynomial p (p/6) (actualLegendreJacobi p)).comp
      (1-WPHasseIntegralTransport.fieldV p)

private theorem conic_comp_injective (hp : 19≤p) :
    Function.Injective (fun P : (ZMod p)[X] => P.comp conic) := by
  have hd : (conic : (ZMod p)[X]).natDegree=2 := by
    unfold conic
    compute_degree
    exact WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  exact comp_injective_nonconstant _ (by rw [hd]; norm_num)

private theorem inverse_five_polynomial (hp : 19≤p) :
    (Polynomial.C (1/5 : ZMod p) : (ZMod p)[X])*5=1 := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  change Polynomial.C (1/5 : ZMod p)*Polynomial.C 5=Polynomial.C 1
  rw [←C_mul,one_div_mul_cancel h5]

theorem native_S_conic (hp : 19≤p) :
    (nativeS p).comp conic=X^2 := by
  simp only [nativeS,mul_comp,C_comp,add_comp,X_comp,one_comp,conic]
  linear_combination X^2*(inverse_five_polynomial p hp)

theorem native_B_conic (hp : 19≤p) :
    (Polynomial.C (1/5 : ZMod p)*(4*X-11)).comp conic=4*X^2-3 := by
  simp only [mul_comp,C_comp,sub_comp,ofNat_comp,X_comp,conic]
  linear_combination (4*X^2-3)*(inverse_five_polynomial p hp)

theorem actual_Hasse_parity_conic (hp : 19≤p) :
    (actualHasseParity p).comp conic=
      (4*X^2-3)^((p/6)%2)*
        (parityPolynomial p (p/6) (actualLegendreJacobi p)).comp (Tc^2) := by
  rw [actualHasseParity,mul_comp,pow_comp,native_B_conic p hp,comp_assoc]
  simp only [sub_comp,one_comp,actual_native_V_conic p hp,sub_sub_cancel]

/-- The entire actual norm factors before selecting its reciprocal sign. -/
theorem actual_Hasse_native_norm (hp : 19≤p) :
    (actualF p).comp (WPHasseIntegralTransport.fieldV p)=
      (nativeS p)^((p/6)%2)*(actualHasseParity p)^2 := by
  apply conic_comp_injective p hp
  dsimp only
  rw [mul_comp,pow_comp,pow_comp,native_S_conic p hp,actual_Hasse_parity_conic p hp,
    comp_assoc,actual_native_V_conic p hp]
  have hf := even_native_attachment p hp _ (actual_Y_square_even p hp)
  change (actualF p).comp (1-X^2)=actualLegendreJacobi p^2 at hf
  have hY := (actual_Y_parity p hp).1
  have hYc := congrArg (fun P : (ZMod p)[X] => P.comp Tc) hY
  simp only [mul_comp,pow_comp,X_comp,comp_assoc] at hYc
  calc
    _ = ((actualF p).comp (1-X^2)).comp Tc := by
      rw [comp_assoc]
      simp only [sub_comp,one_comp,pow_comp,X_comp]
    _ = ((actualLegendreJacobi p).comp Tc)^2 := by rw [hf,pow_comp]
    _ = _ := by
      rw [hYc,show (Tc : (ZMod p)[X])=X*(4*X^2-3) by simp only [Tc]; ring,
        mul_pow,mul_pow]
      simp only [mul_pow,←pow_mul,Nat.mul_comm]
      ring

theorem actual_Hasse_parity_ends (hp : 19≤p) :
    (actualHasseParity p).eval 4=1 ∧
      (actualHasseParity p).eval (1/4)=(-2 : ZMod p)^((p/6)%2) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h8 : (8 : ZMod p)≠0 := by rw [show (8 : ZMod p)=2^3 by ring]; exact pow_ne_zero _ h2
  have hs := actual_Hasse_parity_conic p hp
  have hb := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hs
  have ha := congrArg (fun Q : (ZMod p)[X] => Q.eval (1/2)) hs
  have hx : (conic : (ZMod p)[X]).eval (1/2)=1/4 := by
    simp only [conic,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
    field_simp [h2,h4,h8]
    ring
  have ht : (Tc : (ZMod p)[X]).eval (1/2)= -1 := by
    simp only [Tc,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X]
    field_simp [h2,h4,h8]
    ring
  have hbn : (4 : ZMod p)*(1/2)^2-3= -2 := by
    field_simp [h2,h4,h8]
    ring
  have hx1 : (conic : (ZMod p)[X]).eval 1=4 := by norm_num [conic]
  have ht1 : (Tc : (ZMod p)[X]).eval 1=1 := by norm_num [Tc]
  have hY1 := (actual_Y_parity p hp).2
  constructor
  · simp only [eval_comp,eval_mul,eval_pow,eval_sub,eval_ofNat,eval_X,hx1,ht1,
      one_pow,mul_one,hY1] at hb
    norm_num [hY1] at hb
    exact hb
  · simp only [eval_comp,eval_mul,eval_pow,eval_sub,eval_ofNat,eval_X,hx,ht,hbn,
      neg_one_sq,hY1,mul_one] at ha
    exact ha

theorem actual_half_parity (hp : 19≤p) :
    2*(((p-1)/2-(p/6)%2)/2)+(p/6)%2=(p-1)/2 := by
  rcases WPActualNativeParameter.prime_six_classes p (by omega) with h1 | h5
  · have hdiv := Nat.mod_add_div (p/6) 2
    omega
  · have hdiv := Nat.mod_add_div (p/6) 2
    omega

/-- Both native ends are values of the same actual norm, with no harmonic nonvanishing premise. -/
theorem actual_Hasse_native_unit_ends (hp : 19≤p) :
    ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).eval (1/4)=1 ∧
      ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).eval 4=1 := by
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hs4 : (nativeS p).eval 4=1 := by
    simp only [nativeS,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h5]
    ring
  have hsa : (nativeS p).eval (1/4)=1/4 := by
    simp only [nativeS,eval_mul,eval_C,eval_add,eval_X,eval_one]
    field_simp [h4,h5]
    ring
  have hpow : ((-2 : ZMod p)^((p/6)%2))^2=(4 : ZMod p)^((p/6)%2) := by
    rw [←pow_mul,Nat.mul_comm ((p/6)%2) 2,pow_mul]
    congr 1
    ring
  obtain ⟨hP4,hPa⟩ := actual_Hasse_parity_ends p hp
  rw [actual_Hasse_native_norm p hp]
  simp only [eval_mul,eval_pow,hs4,hsa,hP4,hPa,one_pow,one_mul,hpow]
  constructor
  · rw [←mul_pow,one_div_mul_cancel h4,one_pow]
  · trivial

private theorem native_S_reciprocal :
    (nativeS p).toLaurent=T 1*invert (nativeS p).toLaurent := by
  simp only [nativeS,map_mul,map_add,toLaurent_C,toLaurent_X,map_one,
    invert_C,invert_T]
  have hT : (T 1 : (ZMod p)[T;T⁻¹])*T (-1)=1 := by
    rw [←T_add]
    norm_num
  linear_combination -LaurentPolynomial.C (1/5 : ZMod p)*hT

/-- Cancellation occurs only in the domain, never by inverting a Hasse root. -/
theorem actual_Hasse_parity_square_reciprocal (hp : 19≤p) :
    (actualHasseParity p).toLaurent^2=
      (T ((((p-1)/2-(p/6)%2)/2 : ℕ) : ℤ)*invert (actualHasseParity p).toLaurent)^2 := by
  let r := (p/6)%2
  let M := ((p-1)/2-r)/2
  let s := (nativeS p).toLaurent
  let P := (actualHasseParity p).toLaurent
  have hM : 2*M+r=(p-1)/2 := actual_half_parity p hp
  have hs0 : s≠0 := by
    have hv : (nativeS p).eval 4=1 := by
      simp only [nativeS,eval_mul,eval_C,eval_add,eval_X,eval_one]
      have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
      field_simp [h5]
      ring
    intro hz
    have hzP : nativeS p=0 := by
      apply Polynomial.toLaurent_injective
      simpa only [map_zero] using hz
    rw [hzP,eval_zero] at hv
    exact zero_ne_one hv
  have hf : (s^r*P^2)=T (((p-1)/2 : ℕ) : ℤ)*invert (s^r*P^2) := by
    have hr := WPActualHasseReciprocal.actual_native_Hasse_Laurent p (by omega)
    simp only [←actualF_eq_native p hp] at hr
    have hn := congrArg Polynomial.toLaurent (actual_Hasse_native_norm p hp)
    simp only [map_mul,map_pow] at hn
    change ((actualF p).comp (WPHasseIntegralTransport.fieldV p)).toLaurent=s^r*P^2 at hn
    simpa only [hn] using hr
  have hshift : (T (((p-1)/2 : ℕ) : ℤ) : (ZMod p)[T;T⁻¹])=
      T (M : ℤ)^2*T 1^r := by
    rw [T_pow,T_pow,←T_add]
    congr 1
    omega
  apply mul_left_cancel₀ (pow_ne_zero r hs0)
  change s^r*P^2=s^r*(T (M : ℤ)*invert P)^2
  calc
    _ = T (((p-1)/2 : ℕ) : ℤ)*invert (s^r*P^2) := hf
    _ = (T 1*invert s)^r*(T (M : ℤ)*invert P)^2 := by
      rw [hshift,map_mul,map_pow,map_pow,mul_pow,mul_pow]
      ring
    _ = _ := by rw [←native_S_reciprocal p]

private theorem inversion_eval {K : Type*} [Field K]
    (u : Kˣ) (L : K[T;T⁻¹]) :
    LaurentPolynomial.eval₂ (RingHom.id K) u (invert L)=
      LaurentPolynomial.eval₂ (RingHom.id K) u⁻¹ L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add,hL,hM]
  | C_mul_T n a =>
    simp only [map_mul,invert_C,invert_T,LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T,RingHom.id_apply,zpow_neg,inv_zpow]

/-- The original endpoint selects the SAME entire reciprocal, including every Hasse zero. -/
theorem actual_Hasse_parity_reciprocal (hp : 19≤p) :
    (actualHasseParity p).toLaurent=
      LaurentPolynomial.C (SourceClosureVbalIR61FourEnds.actualCrossHasseSign p)*
        T ((((p-1)/2-(p/6)%2)/2 : ℕ) : ℤ)*
          invert (actualHasseParity p).toLaurent := by
  let M := ((p-1)/2-(p/6)%2)/2
  let P := (actualHasseParity p).toLaurent
  let eta := SourceClosureVbalIR61FourEnds.actualCrossHasseSign p
  let Q := LaurentPolynomial.C eta*T (M : ℤ)*invert P
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  let ψ : (ZMod p)[T;T⁻¹]→+*ZMod p :=
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (Units.mk0 4 h4)
  have hP : ψ P=1 := by
    simpa only [ψ,P,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,
      Units.val_mk0] using (actual_Hasse_parity_ends p hp).1
  have hQ : ψ Q=1 := by
    have he := actual_cross_hasse_unit_scale p hp M (actual_half_parity p hp)
    have ha := (actual_Hasse_parity_ends p hp).2
    change LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (Units.mk0 4 h4)
      (LaurentPolynomial.C eta*T (M : ℤ)*invert P)=1
    simp only [map_mul,LaurentPolynomial.eval₂_C,RingHom.id_apply,
      LaurentPolynomial.eval₂_T,inversion_eval,P,LaurentPolynomial.eval₂_toLaurent,
      Polynomial.eval₂_id,Units.val_inv_eq_inv_val,Units.val_mk0,zpow_natCast,
      Units.val_pow_eq_pow_val]
    rw [←one_div (4 : ZMod p),ha]
    exact he
  have hs : P^2=Q^2 := by
    have h := actual_Hasse_parity_square_reciprocal p hp
    change P^2=(T (M : ℤ)*invert P)^2 at h
    calc
      _ = (T (M : ℤ)*invert P)^2 := h
      _ = _ := by
        dsimp only [Q]
        have heta : eta^2=1 := actual_cross_hasse_sign_square p hp
        have hetaC : (LaurentPolynomial.C eta : (ZMod p)[T;T⁻¹])^2=1 := by
          rw [←map_pow,heta,map_one]
        simp only [mul_pow,hetaC,one_mul]
  exact whole_square_sign_selected h2 ψ P Q hs hP hQ

end WPFieldAssembly.BalancedVbalSuccessorHasse
